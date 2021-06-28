(ns elle.set-add
  "In this workload, our fundamental datatype is a set of elements, and our
  writes add a unique element to that set."
  (:require [clojure [pprint :refer [pprint]]
                     [set :as set]]
            [elle [explanation :as expl]
                  [graph :as g]
                  [recovery :as rec]
                  [txn :as et]
                  [txn-graph :as tg]
                  [util :as util :refer [map-vals]]
                  [version-graph :as vg]]
            [elle.infer [cyclic :as cyclic]]
            [jepsen.txn :as jt]
            [knossos.op :as op])
  (:import (io.lacuna.bifurcan IntSet)))

(set! *warn-on-reflection* true)

; When deriving a subset graph, we're going to do a bunch of subset
; comparisons, hashing, and equality checking. To speed this up, we map raw
; Clojure sets into compact, optimized data structures which support fast
; subset testing, and can be turned back to their original sets when required.

(definterface FastSet
  (^boolean isSubset [potential-superset])
  (toSet []))

(defn fast-set-subset?
  "Is FastSet a a subset of b?"
  [^FastSet a ^FastSet b]
  (.isSubset a b))

(defn fast-set->set
  "Converts a FastSet back to a Clojure set."
  [^FastSet s]
  (.toSet s))

; This fast set is backed by a Bifurcan IntSet, which offers compact subset
; testing. We build a collection of these sets all at once, and assign each a
; unique ID, which is used as its hashcode. Equality testing is done by
; reference, because we create exactly one object for each value. WARNING:
; Absolutely not safe to construct and compare these outside this particular
; context, oh my god, be careful.
(deftype AIntSet [^int id cljset ^IntSet intset]
  Object
  (hashCode [this] id)

  (equals [this other] (identical? this other))

  clojure.lang.Counted
  (count [this]
    (count cljset))

  FastSet
  (isSubset [this other]
    (= 0 (.size (.difference intset ^IntSet (.intset ^AIntSet other)))))

  (toSet [this] cljset))

(defn as-intsets
  "Takes a collection of sets of arbitrary elements, and maps those sets into
  isomorphic FastSet IntSets which have equivalent cardinality and subset
  relations.

  This is important because we can burn a *lot* of time in subset equality
  checking, which is hugely expensive to do over standard Clojure
  collections--but can be efficiently performed over the in-memory layout of an
  IntSet."
  [sets]
  (let [; Later on, it'll be handy for us to have a stable order of these sets,
        ; so we can return them directly instead of reconstructing them from raw
        ; elements.
        sets (vec sets)
        ; We need a mapping of elements to (hopefully dense) integer
        ; indices.
        elements (reduce set/union sets)
        ; What should the encoding order be? I'm honestly not sure. One
        ; argument would be to maximize entropy by choosing early bits with
        ; roughly 50% probability of appearing, but I think that the intset
        ; representation can actually be more compact if we sort the elements
        ; in ascending order, the way they were likely added to the set? This
        ; packing is probably denser, but it also means differences are
        ; probably at the end of the intset, so maybe it takes longer to check?
        ; Might be worth revisiting this later.
        element-order  (vec (sort elements))
        ; This gives us a mapping from indexes to elements. Now we need the
        ; inverse index:
        element->index (->> element-order
                            (map-indexed (fn [i e] [e i]))
                            (into {}))
        ; Right, now map each element into an IntSet
        intsets (map-indexed (fn intset [id s]
                               (AIntSet. id s
                                        (g/forked
                                          (reduce (fn [^IntSet is e]
                                                    (.add is (element->index e)))
                                                  (g/linear (IntSet.))
                                                  s))))
                             sets)]
    intsets))

(defn all-versions
  "Returns a map of keys to the set of all versions we know existed for that
  key, in a given history. We always infer the empty set, even if not observed."
  [history]
  (->> history
       (filter op/ok?)
       jt/op-mops
       (reduce (fn version-finder [kvs [_ [f k v]]]
                 (when (= :r f)
                   (let [vs (get kvs k #{#{}})]
                     (assoc kvs k (conj vs v)))))
               {})))

(def ^:dynamic *calls*
  "Perf testing helper, delete me later"
  (atom 0))

(defn subsets-of-version
  "A helper function for build-version-graph-for-key. Takes a collection of
  tiers, a map of versions to covered tiers, a tier number w-tier-i, and a
  version in that tier w. Returns [subsets], where `subsets` is a set of all
  versions which are subsets (not including transitive dependencies) of that
  version, and covered-tier is the tier for which every v in that tier (and
  below) is a subset of w."
  [tiers covered w-tier-i w]
  ;(prn :looking-for-subsets-of w :from w-tier-i :down)
  ; Iterate over tiers downwards, calling each tier index we examine v-tier-i.
  (let [[subsets covered-tier]
        (reduce (fn tier [[subsets covered-tier] v-tier-i]
                  (if (<= v-tier-i covered-tier)
                    ; We've encountered a version which covers this tier; we
                    ; can skip any further tiers.
                    (reduced [subsets covered-tier])
                    (let [;_ (prn :v-tier v-tier-i (nth tiers v-tier-i))
                      ; For each version v in v-tier, check to see if it might
                      ; be a subset of w, and figure out whether *every* v in
                      ; this tier is a subset of w--allowing us to cover this
                      ; tier.
                      [subsets covered-tier this-tier-covered?]
                      (reduce (fn [[subsets covered-tier this-tier-covered?] v]
                                (swap! *calls* inc)
                                (if (fast-set-subset? v w)
                                  ; It's a match! This might let us cover more
                                  ; tiers too.
                                  [(conj subsets v)
                                   (max covered-tier (get covered v -1))
                                   this-tier-covered?]
                                  ; Nope, not a match
                                  [subsets covered-tier false]))
                              [subsets covered-tier true]
                              (nth tiers v-tier-i))]
                      ; OK, we've finished checking this tier. We might have a
                      ; new covered tier because of one of the versions in this
                      ; tier, and if we're really lucky, EVERYTHING in this
                      ; tier was a subset, and this tier is therefore covered
                      ; too.
                      [subsets
                       (if (and this-tier-covered?
                                (= (dec v-tier-i) covered-tier))
                         ; Good, we can actually cover this tier. TODO: there's
                         ; an edge case here where you could have multiple
                         ; consecutive tiers such that nothing in the higher
                         ; tier covers the lower tier, but ALL of them are
                         ; subsets of w; we'd incorrectly infer a covered tier
                         ; that was conservatively low in that case.
                         v-tier-i
                         ; Ah well, at least we have the lower bounds.
                         covered-tier)])))
                [#{} -1] ; subsets, covered tier
                ; Start at the previous tier and work down to zero.
                (range (dec w-tier-i) -1 -1))]
    [subsets covered-tier]))

(defn version-graph-for-key
  "Takes a collection of versions for a single key, and returns a Bifurcan
  directed graph g over those versions where a->b implies a is a proper subset
  of b, *and* g is its own transitive reduction: if a is a subset of b and b is
  a subset of c, a->b, b->c, but NOT a -> c.

  The bad way to compute this is to compare all n versions to all n-1 other
  versions, which is obviously O(n^2).

  Instead, we do something a little clever. First, a can only be a subset of b
  if a has smaller cardinality than b. So we group the versions into *tiers* of
  increasing size, such that tier 0 is the empty set, tier 1 is singleton sets,
  tier 2 are two-element sets, and so on. When evaluating a version from tier
  n, we need only compare it to versions from smaller tiers.

  The second trick we use is to assume that elements show up in bigger sets
  *eventually*. For version v, there should be some tier below which *every*
  version is a subset of v. We keep track of a map of these 'covered tiers' for
  each version.

  When we're searching for potential subsets, we work our way backwards through
  tiers, keeping track of the *highest* tier we know to be covered, and
  stopping once we hit it."
  [versions]
  (let [; Make sure we have an initial version #{}
        versions (-> versions
                     set
                     (conj #{}))
        fs-versions (as-intsets versions)
        tiers (->> fs-versions
                   (group-by count)
                   (sort-by key)
                   (mapv val))
        ;_ (prn :tiers tiers)
        [graph] ; For each tier...
        (reduce (fn tier [[graph covered w-tier-i] w-tier]
                  ;(prn)
                  ;(prn :graph graph)
                  ;(prn :covered (with-out-str (pprint covered)))
                  ;(prn :w-tier w-tier-i w-tier)
                  ; And for some version w in that tier
                  (let [[graph' covered']
                        (reduce (fn w [[graph covered] w]
                                  ;(prn :w w)
                                  ; Examine each previous tier looking for
                                  ; subsets
                                  (let [[subsets covered-tier]
                                        (subsets-of-version
                                          tiers covered w-tier-i w)]
                                    ;(prn :subsets subsets)
                                    ; Now, add those subsets to the graph
                                    ; OK, so this is surprisingly slow: the
                                    ; hash computation for sets is apparently
                                    ; super expensive.
                                    [(g/link-all-to graph subsets w)
                                     ; And make note of what tiers this version
                                     ; covers.
                                     (assoc covered w covered-tier)]))
                                [graph covered]
                                w-tier)]
                    ; Move to the next tier with our new graph and covered map.
                    [graph' covered' (inc w-tier-i)]))
                [(g/linear (g/digraph))
                 ;(transient {})
                 {}
                 0]
                tiers)]
    ; Map from intsets back to original sets
    (->> graph
         (g/map-vertices fast-set->set)
         g/forked)))

(defn build-version-graph
  "Takes an all-versions map, and computes a map of keys to Bifurcan graphs
  over those versions. For set addition, we use subset inclusion to determine
  dependencies."
  [all-versions]
  (map-vals version-graph-for-key all-versions))

(defn version-graph
  "Returns a VersionGraph for this history."
  [history]
  (let [all-versions (all-versions history)
        g (build-version-graph all-versions)]
    (reify vg/VersionGraph
      (all-keys [this]
        (et/all-keys history))

      (graph [this k]
        (get g k))

      (explain-version-pair [this k v v']
        (reify expl/Explanation
          (->data [_] [:subset v v'])
          (->text [_ ctx] (str (pr-str v) "is a subset of" (pr-str v'))))))))

(defn add-version-graph
  "Adds a version graph to an analysis."
  [analysis]
  (assoc analysis :version-graph (version-graph (:history analysis))))

(defrecord WriteRecovery [elements->versions versions->writes]
  rec/WriteRecovery
  (write->version [_ [f k v]]
    (get-in elements->versions [k v]))

  (explain-write->version [_ [f k v] version]
    expl/trivial)

  (version->write [_ k version]
    (get-in versions->writes [k version]))

  (explain-version->write [_ k version [op mop]]
    expl/trivial))

(defn write-recovery
  "Returns a WriteRecovery object mapping between versions and writes.

  In order to identify a write of element e as generating a particular version,
  we need two distinct versions to exist: one with e, and one with all of those
  elements *except* e. We sort all versions by size, and look at successive
  pairs to identify which element(s) were added.

  A more flexible, but less precise, inference would be to pick the *smallest*
  version including e, but I don't exactly know what that would do to Elle's
  anomaly detection. Obviously it would find serializability violations, but we
  might miscategorize dependencies."
  [history]
  (let [elements->versions
        (->> (all-versions history)
             (map-vals (fn [versions-of-key]
                         ; For each set of versions, we want a series
                         ; of pairs like [vs vs'], where vs are of
                         ; size n, and vs' are of size n+1. That way
                         ; we can incrementally compare them.
                         (let [tier-pairs (->> versions-of-key
                                               (group-by count)
                                               (sort-by key)
                                               (map val)
                                               (partition 2 1))]
                           ; Now, for each of those pairs, look for
                           ; single-element differences between them, and
                           ; produce an [element resulting-version] pair
                           (->> (for [[vs vs']       tier-pairs
                                      v              vs
                                      v'             vs']
                                  (let [diff (set/difference v' v)]
                                    (when (= 1 (count diff))
                                      ; Aha! We found the version resulting
                                      ; from the write of e!
                                      (let [e (first diff)]
                                        [e v']))))
                                ; Turn those into a map of elements to versions
                                (remove nil?)
                                (into {}))))))
        versions->elements (map-vals set/map-invert elements->versions)
        elements->writes   (et/args->writes #{:add} history)
        versions->writes   (util/keyed-map-compose versions->elements
                                                   elements->writes)]
    (->WriteRecovery elements->versions versions->writes)))

(defn explain-indirect-wr
  "Explains an indirect relationship where T1 writes something visible to T2."
  [t1 t2]
  ; TODO: this is gonna break when we find relationships on internal
  ; reads/writes--those shouldn't be generated, but we do right now. Fix this
  ; in indirect-txn-graph.
  (let [writes (jt/ext-writes (:value t1))
        reads  (jt/ext-reads (:value t2))]
    (reduce (fn [_ [k v]]
              (when-let [e (get writes k)]
                (when (contains? v (get writes k))
                  (reduced
                    (reify expl/Explanation
                      (->data [_] {:type        :indirect-wr
                                   :write       [:add k e]
                                   :read        [:r k v]})
                      (->text [_ ctx]
                        (str "added " e " to " k
                             ", which was visible in a read of " v)))))))
            nil
            reads)))

(defn explain-indirect-rw
  "Explains an indirect relationship where T1 read a state prior to T2's write."
  [t1 t2]
  ; TODO: this is gonna break when we find relationships on internal
  ; reads/writes--those shouldn't be generated, but we do right now. Fix this
  ; in indirect-txn-graph.
  (let [reads  (jt/ext-reads  (:value t1))
        writes (jt/ext-writes (:value t2))]
    (reduce (fn [_ [k v]]
              (when-let [e (get writes k)]
                (when-not (contains? v (get writes k))
                  (reduced
                    (reify expl/Explanation
                      (->data [_] {:type        :indirect-rw
                                   :write       [:add k e]
                                   :read        [:r k v]})
                      (->text [_ ctx]
                        (str "added " e " to " k
                             ", which was not present in a read of " v)))))))
            nil
            reads)))

(defrecord IndirectTxnGraph [graph txn-graph]
  tg/TxnGraph
  (graph [this]
    ; Just return the merged graph
    (:graph this))

  (explain [_ t1 t2]
    ; Try to let the direct txn graph explain it, and if not, we'll try.
    (or (tg/explain txn-graph t1 t2)
        ; Do we have an edge in the expanded graph?
        (when-let [edge (g/maybe-edge graph t1 t2)]
          ; OK, cool, what kind?
          (cond
            (edge :wr) (explain-indirect-wr t1 t2)
            (edge :rw) (explain-indirect-rw t1 t2)
            true       (throw (RuntimeException.
                                (str "Don't know how to explain edge of type "
                                     (pr-str edge)))))))))

(defn indirect-txn-graph
  "We can use the usual recovery+version graph to infer relationships between
  transactions, but there are some legal inferences we *can't* draw this way.
  For instance, consider a history with three transactions: ax1, ax2, rx12. We
  know that both ax1 and ax2 had to precede rx12, but we can't actually SHOW
  that via recoverability: ax1 and ax2 are non-recoverable, and because we
  don't know what versions EXIST, we don't have version graph vertices for #{1}
  or #{2}. We could try to generate them via the power set of all unrecoverable
  vertices, but down that path lies madness.

  Instead, we take advantage of a nifty trick: if the version graph is a total
  order for each key, then each read version effectively *partitions* the set
  of writes into those which could have come before, and those which could have
  come after, that read. So long as the jumps between versions aren't huge
  (e.g. #{1 2 3} -> #{1 2 3 4 5} leaves only two elements unfixed), we can
  derive rw edges from any read of #{1 2 3} to the writes ax4 and ax5, and wr
  edges from ax4 and ax5 to any read of #{1 2 3 4 5}. Our normal recovery graph
  is simply the limiting case of this algorithm--when the jump between versions
  is exactly one element.

  Our approach here is to fill in the gaps: we check to make sure the version
  graph is totally ordered, and if it is, we run through each successful read
  in the history. For that read, we take the next smaller and next larger
  versions in the version graph, and compute the differences between the
  smaller (larger) and the present read: this gives us the writes which must
  have occurred just before (after) this read. We look find the transactions
  which wrote those values, and link them using wr (rw) edges.

  These aren't necessarily the TRUE wr and rw edges, but there should exist a
  path which is comprised of any number of ww edges *plus* that wr (rw) edge;
  this inference can't cause us to infer more dangerous anomalies.

  Takes an analysis with a version and transaction graph, and returns the
  TransactionGraph augmented with indirect edges, or nil if we can't infer any
  indirect edges."
  [analysis]
  (when (let [vg (:version-graph analysis)]
          (->> (vg/all-keys vg)
                (map (partial vg/graph vg))
                (every? g/total-order?)))
    (let [vg            (:version-graph analysis)
          tg            (:txn-graph analysis)
          rec           (:recovery analysis)
          history       (:history analysis)
          args->writes  (et/args->writes #{:add} history)
          ; A function which returns true if a write [op2 mop2] is recoverable
          ; OR is the current operation op.
          ignored-write? (fn [op [op2 mop2]]
                           (or (rec/write->version rec mop2)
                               (= op op2)))
          tgg'
          (->> history
               (filter op/ok?)
               ; TODO: instead of reduce-mops (which gives us every mop) we
               ; should take just external reads.
               (jt/reduce-mops
                 (fn [g op [f k v :as mop]]
                   (if (= :r f)
                     (let [; Link previous writes to current read.
                           g'
                           (as-> v %
                             ; Find the previous version
                             (first (g/in (vg/graph vg k) %))
                             ; Compute the delta with the current version
                             (set/difference v %)
                             ; Map those elements back to [op mop] pairs
                             (map (get args->writes k) %)
                             ; Remove unrecoverable writes, and this op to
                             ; prevent self-edges:
                             (remove (partial ignored-write? op) %)
                             ; And taking just the ops from those pairs
                             (map first %)
                             ; And creating links in the graph.
                             (g/link-all-to g % op :wr))

                           ; Almost symmetrically, link following writes to the
                           ; current read.
                           g'
                           (as-> v %
                             (first (g/out (vg/graph vg k) %))
                             (set/difference % v)
                             (map (get args->writes k) %)
                             (remove (partial ignored-write? op) %)
                             (map first %)
                             (g/link-to-all g' op % :rw))]
                       g')
                     ; Not a read
                     g))
                 (tg/graph tg)))]
          (IndirectTxnGraph. tgg' tg))))

(defn add-indirect-txn-graph
  "Takes an analysis, and augments its txn-graph as per indirect-txn-graph."
  [analysis]
  (when-let [tg (indirect-txn-graph analysis)]
    (assoc analysis :txn-graph tg)))

(defn add-recovery
  "Adds a recovery to an analysis."
  [analysis]
  (assoc analysis :recovery (write-recovery (:history analysis))))

(defn preprocess
  "Removes the nemesis from an analysis' history, checks for type sanity, etc."
  [analysis]
  (let [history (:history analysis)
        history (vec (remove (comp #{:nemesis} :process) history))
        _       (et/assert-type-sanity history)]
    (assoc analysis :history history)))

(defn check
  "Full checker for sets with addition. Options are:

    :consistency-models     A collection of consistency models we expect this
                            history to obey. Defaults to [:strict-serializable].
                            See elle.consistency-model for available models.

    :anomalies              You can also specify a collection of specific
                            anomalies you'd like to look for. Performs limited
                            expansion as per
                            elle.consistency-model/implied-anomalies.

    :additional-graphs      A collection of graph analyzers (e.g. realtime)
                            which should be merged with our own dependency
                            graph.

    :directory              Where to output files, if desired. (default nil)

    :plot-format            Either :png or :svg (default :svg)"
  [opts history]
  (-> {:options opts
       :history history}
      preprocess
      add-recovery
      add-version-graph
      tg/add-txn-graph
      add-indirect-txn-graph
      cyclic/add-anomalies))
