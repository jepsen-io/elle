(ns elle.set-add
  "In this workload, our fundamental datatype is a set of elements, and our
  writes add a unique element to that set."
  (:require [clojure [pprint :refer [pprint]]
                     [set :as set]]
            [elle [explanation :as expl]
                  [graph :as g]
                  [recovery :as recovery]
                  [txn :as et]
                  [util :as util :refer [map-vals]]
                  [version-graph :as vg]]
            [jepsen.txn :as jt]
            [knossos.op :as op])
  (:import (io.lacuna.bifurcan IntSet)))

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
        ; in ascending order, the way they were likely added to the set?
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
  key, in a given history."
  [history]
  (->> history
       (filter op/ok?)
       jt/op-mops
       (reduce (fn [kvs [_ [f k v]]]
                 (when (= :r f)
                   (let [vs (get kvs k #{})]
                     (assoc kvs k (conj vs v))))))))

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
          (->text [_] (str (pr-str v) "is a subset of" (pr-str v'))))))))

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
  (let [versions (->> (all-versions history)
                      (map-vals (fn [versions-of-key]
                                  ; For each set of versions, we want a series
                                  ; of pairs like [vs vs'], where vs are of
                                  ; size n, and vs' are of size n+1. That way
                                  ; we can incrementally compare them.
                                  (group-by count)
                                  (sort-by key)
                                  (map val)
                                  (partition 2 1))))
        ; Now, for each key, take every combination of versions which differ in
        ; size by 1, and look for a single-element difference between them.
        elements->versions
        (->> (for [[k [vs vs']] versions
                   v  vs
                   v' vs']
               (let [diff (set/difference v' v)]
                 (when (= 1 (count diff))
                   ; Aha! We found the version resulting from the write of e!
                   (let [e (first diff)]
                     [e v']))))
             (remove nil?)
             (into {}))
        versions->elements (set/map-invert elements->versions)
        elements->writes   (et/args->writes history)
        versions->writes   (util/keyed-map-compose versions->elements
                                                   elements->writes)]

    (reify recovery/WriteRecovery
      (write->version [_ [f k v]]
        (get-in elements->versions [k v]))

      (explain-write->version [_ [f k v] version]
        expl/trivial)

      (version->write [_ k version]
        (get-in versions->writes [k version]))

      (explain-version->write [_ k version [op mop]]
        expl/trivial))))
