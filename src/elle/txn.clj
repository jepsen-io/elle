(ns elle.txn
  "Functions for cycle analysis over transactional workloads."
  (:require [bifurcan-clj [core :as b]
                          [graph :as bg]
                          [set :as bs]]
            [clojure [datafy :refer [datafy]]
                     [pprint :refer [pprint]]
                     [set :as set]]
            [clojure.tools.logging :refer [info warn]]
            [clojure.java.io :as io]
            [dom-top.core :refer [loopr]]
            [elle [bfs :as bfs]
                  [core :as elle]
                  [consistency-model :as cm]
                  [graph :as g]
                  [rels :as rels :refer [ww wr rw wwp wrp rwp process realtime]]
                  [util :as util]
                  [viz :as viz]]
            [jepsen [history :as h]
                    [txn :as txn :refer [reduce-mops]]]
            [jepsen.history.fold :refer [loopf]]
            [tesser.core :as t]
            [unilog.config :refer [start-logging!]])
  (:import (elle BitRels)
           (io.lacuna.bifurcan IGraph
                               LinearMap
                               Map)
           (jepsen.history Op)))

(start-logging! {:console "%p [%d] %t - %c %m%n"})

(defn op-mops
  "A lazy sequence of all [op mop] pairs from a history."
  [history]
  (mapcat (fn [op] (map (fn [mop] [op mop]) (:value op))) history))

(t/deftransform keep-op-mops
  "A tesser fold over a history. For every op, and every mop in that op, calls
  `(f op mop])`. Passes non-nil results to downstream transforms."
  [f]
  (assoc downstream :reducer
         (fn reducer [acc ^Op op]
           (reduce (fn mop [acc mop]
                     (let [res (f op mop)]
                       (if (nil? res)
                         acc
                         (reducer- acc res))))
                   acc
                   (.value op)))))

(defn ok-keep
  "Given a function of operations, returns a sequence of that function applied
  to all ok operations. Returns nil iff every invocation of f is nil. Uses a
  concurrent fold internally."
  [f history]
  (->> (t/filter h/ok?)
       (t/keep f)
       (t/into [])
       (h/tesser history)
       seq))

(defn all-keys
  "A sequence of all unique keys in the given history."
  [history]
  (->> history op-mops (map (comp second second)) distinct))

(def integer-types
  #{Byte Short Integer Long})

(defn assert-type-sanity
  "I cannot begin to convey the confluence of despair and laughter which I
  encountered over the course of three hours attempting to debug this issue.

  We assert that all keys have the same type, and that at most one integer type
  exists. If you put a mix of, say, Ints and Longs into this checker, you WILL
  question your fundamental beliefs about computers"
  [history]
  (let [int-val-types (->> (op-mops history)
                           (map (comp class last second))
                           (filter integer-types)
                           distinct)]
    (assert (<= (count int-val-types) 1)
            (str "History includes a mix of integer types for transaction values: " (pr-str int-val-types) ". You almost certainly don't want to do this.")))
  (let [key-types (->> (op-mops history)
                       (map (comp class second second))
                       distinct)]
    (assert (<= (count key-types) 1)
            (str "History includes a mix of different types for transaction keys: " (pr-str key-types) ". You almost certainly don't want to do this."))))

(defn failed-writes
  "Returns a map of keys to maps of failed write values to the operations which
  wrote them. Used for detecting aborted reads."
  [write? history]
  (h/fold history
          (loopf {:name :failed-writes}
                 ([failed {}]
                  [^Op op]
                  (recur
                    (if (h/fail? op)
                      (loopr [failed' failed]
                             [[f k v :as mop] (.value op)]
                             (if (write? f)
                               (recur (update failed' k assoc v op))
                               (recur failed')))
                      failed)))
                 ([failed {}]
                  [failed']
                  (recur (merge-with merge failed failed'))))))

(defn failed-write-indices
  "Returns a map of keys to maps of failed write values to the :index's of the
  operations which wrote them. Used for detecting aborted reads. This version
  is significantly more memory-efficient, since it does not require retaining
  every failed operation for the entire pass."
  [write? history]
  (h/fold history
          (loopf {:name :failed-writes}
                 ([failed {}]
                  [^Op op]
                  (recur
                    (if (h/fail? op)
                      (loopr [failed' failed]
                             [[f k v :as mop] (.value op)]
                             (if (write? f)
                               (recur (update failed' k assoc v (.index op)))
                               (recur failed')))
                      failed)))
                 ([failed {}]
                  [failed']
                  (recur (merge-with merge failed failed'))))))

(defn intermediate-writes
  "Returns a map of keys to maps of intermediate write values to the operations
  which wrote them. Used for detecting intermediate reads."
  [write? history]
  (h/fold history
          (loopf {:name :intermediate-writes}
                 ([im {}]
                  [^Op op]
                  ; Find intermediate writes for this particular txn by
                  ; producing two maps: intermediate keys to values, and
                  ; final keys to values in this txn. We shift elements
                  ; from final to intermediate when they're overwritten.
                  (recur (loopr [im'   im
                                 final {}]
                                [[f k v] (.value op)]
                                (if (write? f)
                                  (if-let [e (final k)]
                                    ; We have a previous write of k
                                    (recur (assoc-in im' [k e] op)
                                           (assoc final k v))
                                    ; No previous write
                                    (recur im' (assoc final k v)))
                                  ; Something other than an append
                                  (recur im' final))
                                im')))
                 ([im {}]
                  [im']
                  (recur (merge-with merge im im'))))))

(defn intermediate-write-indices
  "Returns a map of keys to maps of intermediate write values to the :index's
  of operations which wrote them. Used for detecting intermediate reads."
  [write? history]
  (h/fold history
          (loopf {:name :intermediate-writes}
                 ([im {}]
                  [^Op op]
                  ; Find intermediate writes for this particular txn by
                  ; producing two maps: intermediate keys to values, and
                  ; final keys to values in this txn. We shift elements
                  ; from final to intermediate when they're overwritten.
                  (recur (loopr [im'   im
                                 final {}]
                                [[f k v] (.value op)]
                                (if (write? f)
                                  (if-let [e (final k)]
                                    ; We have a previous write of k
                                    (recur (assoc-in im' [k e] (.index op))
                                           (assoc final k v))
                                    ; No previous write
                                    (recur im' (assoc final k v)))
                                  ; Something other than an append
                                  (recur im' final))
                                im')))
                 ([im {}]
                  [im']
                  (recur (merge-with merge im im'))))))

(defn lost-update-cases
  "Takes a function write? which returns true iff an operation is a write, and
  a history. Returns a seq of error maps describing any lost updates found.
  Assumes writes are unique. Each map is of the form:

    {:key   The key in common
     :value The value read by all transactions
     :txns  A collection of completion ops for transactions which collided on
            this key and value.}

  Lost Update is a bit of a weird beast. I don't actually *have* a general
  definition of it: even in Adya, it's defined as 'Histories which look like
  H_lu', where H_lu is:

    w0(x0)
           r1(x0, 10)                          w1(x1, 14) c1
                      r2(x0, 10) w2(x2, 15) c2

    [x0 << x2 << x1]

  It stands to reason that the version order x2 << x1 and the precise order of
  T1 and T2 isn't necessary here: the essential problem is that T1 and T2 both
  read x0 and wrote different values of x, presumably based on x0. If this ever
  happens it could lead to the loss of the logical update T1 or T2 is
  performing.

  In cyclic terms, this must manifest as write-read edges from some transaction
  T0 to both T1 and T2 on the same key, (since both must read T0's write of x).

    +--wr--> T1
    |
    T0
    |
    +--wr--> T2

  WLOG, let x1 << x2. If we have the complete version order for x, we must also
  have a write-write edge from T1 -> T2 since both wrote x. However, since T2
  observed the state x0 which was overwritten by T1, we also have an rw edge
  from T2->T1. This forms a G2-item cycle:

    +--wr--> T1 <-+
    |        |    |
    T0       ww   rw
    |        V    |
    +--wr--> T2 --+

  We can already detect G2-item. However, we may not detect some instances of
  lost update because we may be missing some of these edges. Our version order
  inference is conservative, and especially for rw-registers may fail to
  capture many edges between versions. Even for list-append, if one of the
  writes is never read that version won't show up in the version order at all.

  What actually *matters* here is that two transactions read the same x0 and
  both wrote x, and committed. The precise order of writes to x doesn't matter.
  We can detect this directly, in linear time and space, by scanning the set of
  committed transactions and looking for any pair which both read some x=x0 and
  write x."
  [write? history]
  (loopr [; A map of keys to values to txns which read that key and value and
          ; wrote that key.
          txns (transient {})]
         [op history]
         (recur
           (if (not= :ok (:type op))
             txns
             (loopr [; A map of keys to the first value read
                     reads  (transient {})
                     ; And a set of keys we've written, so we don't
                     ; double-count
                     writes (transient #{})
                     txns   txns]
                    [[f k v] (:value op)]
                    (let [read-value (get reads k ::not-found)]
                      (if (and (write? f) (not (contains? writes k)))
                        ; We wrote k for the first time
                        (if (= read-value ::not-found)
                          ; Didn't read k; don't care
                          (recur reads writes txns)
                          ; We read and wrote k; this is relevant to our search
                          (let [txns-k    (get txns k (transient {}))
                                txns-k-v  (get txns-k read-value (transient []))
                                txns-k-v' (conj! txns-k-v op)
                                txns-k'   (assoc! txns-k read-value txns-k-v')]
                            (recur reads
                                   (conj! writes k)
                                   (assoc! txns k txns-k'))))
                        ; We read k
                        (if (= read-value ::not-found)
                          ; And this is our first (i.e. external) read of k
                          (recur (assoc! reads k v) writes txns)
                          ; We already read k
                          (recur reads writes txns))))
                    ; Return txns and move to next op
                    txns)))
         ; Now search for collisions
         (loopr [cases (transient [])]
                [[k v->txns]  (persistent! txns)
                 [v txns]     (persistent! v->txns)]
                (let [txns (persistent! txns)]
                  (recur
                    (if (<= 2 (count txns))
                      (conj! cases {:key   k
                                    :value v
                                    :txns  txns})
                      cases)))
                (let [cases (persistent! cases)]
                  (when (seq cases) cases)))))

;; Cycle existence

(def cycle-exists-specs
  "A series of specifications for consistency models and subgraphs which must be
  acyclic if that level holds. Each of these has a corresponding anomaly type,
  like :read-uncommitted-cycle-exists, in consistency-models.

  Note that these use canonical consistency model names!"
  (->> [; Read uncommitted requires no write cycles--including predicates! See
        ; Adya, page 47
        {:model :PL-1, :subgraph [:union ww wwp]}
        ; Read committed requires no circular information flow
        {:model :PL-2, :subgraph [:union ww wwp wr wrp]}

        ; Prefix can have a WW followed by an RW edge
        ; This is work we can't cite just yet--uncomment it later.
        ; {:model :prefix, :subgraph [:union ww wr [:composition wr rw]]}

        ; Snapshot isolation extends through a single RW hop, and covers
        ; prefixes
        {:model :PL-SI, :subgraph [:extension
                                   [:union ww wwp wr wrp]
                                   [:union rw rwp]]}

        ; Repeatable read means no cycles except for rw with predicates
        {:model :PL-2.99, :subgraph [:union ww wwp wr wrp rw]}

        ; Serializable requires no data cycles
        {:model :PL-3, :subgraph [:union ww wwp wr wrp rw rwp]}

        ; Strong session variants add process edges
        {:model :strong-session-PL-1, :subgraph [:union ww wwp process]}
        {:model :strong-session-PL-2, :subgraph [:union ww wwp wr wrp process]}
        {:model    :strong-session-snapshot-isolation
         :subgraph [:extension
                    [:union ww wwp wr wrp process]
                    [:union rw rwp]]}
        {:model    :strong-session-serializable
         :subgraph [:union ww wwp wr wrp rw rwp process]}

        ; Strong variants add realtime
        {:model :strong-PL-1, :subgraph [:union ww wwp realtime]}
        {:model :strong-PL-2, :subgraph [:union ww wwp wr wrp realtime]}
        {:model    :strong-snapshot-isolation
         :subgraph [:extension
                    [:union ww wwp wr wrp realtime]
                    [:union rw rwp]]}
        {:model :PL-SS, :subgraph [:union ww wwp wr wrp rw rwp realtime]}
        ]
       (mapv (fn [{:keys [model] :as spec}]
               ; Add a :type field for the anomaly type, and a :friendly-model
               ; field for the friendly model name
               (assoc spec
                      :type (keyword (str (name model) "-cycle-exists"))
                      :friendly-model (cm/friendly-model-name model))))))

(defn cycle-exists-subgraph
  "Takes a filtered-graphs fn for a transaction graph, and a subgraph spec ala
  cycle-exists-specs. Computes the given subgraph from it."
  [fg spec]
  (if (rels/bit-rels? spec)
    ; Ah, good, we have specific rels to project to
    (fg spec)
    ; AST interpreter
    (let [[f & args] spec]
      (case f
        :union
        ; We can do something clever here. If we're unioning n IRels
        ; directly, we can just project the graph to those relationships and
        ; get their union in constant time.
        (let [split (group-by rels/bit-rels? args)
              kws   (when-let [kws (get split true)]
                      (fg (reduce rels/union rels/none kws)))
              other (when-let [other (get split false)]
                      (->> other
                           (mapv (partial cycle-exists-subgraph fg))
                           (apply g/digraph-union)))]
          (cond (nil? other) kws
                (nil? kws)   other
                true         (g/digraph-union kws other)))

        :extension
        (do (assert (= 2 (count args)))
            (g/sequential-extension (cycle-exists-subgraph fg (first args))
                                    (cycle-exists-subgraph fg (second args))))

        :composition
        (do (assert (= 2 (count args)))
            (g/sequential-composition (cycle-exists-subgraph fg (first args))
                                      (cycle-exists-subgraph fg (second args))))))))

(defn cycle-exists-friendly-subgraph
  "Takes a subgraph spec and converts it to one with keywords instead of
  bitrels."
  [x]
  (cond (rels/bit-rels? x)
        (first (.toClojure ^BitRels x))

        (vector? x)
        (mapv cycle-exists-friendly-subgraph x)

        true x))

(defn nontrivial-scc?
  "Given a graph g, is an SCC (bifurcan set of vertices) in it a nontrivial
  one? By that we mean it is either bigger than one vertex, or if it has a
  single vertex, it has a self-edge."
  [g scc]
  (case (b/size scc)
    0 false ; how did you even get here
    ; .in is slightly faster on graphs than .out
    1 (let [v (b/nth scc 0)]
        (bs/contains? (bg/in g v) v))
    true))

(defn cycle-exists-cases
  "Finding cycles can be expensive, but we can actually distinguish between
  several levels simply by proving an SCC exists. This function takes a
  filtered-graphs fn for an op graph. It returns a vector of anomaly maps like:

    {:type     :PL-2-cycle-exists ; A cycle violating PL-2 exists... somewhere
     :not      :read-committed  ; The isolation level which must not hold
     :subgraph [:union :ww :wr] ; The weakest subgraph which contained an SCC
     :scc-size 4                ; The size of the smallest SCC found
     :scc      #{1, 5, 7, 8}}   ; The set of indices of the transactions in
                                ; that SCC"
  [fg]
  (loopr [errs       []
          redundant? #{}]
         [{:keys [model friendly-model subgraph type]} cycle-exists-specs]
         (if (redundant? model)
           (recur errs redundant?)
           (let [sg   (cycle-exists-subgraph fg subgraph)
                 ; We have to find singleton SCCs: a ww b rw a yields a -> a.
                 sccs (->> (bg/strongly-connected-components sg true)
                           (filter (partial nontrivial-scc? sg))
                           (sort-by b/size))
                 scc  (g/->clj (first sccs))]
             (if-not (seq sccs)
               (recur errs redundant?)
               (recur (conj errs
                            {:type     type
                             :not      friendly-model
                             :subgraph (cycle-exists-friendly-subgraph subgraph)
                             :scc-size (count scc)
                             :scc      (into (sorted-set) (map :index scc))})
                      (into redundant? (cm/all-impossible-models #{model}))))))
         errs))

(defn remove-redundant-cycle-exists
  "Cycle-exists anomalies are a fallback mechanism: if we can demonstrate a
  specific cycle, an internal anomaly, a lost update, etc., there's really not
  much benefit in telling people 'hey a cycle exists somewhere in these 437
  transactions'. However, we don't *know* when we're doing cycle search whether
  our cycle-exists anomalies will be redundant or not.

  This function takes a map of anomaly types to anomaly collections, ala:

     {:G1c               [...]
      :PL-2-cycle-exists [...]}}

  We return a version of this map omitting redundant cycle-exists anomalies."
  [anomalies]
  (let [; What non-existence anomalies exist?
        other-anomaly-types (remove (fn [t]
                                      (re-find #"-cycle-exists$" (name t)))
                                    (keys anomalies))
        ; What models do they alone rule out?
        impossible-models (cm/anomalies->impossible-models other-anomaly-types)
        ; Which means we can omit...
        omittable (->> cycle-exists-specs
                       (filter (comp impossible-models :model))
                       (map :type)
                       set)]
    (reduce dissoc anomalies omittable)))

;; Cycle finding

(def cycle-explainer
  "This cycle explainer wraps elle.core's cycle explainer, and categorizes
  cycles based on what kinds of edges they contain; e.g. an all-ww cycle is
  :G0, one with realtime, ww, and wr edges is :G1c-realtime, etc."
  (reify elle/CycleExplainer
    (explain-cycle [_ pair-explainer cycle]
      (let [ex (elle/explain-cycle elle/cycle-explainer pair-explainer cycle)
            ; What types of relationships are involved here?
            type-freqs (frequencies (map :type (:steps ex)))
            realtime  (:realtime  type-freqs 0)
            process   (:process   type-freqs 0)
            ww        (:ww        type-freqs 0)
            wwp       (:wwp       type-freqs 0)
            wr        (:wr        type-freqs 0)
            wrp       (:wrp       type-freqs 0)
            rw        (:rw        type-freqs 0)
            rwp       (:rwp       type-freqs 0)
            ; Any predicate rw edges? TODO: we're going to move to :rwp edges
            ; later, and can drop the :predicate? check.
            predicate? (or (boolean (seq (filter :predicate? (:steps ex))))
                           (< 0 rwp))
            ; Are any pair of rw's together?
            rw-adj?   (->> (:steps ex)
                           (cons (last (:steps ex))) ; For last->first edge
                           (map :type)
                           (partition 2 1)           ; Take pairs
                           (filter (fn rwrw? [[a b]] ; Find an rw, rw pair
                                     (and (or (identical? a :rw)
                                              (identical? a :rwp))
                                          (or (identical? b :rw)
                                              (identical? b :rwp)))))
                           seq
                           boolean)
            ; We compute a type based on data dependencies alone
            data-dep-type (cond (= 1 (+ rw rwp))
                                (if predicate?
                                  "G-single"
                                  "G-single-item")

                                (< 1 (+ rw rwp))
                                (if rw-adj?
                                  (if predicate?
                                    "G2"
                                    "G2-item")
                                  (if predicate?
                                    "G-nonadjacent"
                                    "G-nonadjacent-item"))

                                (< 0 (+ wr wrp)) "G1c"
                                (< 0 (+ ww wwp)) "G0"
                                true (throw (IllegalStateException.
                                              (str "Don't know how to classify"
                                                   (pr-str ex)))))
            ; And tack on a -process or -realtime tag if there are those types
            ; of edges.
            subtype (cond (< 0 realtime) "-realtime"
                          (< 0 process)  "-process"
                          true           "")]
        ; (prn :type (keyword (str data-dep-type subtype)))
        (assoc ex :type (keyword (str data-dep-type subtype)))))

    (render-cycle-explanation [_ pair-explainer
                               {:keys [type cycle steps] :as ex}]
      (elle/render-cycle-explanation
        elle/cycle-explainer pair-explainer ex))))

(def base-cycle-anomaly-specs
  "We define a specification language for different anomaly types, and a small
   interpreter to search for them. An anomaly is specified by a map including:

     :rels         A BitRels set of relationships which can be used as edges in
                   the cycle.

   There may also be supplementary relationships which may be used in addition
   to rels:

     :nonadjacent-rels  If present, a set of relationships which must may be
                        used for non-adjacent edges.

     :single-rels    Edges intersecting this set must appear exactly once in
                     this cycle.

     :multiple-rels  Edges intersecting this set must appear more than once in
                     the cycle.

     :required-rels  A set of bitrels. We need at least one edge intersecting
                     each element of this set.

   And optionally:

     :type         If present, the cycle explainer must tell us any cycle is of
                   this :type specifically."
  (sorted-map-by cm/anomaly-depth-compare
    :G0        {:rels (rels/union ww wwp)}
    ; G1c has at least a wr edge, and can take either ww or wr.
    :G1c       {:rels          (rels/union ww wwp wr wrp)
                ; We need either a wr or wrp; otherwise it's just G0
                :required-rels #{(rels/union wr wrp)}}
    ; G-single-item is a special case of G-single where we only consider rw,
    ; not rwp.
    :G-single-item {:rels         (rels/union ww wwp wr wrp)
                    :single-rels  rw
                    :type         :G-single-item}
    ; G-single takes ww/wr normally, but has exactly one rw. Note that some
    ; G-singles are G2-item and we can't distinguish them at the graph level.
    :G-single  {:rels        (rels/union ww wwp wr wrp)
                :single-rels (rels/union rw rwp)
                :type        :G-single}
    ; G-nonadjacent-item: like G-nonadjacent, but no predicate rw edges.
    :G-nonadjacent-item {:rels             (rels/union ww wwp wr wrp)
                         :nonadjacent-rels rw
                         :multiple-rels    rw
                         :type             :G-nonadjacent-item}
    ; G-nonadjacent is the more general form of G-single: it has multiple
    ; nonadjacent rw edges.
    :G-nonadjacent {:rels             (rels/union ww wwp wr wrp)
                    ; TODO: these should have rwp too
                    :nonadjacent-rels (rels/union rw rwp)
                    :multiple-rels    (rels/union rw rwp)
                    :type             :G-nonadjacent}
    ; G2-item, likewise, starts with an anti-dep edge, but allows more, and
    ; insists on being G2, rather than G-single. Not bulletproof, but G-single
    ; is worse, so I'm OK with it.
    :G2-item   {:rels          (rels/union ww wwp wr wrp rw)
                ; A single rw rel is trivially G-Single
                :multiple-rels rw
                :type         :G2-item}
    ; G2 is identical, except we want a cycle explained as G2
    ; specifically--it'll have at least one :predicate? edge.
    :G2        {:rels          (rels/union ww wwp wr wrp rw rwp)
                :multiple-rels (rels/union rw rwp)
                :type          :G2}))

(defn cycle-anomaly-spec-variant
  "Takes a variant (:process or :realtime) and a cycle anomaly pair of name and
  spec map, as in base-cycle-anomaly-specs. Returns a new [name' spec'] pair
  for the process/realtime variant of that spec."
  [variant [anomaly-name spec]]
  (let [; You can take variant edges any time
        rel (case variant
              :realtime BitRels/REALTIME
              :process  BitRels/PROCESS)
        spec' (update spec :rels rels/union rel)
        ; Those edges are also required, in addition to any other edges
        r'    (:required-rels spec #{})
        spec' (assoc spec' :required-rels (conj r' rel))
        ; If there's a type, we need to match its variant.
        spec' (if-let [t (:type spec)]
                (assoc spec' :type (keyword (str (name anomaly-name) "-"
                                                 (name variant))))
                spec')]
    [(keyword (str (name anomaly-name) "-" (name variant))) spec']))

(def cycle-anomaly-specs
  "Like base-cycle-anomaly-specs, but with realtime and process variants."
  (into base-cycle-anomaly-specs
        (mapcat (juxt identity
                      (partial cycle-anomaly-spec-variant :process)
                      (partial cycle-anomaly-spec-variant :realtime))
                base-cycle-anomaly-specs)))

(def cycle-types
  "All types of cycles we can detect."
  (set (keys cycle-anomaly-specs)))

(def process-anomaly-types
  "Anomaly types involving process edges."
  (set (filter (comp (partial re-find #"-process") name) cycle-types)))

(def realtime-anomaly-types
  "Anomaly types involving realtime edges."
  (set (filter (comp (partial re-find #"-realtime") name) cycle-types)))

(def unknown-anomaly-types
  "Anomalies which cause the analysis to yield :valid? :unknown, rather than
  false."
  #{:empty-transaction-graph
    :cycle-search-timeout})

(defn prohibited-anomaly-types
  "Takes an options map with

      :consistency-models   A collection of consistency models we expect hold
      :anomalies            A set of additional, specific anomalies we don't
                            want to see

  and returns a set of anomalies which would constitute a test failure.
  Defaults to {:consistency-models [:strict-serializable]}"
  [opts]
  (set/union (cm/all-anomalies-implying (:anomalies opts))
             (cm/anomalies-prohibited-by
               (:consistency-models opts [:strict-serializable]))))

(defn reportable-anomaly-types
  "Anomalies worth reporting on, even if they don't cause the test to fail."
  [opts]
  (set/union (prohibited-anomaly-types opts)
             unknown-anomaly-types))

(defn additional-graphs
  "Given options, determines what additional graphs we'll need to consider for
  this analysis. Options:

      :consistency-models   A collection of consistency models we expect hold
      :anomalies            A set of additional, specific anomalies we don't
                            want to see
      :additional-graphs    If you'd like even more dependencies"
  [opts]
  (let [ats (reportable-anomaly-types opts)]
    (-> ; If we need realtime, use realtime-graph. No need to bother
        ; with process, cuz we'll find those too.
        (cond (seq (set/intersection realtime-anomaly-types ats))
              #{elle/realtime-graph}

              ; If we're looking for any process anomalies...
              (seq (set/intersection process-anomaly-types ats))
              #{elle/process-graph}

              ; Otherwise, the usual graph is fine.
              true nil)
        ; Tack on any other requested graphs.
        (into (:additional-graphs opts)))))

(defn filtered-graphs
  "Takes a history and graph g. Returns a function that takes a set of
  relationships, and yields g filtered to just those relationships. Memoized."
  [history graph]
  (memoize (fn filter-graph [rels]
             (if (< 16384 (b/size graph))
               (g/parallel-project-rels history rels graph)
               (g/project-rels rels graph)))))

(defn warm-filtered-graphs!
  "I thought memoizing this and making it lazy was a good idea, and it might be
  later, but it also pushes a BIG chunk of work into initial cycle search---the
  timeout fires and kills a whole bunch of searches because the graph isn't
  computed yet, and that's silly. So instead, we explicitly precompute these.

  Returns fg, but as a side effect, with all the relevant filtered graphs for
  our search precomputed."
  [fg]
  (->> (vals cycle-anomaly-specs)
       (mapcat (juxt :rels :first-rels :rest-rels))
       (remove nil?)
       set
       (mapv fg))
  fg)

(def cycle-search-timeout
  "How long, in milliseconds, to look for a certain cycle in any given SCC."
  1000)

(defn cycle-cases-in-scc-fallback
  "This finds SOME cycle via DFS in a graph (guaranteed to be strongly
  connected), as a fallback in case our BFS gets stuck. We invoke this if our
  search times out."
  [g fg pair-explainer]
  (let [c (loop [rels [ww
                       (rels/union ww realtime process)
                       (rels/union ww wr)
                       (rels/union ww wr realtime process)
                       (rels/union ww wr rw)
                       (rels/union ww wr rw realtime process)]]
            (if-not (seq rels)
              ; Out of projections; fall back to the total scc, which
              ; MUST have a cycle.
              (g/fallback-cycle g)

              ; Try the graph which has just those relationships and
              ; that particular SCC
              (if-let [sub-scc (-> ^IGraph (fg (first rels))
                                   (g/strongly-connected-components)
                                   first)]
                ; Hey, we've got a smaller SCC to focus on!
                (g/fallback-cycle g)
                ; No dice
                (recur (next rels)))))]
    (elle/explain-cycle cycle-explainer
                        pair-explainer
                        c)))

(defn cycle-in-scc-of-type
  "Takes a graph, a filtered-graph function, a pair explainer, and a cycle
  anomaly type specification from cycle-anomaly-specs. Tries to find a cycle
  matching that specification in the graph. Returns the explained cycle, or
  nil if none found."
  [opts g fg pair-explainer
   [type {:keys [rels nonadjacent-rels single-rels multiple-rels required-rels
                 ]
          :as spec}]]
  ; First pass: look for a candidate
  (let [;_ (info :type type :spec spec)
        ;_ (info ":preds\n" (with-out-str (pprint preds)))
        ;_ (info :transition transition)
        cycle (bfs/search (fg (rels/union rels
                                          nonadjacent-rels
                                          (reduce rels/union required-rels)
                                          single-rels
                                          multiple-rels))
                          spec)]
    (when cycle
      ;(info "Cycle:\n" (with-out-str (pprint cycle)))
      (let [ex (elle/explain-cycle cycle-explainer pair-explainer cycle)]
            ; Our cycle spec here isn't QUITE complete: the explainer might
            ; declare it (e.g.) g2-item vs g2. If there's a type constraint, we
            ; explain the cycle and check the type matches.
            ;(when (not= type (:type ex))
            ;  (info "Was looking for" type "but found a" (:type ex)
            ;        (with-out-str
            ;          (prn)
            ;          (pprint spec)
            ;          (prn)
            ;          (pprint ex))))
            (if (:type spec)
              (do ; _ (info "Filtering explanation")
                  ; _ (prn :explanation ex)
                  (when (= (:type spec) (:type ex))
                    ex))
              ex)))))

(defn cycle-exists-cases->impossible-cycle-anomalies
  "Takes a complete collection of cycle-exists cases for a graph, and returns a
  set of cycle anomalies which *must not* exist in the graph. For instance, if
  :snapshot-isolation doesn't appear in the cycle exists cases, we don't need
  to check for :G0, :G1c, or :G-single: they can't possibly be there."
  [cases]
  (let [; We know these models are impossible
        impossible-models (set (cm/all-impossible-models
                                 (map :not cases)))
        ;_ (info :impossible-models impossible-models)
        ; And by extension these models
        ; Which means we did *not* find a cyclic anomaly that would have
        ; invalidated these models.
        possible-models (set/difference (set (map :model cycle-exists-specs))
                                        impossible-models)
        ;_ (info :possible-models possible-models)
        ; Which cyclic anomalies are proscribed by the possible models? These
        ; can't exist.
        impossible-anomalies (set/intersection
                               cycle-types
                               (cm/anomalies-prohibited-by possible-models))]
    ;(info :impossible-anomalies impossible-anomalies)
    impossible-anomalies))

(defn merge-cycle-exists+cycle-cases
  "Takes a vector of cycle-exists cases and a vector of cycle cases. Eliminates
  any cycle-exists cases where we have a corresponding cycle case. Returns a
  vector of all cases mixed together."
  [cycle-exists-cases cycle-cases]
  (let [; What kinds of cycles did we find?
        cycle-types (set (map :type cycle-cases))
        ; What consistency models can we rule out based on cycles alone?
        impossible-models (cm/anomalies->impossible-models cycle-types)
        ; Skip any cycle-exists cases where we have a cycle that proves that
        ; specific level is impossible
        cycle-exists-cases (vec (remove (comp impossible-models
                                              cm/canonical-model-name
                                              :not)
                                        cycle-exists-cases))
        ]
    (into cycle-exists-cases cycle-cases)))

(defn cycle-cases-in-scc
  "Searches a graph restricted to a single SCC for cycle anomalies. See
  cycle-cases."
  [opts g fg pair-explainer]
  ; (info "Checking scc of size" (b/size g))
  (let [; First, check for cycle existence. We'll use this to guide our search.
        cycle-exists-cases (cycle-exists-cases fg)
        ;_ (info "cycle-exists-cases")
        ;_ (pprint (map :type cycle-exists-cases))
        ;_ (info "We're going to skip"
        ;        (cycle-exists-cases->impossible-cycle-anomalies cycle-exists-cases))
        ; We're going to do a partial search which can time out. If that
        ; happens, we want to preserve as many of the cycles that we found as
        ; possible, and offer an informative error message. These two variables
        ; help us do that.
        types  (atom [])  ; What kind of anomalies have we searched for?
        cycles (atom [])] ; What anomalies did we find?
    (util/timeout
      (:cycle-search-timeout opts cycle-search-timeout)
      ; If we time out...
      (let [types  @types
            cycles @cycles]
        ;(info "Timing out search for" (peek types) "in SCC of" (b/size g)
        ;      "transactions (checked" (str (pr-str (drop-last types)) ")"))
        ;(info :scc (with-out-str (pprint scc)))
        ; We generate two types of anomalies no matter what. First, an anomaly
        ; that lets us know we failed to complete the search. Second, a
        ; fallback cycle so there's SOMETHING from this SCC.
        (into [{:type               :cycle-search-timeout
                :anomaly-spec-type  (peek types)
                :does-not-contain   (->> (drop-last types)
                                         (remove (set (map :type cycles))))
                :scc-size           (b/size g)}
               (cycle-cases-in-scc-fallback g fg pair-explainer)]
              ; Then any cycles we already found.
              (into cycle-exists-cases cycles)))
      ; Try increasingly severe anomalies, updating cycles as side effect
      (reduce (fn check-type [redundant? [type :as type+spec]]
                ; Don't check a type we've already implied
                (if (redundant? type)
                  (do ;(info "Skipping redundant search for" type)
                      redundant?)
                  (do ;(info "Checking for" type)
                      (swap! types conj type)
                      (if-let [cycle (cycle-in-scc-of-type
                                       opts g fg pair-explainer type+spec)]
                        (do (swap! cycles conj cycle)
                            ;(info "Found a" type "so we can skip" (cm/all-implied-anomalies [type]))
                            (into redundant? (cm/all-implied-anomalies [type])))
                        redundant?))))
              (cycle-exists-cases->impossible-cycle-anomalies
                cycle-exists-cases)
              cycle-anomaly-specs)
      ; Combine with cycle-exists-cases
      (into cycle-exists-cases @cycles))))

(defn cycle-cases-in-graph
  "Takes a search options map (see cycles), a pair explainer that
  can justify relationships between pairs of transactions, and a graph. Returns
  a map of anomaly names to sequences of cycle explanations for each. We find:

  :G0                 ww edges only
  :G1c                ww, at least one wr edge
  :G-single           ww, wr, exactly one rw
  :G-nonadjacent      ww, wr, 2+ nonadjacent rw
  :G2-item            ww, wr, 2+ rw
  :G2                 ww, wr, 2+ rw, with predicate edges

  :G0-process         G0, but with process edges
  ...

  :G0-realtime        G0, but with realtime edges
  ...

  Note that while this works for any transaction graph, including the full
  graph, we call this function with independent SCCs from the full graph.
  There's no point in exploring beyond the bounds of a single SCC; there can't
  possibly be a cycle out there. This means we can avoid materializing filtered
  graphs and searching the entire graph."
  [history opts pair-explainer graph]
  ; (info "Checking SCC of" (b/size graph) "ops")
  (let [fg (-> (filtered-graphs history graph)
               ; Warming filtered graphs may actually be more trouble than it's
               ; worth now: graphs are smaller and we only filter some, not all
               ; relationships, depending on how our exploration goes.
               #_ warm-filtered-graphs!)]
    (->> (cycle-cases-in-scc opts graph fg pair-explainer)
         (group-by :type))))

(defn cycles
  "Takes an options map, including a collection of expected consistency models
  :consistency-models, a set of additional :anomalies, an analyzer function,
  and a history. Analyzes the history and yields the analysis, plus an anomaly
  map like {:G1c [...]}."
  [opts analyzer history]
  (let [; Analyze the history. Duplicating some of the logic in core/check-
        ; here...
        ;_ (info "Building graphs")
        {:keys [anomalies graph explainer]} (analyzer (h/client-ops history))
        anomalies (if (= 0 (b/size graph))
                    (assoc anomalies :empty-transaction-graph true)
                    anomalies)
        ;_      (info "Graph built")
        sccs   (g/strongly-connected-components graph)
        ;_ (info "Found" (count sccs) "top-level SCCs")

        ; Spawn a task to check each SCC
        scc-tasks (mapv (fn per-scc [scc]
                          (h/task history cycle-cases-in-graph []
                                  (let [g (bg/select graph (bs/from scc))]
                                    (cycle-cases-in-graph
                                      history opts explainer g))))
                        sccs)

        ; And merge together
        anomalies (reduce (partial merge-with into)
                          anomalies
                          (map deref scc-tasks))]

    ;(pprint anomalies)
    ; Merge our cases into the existing anomalies map.
    {:graph     graph
     :explainer explainer
     :sccs      sccs
     :anomalies anomalies}))

(defn cycles!
  "Like cycles, but writes out files as a side effect. Only writes files for
  relevant anomalies."
  [opts analyzer history]
  (let [analysis (cycles opts analyzer history)
        anomalies (select-keys (:anomalies analysis)
                               (reportable-anomaly-types opts))]
    ; Shall we render output?
    (when-let [d (:directory opts)]
      ; First, text files.
      (doseq [[type cycles] anomalies]
        (when (cycle-types type)
          (elle/write-cycles! (assoc opts
                                     :pair-explainer  (:explainer analysis)
                                     :cycle-explainer cycle-explainer
                                     :filename        (str (name type) ".txt"))
                              cycles)))

      ; Then (in case they break), GraphViz plots.
      ; We do a directory for SCCs...
      (viz/plot-analysis! analysis (io/file d "sccs") opts)

      ; Then for each class of anomaly...
      (dorun
        (pmap (fn [[type cycles]]
                (when (cycle-types type)
                  ; plot-analysis! expects a list of sccs, which it's gonna go
                  ; through and plot. We're going to give it just the component
                  ; it needs to show each particular cycle explanation.
                  (let [sccs (map (comp set :cycle) cycles)]
                    (viz/plot-analysis! (assoc analysis :sccs sccs)
                                        (io/file d (name type))
                                        opts))))
              anomalies)))

    ; And return analysis
    analysis))

(defn result-map
  "Takes options, including :anomalies and :consistency-models, which define
  what specific anomalies and consistency models to look for, and a map of
  anomaly names to anomalies, and returns a map of the form...

  {:valid?        true | :unknown | false
   :anomaly-types [:g1c ...]
   :anomalies     {:g1c [...] ...}
   :impossible-models #{:snapshot-isolation ...}}"
  [opts anomalies]
  ;(info :anomalies anomalies)
  ;(info :reportable-anomaly-types (reportable-anomaly-types opts))
  (let [bad         (select-keys anomalies (prohibited-anomaly-types opts))
        reportable  (select-keys anomalies (reportable-anomaly-types opts))
        reportable  (remove-redundant-cycle-exists reportable)]
    (if (empty? reportable)
      ; TODO: Maybe return anomalies and/or a boundary here too, and just not
      ; flag them as invalid? Maybe? I dunno, might be noisy, especially if we
      ; expect to see them all the time.
      {:valid? true}
      (merge {:valid?            (cond (seq bad)          false
                                       (seq reportable)   :unknown
                                       true               true)
              :anomaly-types     (sort (keys reportable))
              :anomalies         reportable}
             (cm/friendly-boundary (keys anomalies))))))

;; Generator

(defn key-dist-scale
  "Takes a key-dist-base and a key count. Computes the scale factor used for
  random number selection used in rand-key."
  [key-dist-base key-count]
  (-> (Math/pow key-dist-base key-count)
      (- 1)
      (* key-dist-base)
      (/ (- key-dist-base 1))))

(defn rand-key
  "Helper for generators. Takes a key distribution (e.g. :uniform or
  :exponential), a key distribution scale, a key distribution base, and a
  vector of active keys. Returns a random active key."
  [key-dist key-dist-base key-dist-scale active-keys]
  (case key-dist
    :uniform     (rand-nth active-keys)
    :exponential (let [ki (-> (rand key-dist-scale)
                              (+ key-dist-base)
                              Math/log
                              (/ (Math/log key-dist-base))
                              (- 1)
                              Math/floor
                              long)]
                   (nth active-keys ki))))

(defn fresh-key
  "Takes a key and a vector of active keys. Returns the vector with that key
  replaced by a fresh key."
  [^java.util.List active-keys k]
  (let [i (.indexOf active-keys k)
        k' (inc (reduce max active-keys))]
    (assoc active-keys i k')))

(defn wr-txns
  "A lazy sequence of write and read transactions over a pool of n numeric
  keys; every write is unique per key. Options:

    :key-dist             Controls probability distribution for keys being
                          selected for a given operation. Choosing :uniform
                          means every key has an equal probability of appearing.
                          :exponential means that key i in the current key pool
                          is k^i times more likely than the first key to be
                          chosen. Defaults to :exponential.

    :key-dist-base        The base for an exponential distribution. Defaults
                          to 2, so the first key is twice as likely as the
                          second, which is twice as likely as the third, etc.

    :key-count            Number of distinct keys at any point. Defaults to
                          10 for exponential, 3 for uniform.

    :min-txn-length       Minimum number of operations per txn

    :max-txn-length       Maximum number of operations per txn

    :max-writes-per-key   Maximum number of operations per key"
  ([opts]
   (let [key-dist  (:key-dist  opts :exponential)
         key-count (:key-count opts (case key-dist
                                      :exponential 10
                                      :uniform     3))]
     (wr-txns (assoc opts
                     :key-dist  key-dist
                     :key-count key-count)
              {:active-keys (vec (range key-count))})))
  ([opts state]
   (lazy-seq
     (let [min-length           (:min-txn-length      opts 1)
           max-length           (:max-txn-length      opts 2)
           max-writes-per-key   (:max-writes-per-key  opts 32)
           key-dist             (:key-dist            opts :exponential)
           key-dist-base        (:key-dist-base       opts 2)
           key-count            (:key-count           opts)
           ; Choosing our random numbers from this range converts them to an
           ; index in the range [0, key-count).
           key-dist-scale       (key-dist-scale key-dist-base key-count)
           length               (+ min-length (rand-int (- (inc max-length)
                                                           min-length)))
           [txn state] (loop [length  length
                              txn     []
                              state   state]
                         (let [^java.util.List active-keys
                               (:active-keys state)]
                           (if (zero? length)
                             ; All done!
                             [txn state]
                             ; Add an op
                             (let [f (rand-nth [:r :w])
                                   k (rand-key key-dist key-dist-base
                                               key-dist-scale active-keys)
                                   v (when (= f :w) (get state k 1))]
                               (if (and (= :w f)
                                        (< max-writes-per-key v))
                                 ; We've updated this key too many times!
                                 (let [state' (update state :active-keys
                                                      fresh-key k)]
                                   (recur length txn state'))
                                 ; Key is valid, OK
                                 (let [state' (if (= f :w)
                                                (assoc state k (inc v))
                                                state)]
                                   (recur (dec length)
                                          (conj txn [f k v])
                                          state')))))))]
       (cons txn (wr-txns opts state))))))

(defn gen
  "Takes a sequence of transactions and returns a sequence of invocation
  operations."
  [txns]
  (map (fn [txn] {:type :invoke, :f :txn, :value txn}) txns))
