(ns elle.txn
  "Functions for cycle analysis over transactional workloads."
  (:require [clojure [pprint :refer [pprint]]
                      [set :as set]]
            [clojure.tools.logging :refer [info warn]]
            [clojure.java.io :as io]
            [elle [core :as elle]
                  [consistency-model :as cm]
                  [graph :as g]
                  [viz :as viz]]
            [jepsen.txn :as txn :refer [reduce-mops]]
						[knossos.op :as op])
  (:import (io.lacuna.bifurcan LinearMap
                               Map)))


(defn op-mops
  "A lazy sequence of all [op mop] pairs from a history."
  [history]
  (mapcat (fn [op] (map (fn [mop] [op mop]) (:value op))) history))

(defn ok-keep
	"Given a function of operations, returns a sequence of that function applied
  to all ok operations. Returns nil iff every invocation of f is nil."
  [f history]
  (->> history
       (filter op/ok?)
       (keep f)
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
  (reduce-mops (fn index [failed op [f k v :as mop]]
                 (if (and (op/fail? op)
                          (write? f))
                   (assoc-in failed [k v] op)
                   failed))
               {}
               history))

(defn intermediate-writes
  "Returns a map of keys to maps of intermediate write values to the operations
  which wrote them. Used for detecting intermediate reads."
  [write? history]
  (reduce (fn [im op]
            ; Find intermediate writes for this particular txn by
            ; producing two maps: intermediate keys to values, and
            ; final keys to values in this txn. We shift elements
            ; from final to intermediate when they're overwritten.
            (first
              (reduce (fn [[im final :as state] [f k v]]
                        (if (write? f)
                          (if-let [e (final k)]
                            ; We have a previous write of k
                            [(assoc-in im [k e] op)
                             (assoc final k v)]
                            ; No previous write
                            [im (assoc final k v)])
                          ; Something other than an append
                          state))
                      [im {}]
                      (:value op))))
          {}
          history))

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
            wr        (:wr        type-freqs 0)
            rw        (:rw        type-freqs 0)
            ; We compute a type based on data dependencies alone
            data-dep-type (cond (< 1 rw) "G2"
                                (= 1 rw) "G-single"
                                (< 0 wr) "G1c"
                                (< 0 ww) "G0"
                                true (throw (IllegalStateException.
                                              (str "Don't know how to classify"
                                                   (pr-str ex)))))
            ; And tack on a -process or -realtime tag if there are those types
            ; of edges.
            subtype (cond (< 0 realtime) "-realtime"
                          (< 0 process)  "-process"
                          true           "")]
        (assoc ex :type (keyword (str data-dep-type subtype)))))

    (render-cycle-explanation [_ pair-explainer
                               {:keys [type cycle steps] :as ex}]
      (elle/render-cycle-explanation
        elle/cycle-explainer pair-explainer ex))))

(def cycle-anomaly-specs
  "We define a specification language for different anomaly types, and a small
   interpreter to search for them. An anomaly is specified by a map including:

     :rels         A set of relationships which must intersect with every
                   edge in the cycle

     - or -

     :first-rels   A set of relationships which must intersect with the first
                   edge in the cycle.
     :rest-rels    A set of relationships which must intersect with remaining
                   edges.

     - and optionally -

     :filter-ex    A predicate over a cycle explanation. We use this
                   to restrict cycles to e.g. *just* G2 instead of G-single."
  {:G0        {:rels #{:ww}}
   ; We want at least one wr edge, so we specify that as first-rels.
   :G1c       {:first-rels #{:wr}
               :rest-rels  #{:ww :wr}}
   ; Likewise, G-single starts with the anti-dependency edge.
   :G-single  {:first-rels  #{:rw}
               :rest-rels   #{:ww :wr}}
   ; G2, likewise, starts with an anti-dep edge, but allows more, and insists
   ; on being G2, rather than G-single. Not bulletproof, but G-single is worse,
   ; so I'm OK with it.
   :G2        {:first-rels  #{:rw}
               :rest-rels   #{:ww :wr :rw}
               :filter-ex   (comp #{:G2} :type)}

   ; A process G0 can use any number of process and ww edges--process is
   ; acyclic, so there's got to be at least one ww edge. We also demand the
   ; resulting cycle be G0-process, to filter out plain old G0s.
   :G0-process        {:rels        #{:ww :process}
                       :filter-ex   (comp #{:G0-process} :type)}
   ; G1c-process needs at least one wr-edge to distinguish itself from
   ; G0-process.
   :G1c-process       {:first-rels  #{:wr}
                       :rest-rels   #{:ww :wr :process}
                       :filter-ex   (comp #{:G1c-process} :type)}
   ; G-single-process starts with an anti-dep edge and can use processes from
   ; there.
   :G-single-process  {:first-rels  #{:rw}
                       :rest-rels   #{:ww :wr :process}
                       :filter-ex   (comp #{:G-single-process} :type)}
   ; G2-process starts with an anti-dep edge, and allows anything from there.
   ; Plus it's gotta be G2-process, so we don't report G2s or G-single-process
   ; etc.
   :G2-process        {:first-rels  #{:rw}
                       :rest-rels   #{:ww :wr :rw :process}
                       :filter-ex   (comp #{:G2-process} :type)}

   ; Ditto for realtime
   :G0-realtime        {:rels        #{:ww :realtime}
                        :filter-ex   (comp #{:G0-realtime} :type)}
   :G1c-realtime       {:first-rels  #{:wr}
                        :rest-rels   #{:ww :wr :realtime}
                        :filter-ex   (comp #{:G1c-realtime} :type)}
   :G-single-realtime  {:first-rels  #{:rw}
                        :rest-rels   #{:ww :wr :realtime}
                        :filter-ex   (comp #{:G-single-realtime} :type)}
   :G2-realtime        {:first-rels  #{:rw}
                        :rest-rels   #{:ww :wr :rw :realtime}
                        :filter-ex   (comp #{:G2-realtime} :type)}})

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
  #{:empty-transaction-graph})

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
  "Takes a graph g. Returns a function that takes a set of relationships, and
  yields g filtered to just those relationships. Memoized."
  [graph]
  (memoize (fn [rels] (g/filter-relationships rels graph))))

(defn cycle-cases
  "We take the unified graph, a pair explainer that can justify relationships
  between pairs of transactions, and a collection of strongly connected
  components in the unified graph. We proceed to find allllll kinds of cycles,
  returning a map of anomaly names to sequences of cycle explanations for each.
  We find:

  :G0                 ww edges only
  :G1c                ww, at least one wr edge
  :G-single           ww, wr, exactly one rw
  :G2                 ww, wr, 2+ rw

  :G0-process         G0, but with process edges
  ...

  :G0-realtime        G0, but with realtime edges
  ..."
  [graph pair-explainer sccs]
  (let [fg (filtered-graphs graph)]
    ; This is basically a miniature interpreter for the anomaly specification
    ; language we defined above. It's... clean, but it also duplicates a lot of
    ; work--for instance, a G1c cycle will be detected three times, by G1c,
    ; G1c-process, and G1c-realtime; we then have to ignore 2 of those in the
    ; filter step. I don't think this is super expensive, but future self, if
    ; you're looking at a profiler and trying to find constant factors to
    ; optimize, this might be a good spot to start.
    (->> (for [scc          sccs
               [type spec]  cycle-anomaly-specs]
           ; First, find a cycle using the spec.
           (let [;_      (prn)
                 ;_      (prn :spec type spec)
                 cycle (if-let [rels (:rels spec)]
                         ; All edges in the same set of relationships
                         (do ;(prn :find-cycle rels)
                             ;(prn :graph (fg rels))
                             (g/find-cycle (fg rels) scc))
                         ; First edge special
                         (do ;(prn :find-first-cycle (:first-rels spec)
                             ;     (:rest-rels spec))
                             ;(prn :first-graph (fg (:first-rels spec)))
                             ;(prn :rest-graph  (fg (:rest-rels spec)))
                             (g/find-cycle-starting-with (fg (:first-rels spec))
                                                         (fg (:rest-rels spec))
                                                         scc)))]
             (when cycle
               ; Explain the cycle
               (let [ex (elle/explain-cycle cycle-explainer pair-explainer
                                            cycle)]
                 ;(prn :explanation ex)
                 ; Make sure it passes the filter, if we have one.
                 (if-let [p (:filter-ex spec)]
                   (when (p ex) ex)
                   ex)))))
         ; Strip out missing cycles, or explanations that didn't pass muster
         (remove nil?)
         ; And group them by type
         (group-by :type))))

(defn cycles
  "Takes an options map, including a collection of expected consistency models
  :consistency-models, a set of additional :anomalies, an analyzer function,
  and a history. Analyzes the history and yields the analysis, plus an anomaly
  map like {:G1c [...]}."
  [opts analyzer history]
  (let [; Analyze the history
        {:keys [graph explainer sccs] :as analysis}
        (elle/check- analyzer history)

        ; Find anomalies
        anomalies (cycle-cases graph explainer sccs)]
    ;(prn :cycles)
    ;(pprint anomalies)
    ; Merge our cases into the existing anomalies map.
    (update analysis :anomalies merge anomalies)))

(defn cycles!
  "Like cycles, but writes out files as a side effect. Only writes files for
  relevant anomalies."
  [opts analyzer history]
  (let [analysis (cycles opts analyzer history)
        anomalies (select-keys (:anomalies analysis)
                               (reportable-anomaly-types opts))]
    ; First, text files.
    (doseq [[type cycles] anomalies]
      (when (cycle-types type)
        (elle/write-cycles! (assoc opts
                                   :pair-explainer  (:explainer analysis)
                                   :cycle-explainer cycle-explainer
                                   :filename        (str (name type) ".txt"))
                            cycles)))

    ; Then (in case they break), GraphViz plots.
    (when-let [d (:directory opts)]
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
  ;(prn :anomalies anomalies)
  ;(prn :reportable-anomalies (reportable-anomaly-types opts))
  (let [bad         (select-keys anomalies (prohibited-anomaly-types opts))
        reportable  (select-keys anomalies (reportable-anomaly-types opts))]
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

(defn wr-txns
  "A lazy sequence of write and read transactions over a pool of n numeric
  keys; every write is unique per key. Options:

    :key-count            Number of distinct keys at any point
    :min-txn-length       Minimum number of operations per txn
    :max-txn-length       Maximum number of operations per txn
    :max-writes-per-key   Maximum number of operations per key"
  ([opts]
   (wr-txns opts {:active-keys (vec (range (:key-count opts 2)))}))
  ([opts state]
   (lazy-seq
     (let [min-length           (:min-txn-length opts 1)
           max-length           (:max-txn-length opts 2)
           max-writes-per-key   (:max-writes-per-key opts 32)
           key-count            (:key-count opts 2)
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
                                   k (rand-nth active-keys)
                                   v (when (= f :w) (get state k 1))]
                               (if (and (= :w f)
                                        (< max-writes-per-key v))
                                 ; We've updated this key too many times!
                                 (let [i  (.indexOf active-keys k)
                                       k' (inc (reduce max active-keys))
                                       state' (update state :active-keys
                                                      assoc i k')]
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
