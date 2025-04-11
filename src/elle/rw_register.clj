(ns elle.rw-register
  "A test which looks for cycles in write/read transactionss over registers.
  Writes are assumed to be unique, but this is the only constraint.

  Operations are of two forms:

    [:r x 1] denotes a read of x observing the value 1.
    [:w x 2] denotes a write of x, settings its value to 2.

  Unlike the append test, we cannot recover information about the version order
  by comparing versions directly. The only dependency we can directly infer
  between transactions is:

    1. T1 writes x_i, and T2 reads x_i: we know T1 < T2.

  However, this is not the only information we have access to. We can infer
  partial version orders *within* a transaction. When x_i =/= x_j...

    2rr. T1 reads x_i,  then reads  x_j: we know x_i < x_j.
    2rw. T1 reads x_i,  then writes x_j: we know x_i < x_j.
    2wr. T1 writes x_i, then reads  x_j: we know x_i < x_j.
    2ww. T1 writes x_i, then writes x_j: we know x_i < x_j.

  In serializable systems, only 2ww and 2rw should arise. 2rr is obviously a
  non-repeatable read. 2wr suggests dirty write, I think. Both 2rr and 2wr are
  violations of internal consistency.

  We can use these dependencies to infer additional transaction edges, wherever
  the version graph is available.

  What's more: given an ordering relationship between two transactions, we can,
  by assuming serializability, infer *additional version constraints*. If T1 <
  T2, and T1 reads or writes x_i, and T2 reads or writes x_j, we can infer x_i
  < x_j. This expands our version graph.

  We can alternate between expanding the transaction graph and expanding the
  version graph until we reach a fixed point. This isn't implemented yet."
  (:require [bifurcan-clj [core :as b]
                          [graph :as bg]
                          [set :as bs]]
            [clojure.core.reducers :as r]
            [clojure [set :as set]
                     [pprint :refer [pprint]]]
            [clojure.tools.logging :refer [info warn]]
            [dom-top.core :refer [loopr]]
            [elle [core :as elle]
                  [txn :as ct]
                  [graph :as g]
                  [rels :refer [ww wr rw]]
                  [util :as util :refer [empty->nil
                                         map-vals
                                         index-of
                                         op-memoize]]]
            [jepsen [history :as h]
                    [txn :as txn :refer [reduce-mops]]]
            [jepsen.history.fold :refer [loopf]]
						[jepsen.txn.micro-op :as mop]
            [tesser.core :as t])
  (:import (io.lacuna.bifurcan DirectedGraph
                               IEdge
                               IEntry
                               IMap
                               ISet
                               Graphs
                               LinearMap
                               LinearSet
                               Map
                               Set)
           (java.util.function BinaryOperator
                               BiFunction)
           (jepsen.history Op)))

(defn op-internal-case
  "Given an op, returns a map describing internal consistency violations, or
  nil otherwise. Our maps are:

      {:op        The operation which went wrong
       :mop       The micro-operation which went wrong
       :expected  The state we expected to observe.}"
  [op]
  ; We maintain a map of keys to expected states.
  (->> (:value op)
       (reduce (fn [[state error] [f k v :as mop]]
                 (case f
                   :w [(assoc! state k v) error]
                   :r (let [s (get state k)]
                        (if (and s (not= s v))
                          ; Not equal!
                          (reduced [state
                                    {:op       op
                                     :mop      mop
                                     :expected s}])
                          ; OK! Either a match, or our first time seeing k.
                          [(assoc! state k v) error]))))
               [(transient {}) nil])
       second))

(defn internal-cases
  "Given a history, finds operations which exhibit internal consistency
  violations: e.g. some read [:r k v] in the transaction fails to observe a v
  consistent with that transaction's previous write to k."
  [history]
  (ct/ok-keep op-internal-case history))

(defn g1a-cases
  "G1a, or aborted read, is an anomaly where a transaction reads data from an
  aborted transaction. For us, an aborted transaction is one that we know
  failed. Info transactions may abort, but if they do, the only way for us to
  TELL they aborted is by observing their writes, and if we observe their
  writes, we can't conclude they aborted, sooooo...

  This function takes a history (which should include :fail events!), and
  produces a sequence of error objects, each representing an operation which
  read state written by a failed transaction."
  [history]
  ; Build a map of keys to maps of failed elements to the ops that appended
  ; them.
  (let [failed (ct/failed-write-indices #{:w} history)]
    ; Look for ok ops with a read mop of a failed append
    (->> history
         h/oks
         ct/op-mops
         (keep (fn [[^Op op [f k v :as mop]]]
                 (when (= :r f)
                   (when-let [writer-index (get-in failed [k v])]
                     {:op        op
                      :mop       mop
                      :writer    (h/get-index history writer-index)}))))
         seq)))

(defn g1b-cases
  "G1b, or intermediate read, is an anomaly where a transaction T2 reads a
  state for key k that was written by another transaction, T1, that was not
  T1's final update to k.

  This function takes a history (which should include :fail events!), and
  produces a sequence of error objects, each representing a read of an
  intermediate state."
  [history]
  ; Build a map of keys to maps of intermediate elements to the ops that wrote
  ; them
  (let [im (ct/intermediate-write-indices #{:w} history)]
    ; Look for ok ops with a read mop of an intermediate append
    (->> history
         h/oks
         ct/op-mops
         (keep (fn [[^Op op [f k v :as mop]]]
                 (when (= :r f)
									 ; We've got an illegal read if value came from an
				           ; intermediate append.
                   (when-let [writer-index (get-in im [k v])]
                     ; Internal reads are OK!
                     (when (not= (.index op) writer-index)
                       {:op       op
                        :mop      mop
                        :writer   (h/get-index history writer-index)})))))
         seq)))

(defn ext-index
  "Given a function that takes a txn and returns a map of external keys to
  written values for that txn, and a history, computes a map like {k {v [op1,
  op2, ...]}}, where k is a key, v is a particular value for that key, and op1,
  op2, ... are operations which externally wrote k=v.

  Right now we index only :ok ops. Later we should do :infos too, but we need
  to think carefully about how to interpret the meaning of their nil reads.

  TODO: we fail to index external writes of type :info. That's bad."
  [ext-fn history]
  (->> history
       h/oks
       (reduce (fn [idx op]
                 (reduce (fn [idx [k v]]
                           (update-in idx [k v] conj op))
                         idx
                         (ext-fn (:value op))))
               {})))

(defn initial-state-version-graphs
  "We assume the initial state of every key is `nil`; every version trivially
  comes after it. We take a history and return a map of keys to version graphs
  encoding this relationship."
  [history]
  (reduce (fn op [vgs op]
            (if (or (h/invoke? op)
                    (h/fail?   op))
              vgs ; No sense in inferring anything here
              (let [txn (:value op)
                    writes (txn/ext-writes txn)
                    ; For reads, we only know their values when the op is OK.
                    reads  (when (h/ok? op) (txn/ext-reads txn))]
                (->> (concat writes reads)
                     ; OK, now iterate over kv maps, building up our version
                     ; graph.
                     (reduce (fn kv [vgs [k v]]
                               (if (nil? v)
                                 ; Don't make a self-edge!
                                 vgs
                                 (let [vg (get vgs k (g/digraph))]
                                   (assoc vgs k (g/link vg nil v)))))
                               vgs)))))
          {}
          history))

(defn wfr-version-graphs
  "If we assume that within a transaction, writes follow reads, then we can
  infer the version order wherever a transaction performs an external read of
  some key x, and an external write of x as well."
  [history]
  (->> history
       h/oks ; Since we need BOTH reads and writes, this only works with ok ops.
       (reduce
         (fn [vgs op]
           (let [txn    (:value op)
                 reads  (txn/ext-reads txn)
                 writes (txn/ext-writes txn)]
             (reduce (fn [vgs [k v]]
                       (if (not (nil? v)) ; nils handled separately
                         (if-let [v' (get writes k)]
                           (let [vg (get vgs k (g/digraph))]
                             (assoc vgs k (g/link vg v v')))
                           vgs)
                         vgs))
                     vgs
                     reads)))
         {})))

(defn ext-keys
  "Given an operation, returns the set of keys we know it interacted with via
  an external read or write."
  [^Op op]
  (when (or (h/ok? op) (h/info? op))
    (let [txn    (.value op)
          ; Can't infer crashed reads!
          reads  (when (h/ok? op)
                   (txn/ext-reads txn))
          ; We can infer crashed writes though!
          writes (txn/ext-writes txn)]
      (keys (merge reads writes)))))

;(defn kg-str
;  "Prints a key graph to a string. You'll want this to optimize
;  downstream-ops-by-ext-key."
;  [kg]
;  (-> kg
;       g/->clj
;       (update-keys :index)
;       (update-vals (fn [k->ops]
;                      (update-vals k->ops
;                                   (fn [ops]
;                                     (sort (map :index ops))))))
;       pprint
;       with-out-str))

(defn downstream-ops-by-ext-key-transitive!
  "Takes a downstream map and adds transitive dependencies to it. Uses a
  partial ext-key graph (a map of ops to keys to downstream txns), a set of ext
  keys for the op under consideration, and a transitive downstream map taken
  from the key graph for this op.

  We use the downstream information from the key graph kg, and override it with
  whatever is in the node itself. Returns a new downstream LinearMap."
  [^LinearMap downstream, ^IMap kg, ^ISet ext-keys,
   ^LinearMap transitive-downstream]
  (reduce (fn [^IMap downstream ^IEntry k->bs']
            (let [k   (.key k->bs')
                  bs' ^ISet (.value k->bs')]
              ;(prn :trans k (map :index bs'))
              (if (.contains ext-keys k)
                ; We'll handle this in downstream-ops-by-ext-key-local!
                downstream
                ; Use transitive bs
                (do ;(prn :trans-union
                    ;     (sort (map :index bs))
                    ;     (sort (map :index bs')))
                    (.put downstream k bs' g/union-bset)))))
          downstream
          transitive-downstream))

(defn downstream-ops-by-ext-key-local!
  "Enlarges a downstream map with local dependencies. Takes a downstream map, a
  collection of ext keys, and an operation. Returns the downstream map with op
  added for each key in ext-keys."
  [downstream ext-keys op]
  (reduce (fn [^IMap downstream k]
            ; (prn :local k :op (:index op))
            (let [bs (.get downstream k (LinearSet.))]
              (.put downstream k (bs/add bs op))))
          downstream
          ext-keys))

(defn downstream-ops-by-ext-key-explore
  "Takes

  - `kg`, a (perhaps partial) ext-key graph
  - `out`, a set of ops downstream from some op

  Returns a pair of a new downstream map (a map of k -> #{op1 op2 ...}), and a
  vector of unexplored ops we need to look at before we can check this one."
  [^IMap kg out]
  (loopr [downstream  (LinearMap.) ; map of k => #{op1, op2}
          unexplored  []]          ; list of ops to explore
          [op out]
          (let [ext-keys (ext-keys op)
                ext-keys (if (nil? ext-keys)
                           (Set/empty)
                           (Set/from ^Iterable ext-keys))]
            ;(prn :checking-descendent n)
            ; Transitive k->vs
            (if-let [trans-downstream (.get kg op nil)]
              (if (< 0 (count unexplored))
                ; There are unexplored nodes in this pass; we're not actually
                ; going to use our downstream results here and there's no sense
                ; in computing them.
                (recur downstream unexplored)
                ; Check this next node. We use the downstream
                ; information from kg, and override it with whatever's
                ; in the node itself.
                (recur (-> downstream
                           (downstream-ops-by-ext-key-transitive!
                             kg ext-keys trans-downstream)
                           ; OK, and now local deps!
                           (downstream-ops-by-ext-key-local!
                             ext-keys op))
                       unexplored))
              ; Huh, this node hasn't been explored yet. If this happens we
              ; can't use the downstream results we've built so far.
              (do ;(prn :unexplored!)
                  (recur downstream (conj unexplored op)))))))

(defn downstream-ops-by-ext-key
  "Takes a transaction graph, a (perhaps partial) ext-key graph, a set of keys
  to ignore, and a stack of ops to explore. Returns a more complete key graph
  which contains an entry for every op in the ops stack as well as all their
  downstream dependencies, transitively."
  [g ^IMap kg ops]
  (if (empty? ops)
    ; Nowhere else to explore!
    kg
    (let [op (peek ops)]
      ; (prn :op (.index op) :with (dec (count ops)) :more)
      (if (.contains kg op)
        ; Well, we've already explored this op; no need to go further!
        (do ;(prn :hit!)
            (recur g kg (pop ops)))
        (let [out (g/out g op)]
          (if (= 0 (.size out))
            ; Nobody downstream of us; all we need is an empty map.
            (recur g (.put kg op Map/EMPTY) (pop ops))

            ; OK, so we've got downstream nodes. We need all of them to be
            ; explored.
            (let [[downstream unexplored]
                  (downstream-ops-by-ext-key-explore kg out)]
              ;(prn :downstream (.size downstream)
              ;     :unexplored (count unexplored))
              (if (< 0 (count unexplored))
                ; If we have any unexplored, move on to them; we'll come
                ; back to this later.
                (do ;(prn :unexplored (count unexplored))
                    (recur g kg (into ops unexplored)))

                ; Good, we explored everything; this means our results are
                ; total. Update kg with our findings for this node and
                ; move on to the next op in the stack.
                (do ;(prn :complete (.index op))
                    (recur g
                           (.put kg op (b/forked downstream))
                           (pop ops)))))))))))

(defn ^IMap ext-key-graph
  "Takes a transaction graph g, and yields an external key graph: a map of ops
  a to keys k to downstream ops b, such that if a externally interacted with k,
  b did too, and b follows a in g.

  This graph lets us ask \"what were the next transactions to interact with a
  given key?\". We use this to extract *version* orders from a transaction
  graph."
  [g]
  ; In general, finding the set of downstream nodes could require traversing
  ; the entire graph in O(n) time; this is n^2. To avoid this, we employ two
  ; tricks:
  ;
  ; 1. Memoize
  ; 2. Under the assumption that our graph *roughly* points forward in time,
  ;    we traverse ops in reverse time (:index) order. This gives our memoized
  ;    data structure the maximum chance to work.
  (->> (bg/vertices g)
       (sort-by :index)
       reverse
       ; Build up the key graph
       (reduce (fn red [kg op]
                 ;(println "\n")
                 ;(prn :ext-key-graph (:index op))
                 ;(print :kg (kg-str kg))
                 (downstream-ops-by-ext-key g kg [op]))
               (LinearMap.))
       b/forked))

(defn transaction-graph->version-graphs
  "Takes a graph of transactions (operations), and yields a map of keys to
  graphs of version relationships we can infer from those transactions,
  ASSUMING THAT IF T1 < T2, x1 < x2, FOR ALL x1 in T1 and x2 in T2.

  For instance, if a system is per-key sequential, you could feed this a
  process order and use it to derive a version order, since each process must
  observe subsequent states of the system. Likewise, if a system is per-key
  linearizable, you can use a realtime order to infer version relationships.

  Assume we have a transaction T1 which interacts with key k at value v1. We
  write every other transation as T2, T3, etc if it interacts with k, and t2,
  t3, etc if it does not. We write the first version of k interacted with by T2
  as v2, T3 as v3, and so on.

    T1─T2

  If T2 interacts with k at v2, we can infer v1 < v2. Great.

    T1─t2─T3

  Since t2 does not interact with k, this doesn't help us--but T3 *does*, so we
  can infer v1 < v3.

       ┌T2
    T1─┤
       └T3

  When a dependency chain splits, we have (at most) n dependencies we can
  infer: x1 < x2, x1 < x3.

       ┌T2
    T1─┤
       └t3─T4

  Clearly we can infer x1 < x2--and we need search no further, since T2's
  dependencies will cover the rest of the chain transitively. We must search
  past t3 however, to T4, to infer x1 < x4.

  In general, then, our program is to search the downstream transaction graph,
  stopping and recording a dependency whenever we encounter a transaction which
  interacted with k.

  This search is, of course, n^2: the first transaction might have to search
  every remaining transaction, the second the same chain, and so forth. This is
  *especially* likely to explode pathologically because we probably abandon
  keys at some point in the history, leaving a long stretch of transactions to
  fruitlessly explore.

  To avoid this problem, we *compress* the transaction graph to remove
  transactions which do not involve k, in linear time. We simply find a
  transaction t2 which does not involve k, take all of t2's predecessors, all
  of t2's successors, and link them all directly together, finally deleting t2.
  This process is linear in the number of keys, transactions, and edges.

  With this process complete, we can transform the reduced transaction graph
  directly to a version graph: the final value x1 in T1 directly precedes the
  initial values x2, x3, ... in T2, T3, ... following T1."
  [txn-graph]
  ; These seem expensive according to Yourkit, but I'm not actually seeing
  ; a change in runtime memoizing em. Not sure what's up.
  (let [ext-reads  (op-memoize (comp txn/ext-reads :value))
        ext-writes (op-memoize (comp txn/ext-writes :value))
        ; Build up a map of t1 -> k -> #{t2 t3 ...}
        ext-key-graph (ext-key-graph txn-graph)
        ; This is really expensive, so we parallelize
        procs (.availableProcessors (Runtime/getRuntime))
        ext-key-graph-chunks (.split ext-key-graph (* 4 procs))
        ; A fold which turns chunks of the key graph into version orders, then
        ; merges those order graphs together.
        fold
        (loopf {:name :txn-graph->version-graph}
               ; Reducer
               ([key-graphs (.linear Map/EMPTY)] ; k -> value-digraph
                [^IEntry pair] ; op -> m, where m is k -> op-set
                ; We're trying to relate *external* values forward. There are
                ; two possible external values per key per txn: the first
                ; read, and the final write. WFR (which we check separately)
                ; lets us infer the relationship between the first read and
                ; final write *in* the transaction, so what we want to infer
                ; here is the relationship between the *final* external value.
                ; If internal consistency holds (which we check separately),
                ; then the final external value must be the final write, or if
                ; that's not present, the first read.
                (let [a            ^Op (.key pair)
                      downstream   (.value pair)
                      ta           (.value a)
                      ext-writes-a (ext-writes a)
                      ext-reads-a  (ext-reads  a)]
                  ; For each key and set of downstream txns bs...
                  (loopr [^IMap key-graphs' key-graphs]
                         [^IEntry pair downstream :via :iterator]
                         (let [k  (.key pair)
                               bs (.value pair)
                               kg (.get key-graphs' k (.linear (g/digraph)))
                               ; Figure out what version of k we last
                               ; interacted with
                               v1 (condp = (:type a)
                                    :ok   (or (get ext-writes-a k)
                                              (get ext-reads-a  k))
                                    :info (get ext-writes-a k ::none)
                                    :fail ::none)]
                           (if (= ::none v1)
                             ; Nothing doing
                             (recur (.put key-graphs' k kg))

                             ; Now, we want to relate this version v1 to the
                             ; first external value of k for b, which will be
                             ; either the external read, or if that's missing,
                             ; the external write.
                             (loopr [^ISet v2s (.linear Set/EMPTY)]
                                    ; As a LinearSet, bs is faster with iterator
                                    [^Op b bs :via :iterator]
                                    (let [v (condp identical? (.type b)
                                              :ok (or (get (ext-reads b) k)
                                                      (get (ext-writes b) k))
                                              :info (get (ext-writes b) k
                                                         ::none)
                                              ::none)]
                                      (if (or (identical? ::none v)
                                              ; Don't generate self-edges
                                              (= v1 v))
                                        (recur v2s)
                                        (recur (.add v2s v))))
                                    ; Done building v2s; link v1 to each
                                    (recur
                                      (if (= 0 (.size v2s))
                                        key-graphs'
                                        (.put key-graphs' k
                                              (g/link-to-all-iter
                                                kg v1 v2s)))))))
                         (recur key-graphs'))))
               ; Combiner
               ([^IMap kg1 (.linear Map/EMPTY)]
                [^IMap kg2]
                (recur
                  (.merge kg1 kg2
                          (reify BinaryOperator
                            (apply [_ g1 g2]
                              (.merge ^DirectedGraph g1, ^DirectedGraph g2
                                      g/merge-last-write-wins)))))
                ; Seal off transients, convert back to Clojure map
                (loopr [kg (transient {})]
                       [^IEntry pair kg1 :via :iterator]
                       (recur (assoc! kg
                                      (.key pair)
                                      (.forked ^DirectedGraph (.value pair))))
                       (persistent! kg))))]
    ; Run fold
    (t/tesser ext-key-graph-chunks (t/fold fold))))

(defn cyclic-version-cases
  "Given a map of version graphs, returns a sequence (or nil) of cycles in that
  graph."
  [version-graphs]
  (empty->nil
    (reduce (fn [cases [k version-graph]]
              (let [sccs (g/strongly-connected-components version-graph)
                    ; It's nice, for test stability, to sort these somehow, but
                    ; if we get something polymorphic don't worry too much
                    ; about it.
                    sccs (try (sort-by (partial reduce min) sccs)
                              (catch java.lang.NullPointerException e
                                (sort-by count sccs))
                              (catch java.lang.ClassCastException e
                                (sort-by count sccs)))]
                (->> sccs
                     (map (fn [scc]
                            {:key k
                             :scc scc}))
                     (into cases))))
            []
            version-graphs)))

(defn version-graphs
  "We build version graphs by combining information from many sources. This
  function takes options (as for ww+rw-graph) and a history, and yields
  {:anomalies [...], :sources [...], :graphs version-graphs}"
  [opts history]
  (loop [analyzers (cond-> [{:name    :initial-state
                             :grapher initial-state-version-graphs}]

                     (:wfr-keys? opts)
                     (conj {:name     :wfr-keys
                            :grapher  wfr-version-graphs})

                     (:sequential-keys? opts)
                     (conj {:name    :sequential-keys
                            :grapher (comp transaction-graph->version-graphs
                                           :graph
                                           elle/process-graph)})

                     (:linearizable-keys? opts)
                     (conj {:name    :linearizable-keys
                            :grapher (comp transaction-graph->version-graphs
                                           :graph
                                           elle/realtime-graph)}))
         sources       []
         graphs        {}
         cycles        []]
    (if (seq analyzers)
      (let [{:keys [name grapher]} (first analyzers)
            ; Apply this grapher fn to the history, merge it into the graphs,
            ; and record any cyclic version cases we might find, along with the
            ; analyzer names that contributed to that cycle.
            ;
            ; TODO: This is basically the txn graph explainer cycle search
            ; problem all over again, just over versions. I'm writing a hack
            ; here because the paper deadline is coming up RIGHT NOW, but later
            ; we should come back and redo this so we can *justify* exactly why
            ; we inferred a version order.
            sources'  (conj sources name)
            graph     (grapher history)
            graphs'   (merge-with g/digraph-union graphs graph)]
        (if-let [cs (->> (cyclic-version-cases graphs')
                         (map #(assoc % :sources sources'))
                         seq)]
          ; Huh. Cycles in this version of the dependency graph. Let's skip
          ; over it in the graph, but note the cycle anomalies.
          (recur (next analyzers) sources graphs (into cycles cs))
          ; No cycles in this combined graph; let's use it!
          (recur (next analyzers) sources' graphs' cycles)))
      ; Done!
      {:anomalies (when (seq cycles) {:cyclic-versions cycles})
       :sources   sources
       :graphs    graphs})))

(defn version-graphs->transaction-graph
  "Takes a history and a map of keys to version graphs, and infers a graph of
  dependencies between operations in that history by using the (likely partial)
  version graph information.

  We do this by taking every key k, and for k, every edge v1 -> v2 in the
  version graph, and for every T1 which finally interacted with v1, and every
  T2 which initially interacted with T2, emitting an edge in the transaction
  graph. We tag our edges :ww and :rw as appropriate. :wr edges we can detect
  directly; we don't need the version graph to do that. Any :rr edge SHOULD
  (assuming values just don't pop out of nowhere, internal consistency holds,
  etc) manifest as a combination of :rw, :ww, and :wr edges; we don't gain
  anything by emitting them here."
  [history version-graphs]
  (let [ext-read-index  (ext-index txn/ext-reads  history)
        ext-write-index (ext-index txn/ext-writes history)]
    (loopr [g (b/linear (g/op-digraph))]
           [[k version-graph] version-graphs
            ^IEdge edge (bg/edges version-graph)]
           (let [v1        (.from edge)
                 v2        (.to edge)
                 k-writes  (get ext-write-index k)
                 k-reads   (get ext-read-index k)
                 v1-reads  (get k-reads v1)
                 v1-writes (get k-writes v1)
                 v2-writes (get k-writes v2)
                 all-vals  (set (concat v1-reads v1-writes v2-writes))]
             (recur (-> g
                        (g/link-all-to-all v1-writes v2-writes ww)
                        (g/link-all-to-all v1-reads v2-writes rw)
                        (g/remove-self-edges all-vals))))
           (b/forked g))))

(defn explain-op-deps
  "Given version graphs, a function extracting a map of keys to values from op
  A, and also from op B, and a pair of operations A and B, returns a map (or
  nil) explaining why A precedes B.

  We look for a key on which A interacted with version v, and B interacted with
  v', and v->v' in the version graph."
  [version-graphs ext-a a ext-b b]
  (let [a-kvs (ext-a (:value a))
        b-kvs (ext-b (:value b))]
    ; Look for a key where a's value precedes b's!
    (first
      (keep (fn [[k a-value]]
              (when-let [version-graph (get version-graphs k)]
                (when-let [b-value (get b-kvs k)]
                  (when (.contains ^ISet (g/out version-graph a-value)
                                   b-value)
                    {:key     k
                     :value   a-value
                     :value'  b-value}))))
            a-kvs))))

(defrecord WWExplainer [version-graphs]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (when-let [{:keys [key value value'] :as e}
               (explain-op-deps
                 version-graphs txn/ext-writes a txn/ext-writes b)]
      (assoc e
             :type :ww
             :a-mop-index (index-of (:value a) [:w key value])
             :b-mop-index (index-of (:value b) [:w key value']))))

  (render-explanation [_ {:keys [key value value'] :as m} a-name b-name]
    (str a-name " set key " (pr-str key) " to " (pr-str value) ", and "
         b-name " set it to " (pr-str value')
         ", which came later in the version order")))

(defrecord RWExplainer [version-graphs]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (when-let [{:keys [key value value'] :as e}
               (explain-op-deps version-graphs
                                txn/ext-reads a txn/ext-writes b)]
      (assoc e
             :type :rw
             :a-mop-index (index-of (:value a) [:r key value])
             :b-mop-index (index-of (:value b) [:w key value']))))

  (render-explanation [_ {:keys [key value value'] :as m} a-name b-name]
    (str a-name " read key " (pr-str key) " = " (pr-str value) ", and "
         b-name " set it to " (pr-str value')
         ", which came later in the version order")))

(defn ww+rw-graph
  "Given options and a history where the ops are txns, constructs a graph and
  explainer over transactions with :rw and :ww edges, based on an inferred
  partial version order.

  We infer the version order based on options:

    :linearizable-keys?  Uses realtime order
    :sequential-keys?    Uses process order
    :wfr-keys?           Assumes writes follow reads in a txn

  In addition, we infer a dependency edge from nil to every non-nil value."
  [opts history]
  (let [{:keys [anomalies sources graphs]} (version-graphs opts history)
        tg  (version-graphs->transaction-graph history graphs)]
    ; We might have found anomalies when computing the version graph
    {:anomalies anomalies
     :graph     tg
     :explainer (elle/->CombinedExplainer [(WWExplainer. graphs)
                                           (RWExplainer. graphs)])}))

(defrecord WRExplainer []
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (let [writes (txn/ext-writes (:value a))
          reads  (txn/ext-reads  (:value b))]
      (reduce (fn [_ [k v]]
                (when (and (contains? reads k)
                           (= v (get reads k)))
                  (reduced
                    {:type  :wr
                     :key   k
                     :value v
                     :a-mop-index (index-of (:value a) [:w k v])
                     :b-mop-index (index-of (:value b) [:r k v])})))
              nil
              writes)))

  (render-explanation [_ {:keys [key value]} a-name b-name]
    (str a-name " wrote " (pr-str key) " = " (pr-str value)
         ", which was read by " b-name)))

(defn wr-graph
  "Given a history where ops are txns (e.g. [[:r :x 2] [:w :y 3]]), constructs
  an order over txns based on the external writes and reads of key k: any txn
  that reads value v must come after the txn that wrote v."
  [history]
  (let [ext-writes (ext-index txn/ext-writes history)
        ext-reads  (ext-index txn/ext-reads  history)]
    ; Take all reads and relate them to prior writes.
    {:graph
     (b/forked
       (reduce (fn [graph [k values->reads]]
                 ; OK, we've got a map of values to ops that read those values
                 (reduce (fn [graph [v reads]]
                           ; Find ops that set k=v
                           (let [writes (-> ext-writes (get k) (get v))]
                             (case (count writes)
                               ; Huh. We read a value that came out of nowhere.
                               ; This is probably an initial state. Later on
                               ; we could do something interesting here, like
                               ; enforcing that there's only one of these
                               ; values and they have to precede all writes.
                               0 graph

                               ; OK, in this case, we've got exactly one
                               ; txn that wrote this value, which is good!
                               ; We can generate dependency edges here!
                               1 (g/link-to-all graph (first writes) reads wr)

                               ; But if there's more than one, we can't do this
                               ; sort of cycle analysis because there are
                               ; multiple alternative orders. Technically, it'd
                               ; be legal to ignore these, but I think it's
                               ; likely the case that users will want a big
                               ; flashing warning if they mess this up.
                               (assert (< (count writes) 2)
                                       (throw (IllegalArgumentException.
                                                (str "Key " (pr-str k)
                                                     " had value " (pr-str v)
                                                     " written by more than one op: "
                                                     (pr-str writes))))))))
                         graph
                         values->reads))
               (b/linear (g/op-digraph))
               ext-reads))
     :explainer (WRExplainer.)}))

(defn graph
  "Given options and a history, computes a {:graph g, :explainer e} map of
  dependencies. We combine several pieces:

    1. A wr-dependency graph, which we obtain by directly comparing writes and
       reads.

    2. Additional graphs, as given by (:additional-graphs opts).

    3. ww and rw dependencies, as derived from a version order, which we derive
       on the basis of...

       a. nil precedes *every* read value

       b. If either :linearizable-keys? or :sequential-keys? is passed, we
          assume individual keys are linearizable/sequentially consistent, and
          use that to infer (partial) version graphs from either the realtime
          or process order, respectively.

  The graph we return combines all this information.

  TODO: maybe use writes-follow-reads(?) to infer more versions from wr deps?"
  [opts history]
  (let [; Build our combined analyzers
        analyzers (into [wr-graph (partial ww+rw-graph opts)]
                        (ct/additional-graphs opts))
        analyzer (apply elle/combine analyzers)]
    ; And go!
    (analyzer history)))

(defn check
  "Full checker for write-read registers. Options are:

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

    :cycle-search-timeout   How many milliseconds are we willing to search a
                            single SCC for a cycle?

    :sequential-keys?       Assume that each key is independently sequentially
                            consistent, and use each processes' transaction
                            order to derive a version order.

    :linearizable-keys?     Assume that each key is independently linearizable,
                            and use the realtime process order to derive a
                            version order.

    :wfr-keys?              Assume that within each transaction, writes follow
                            reads, and use that to infer a version order.

    :directory              Where to output files, if desired. (default nil)

    :plot-format            Either :png or :svg (default :svg)

    :plot-timeout           How many milliseconds will we wait to render a SCC
                            plot?

    :max-plot-bytes         Maximum size of a cycle graph (in bytes of DOT)
                            which we're willing to try and render.
"
  ([history]
   (check {} history))
  ([opts history]
   (let [history      (h/client-ops history)
         type-sanity  (h/task history type-sanity []
                              (ct/assert-type-sanity history))
         g1a          (h/task history g1a [] (g1a-cases history))
         g1b          (h/task history g1b [] (g1b-cases history))
         internal     (h/task history internal [] (internal-cases history))
         lost-update  (h/task history lost-update []
                              (ct/lost-update-cases #{:w} history))
         cycles       (:anomalies (ct/cycles! opts (partial graph opts)
                                              history))
         _            @type-sanity ; Will throw if problems
         ; Build up anomaly map
         anomalies (cond-> cycles
                     @internal     (assoc :internal @internal)
                     @g1a          (assoc :G1a @g1a)
                     @g1b          (assoc :G1b @g1b)
                     @lost-update  (assoc :lost-update @lost-update))]
     (ct/result-map opts anomalies))))

(defn gen
  "See elle.txn/wr-txns for options"
  ([] (gen {}))
  ([opts]
   (ct/gen (ct/wr-txns opts))))
