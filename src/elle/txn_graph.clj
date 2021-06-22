(ns elle.txn-graph
  "This structure forms a graph over transactions (completed operations), where
  relationships are sets of dependency types like :ww, :wr, :rw, and :rt."
  (:require [jepsen.txn :as txn]
            [elle [explanation :as expl]
                  [graph :as g]
                  [recovery :as recovery]
                  [version-graph :as vg]]))

(defprotocol TxnGraph
  "A TxnGraph basically combines a Bifurcan graph between completed operations
  with a means of *justifying* the relationships in that graph."

  (graph [_]
         "Returns a Bifurcan DirectedGraph over transactions (completed
         operations).")

  (explain [_ t1 t2]
           "Returns an Explanation of why transaction T1 precedes T2."))

(defn add-ww-edges
  "Takes a txn graph, a recovery, a version graph, and a write mop in an op t1.
  Finds the transactions t2 which wrote the immediately following version, and
  adds t1 -ww-> t2 edges in the transaction graph."
  [txn-graph recovery version-graph t1 [f k v :as mop]]
  ; What version did this write produce?
  (if-let [v (recovery/write->version recovery mop)]
    ; Find following versions
    (let [next-versions (g/out (vg/graph version-graph k) v)
          ; And the txns which wrote them
          t2s (map (comp first (partial recovery/version->write recovery k))
                   next-versions)]
      (g/link-to-all txn-graph t1 t2s :ww))
    ; Shoot, we don't know what version this write produced.
    txn-graph))

(defn add-wr-edge
  "Takes a txn graph, a recovery, a version graph, and a read mop in an op t2.
  Finds the transation t1 which wrote the value this read observed, and adds a
  :wr edge to the txn graph."
  [txn-graph recovery version-graph t2 [f k v]]
  (if-let [[t1 _] (recovery/version->write recovery k v)]
    (g/link txn-graph t1 t2 :wr)
    txn-graph))

(defn add-rw-edges
  "Takes a txn graph, a recovery, a version graph, and a read mop in an op t1.
  Finds the transactions t2 which wrote the immediately following version(s) in
  the version graph, and adds :rw edges from t1 -> t2 to the transaction graph.

  Why is this legal? Imagine we have a record with versions 1 and 2, both of
  which follow version 0, but no relationship between 1 and 2. Assume, WLOG, 0
  < 1 < 2 in the real history--but we don't know this. Can we emit improper
  cycles by having a direct rw edge 0 -rw-> 2, and missing the edges 0-ww->1
  and 1-ww->2, etc?

  The answer is no, GIVEN the types of anomalies we infer. Any cycle which uses
  the inferred edge 0 -rw-> 2 has a corresponding path of the form [0 -rw-> 1,
  1 -ww-> 2], and the same holds true for arbitrary additional 'hidden
  versions' between 0 and 2: each must be connected by a ww edge. We might
  accidentally infer a more conservative cycle--like interpreting a g-single as
  a g2, but missing some ww edges won't cause us to miss a cycle, or interpret
  it as a *worse* cycle."
  [txn-graph recovery version-graph t1 [f k v]]
  ; Find the following versions
  (let [next-versions (g/out (vg/graph version-graph k) v)
        ; And the txns which wrote them
        t2s (map (comp first (partial recovery/version->write recovery k))
                 next-versions)]
    ; Now, generate links
    (g/link-to-all txn-graph t1 t2s :rw)))

(defn add-txn-edges
  "Takes a transaction graph, a recovery, a version graph, and a mop in an op.
  Adds ww, wr, and rw edges to the transaction graph which are inferrable from
  this particular mop."
  [txn-graph recovery version-graph op [f :as mop]]
  (case f
    ; For reads, we infer wr and rw edges into and out of (respectively) this
    ; read version.
    :r (-> txn-graph
           (add-wr-edge  recovery version-graph op mop)
           (add-rw-edges recovery version-graph op mop))
    ; Must be a write. For this, we infer the outbound ww edges--inbound will
    ; be covered by other ops.
    (-> txn-graph
        (add-ww-edges recovery version-graph op mop))))

(defn version-graph->txn-graph
  "Takes an analysis and yields a TxnGraph from it, using that analysis'
  :history, :recovery, and :version-graph."
  [analysis]
  (let [r  (:recovery analysis)
        vg (:version-graph analysis)
        tg (g/forked
             (txn/reduce-mops (fn [g op mop]
                                (add-txn-edges g r vg op mop))
                              (g/linear (g/digraph))
                              ; For our purposes, we only care about ok and
                              ; info ops; no need to infer dependencies over
                              ; failed operations.
                              (filter (comp #{:ok :info} :type)
                                      (:history analysis))))]
    (reify TxnGraph
      (graph [_] tg)

      (explain [_ t1 t2]
        ; What kind of edge do we have?
        (when-let [edge (g/maybe-edge tg t1 t2)]
          (cond
            (edge :ww) (reify expl/Explanation
                         (->data [_] :ww)
                         (->text [_ ctx] "ww"))
            (edge :wr) (reify expl/Explanation
                         (->data [_] :wr)
                         (->text [_ ctx] "wr"))
            (edge :rw) (reify expl/Explanation
                         (->data [_] :rw)
                         (->text [_ ctx] "rw"))
            true       (throw (RuntimeException.
                                (str "Don't know how to explain edge of type "
                                     (pr-str edge))))))))))

(defn add-txn-graph
  "Takes an analysis with a history, recovery, and version graph, and infers a txn graph for it."
  [analysis]
  (assoc analysis :txn-graph (version-graph->txn-graph analysis)))
