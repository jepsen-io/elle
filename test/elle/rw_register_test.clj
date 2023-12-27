(ns elle.rw-register-test
  (:refer-clojure :exclude [test])
  (:require [clojure.pprint :refer [pprint]]
            [dom-top.core :refer [loopr real-pmap]]
						[elle [core :as elle]
                  [graph :as g]
                  [rw-register :refer :all]
                  [util :refer [map-vals]]]
            [jepsen [history :as h]
                    [txn :as txn]]
            [clojure.test :refer :all]
            [slingshot.slingshot :refer [try+ throw+]]))

(defn op
  "Generates an operation from a string language like so:

  wx1       set x = 1
  ry1       read y = 1
  wx1wx2    set x=1, x=2"
  ([string]
   (let [[txn mop] (reduce (fn [[txn [f k v :as mop]] c]
                             (case c
                               \w [(conj txn mop) [:w]]
                               \r [(conj txn mop) [:r]]
                               \x [txn (conj mop :x)]
                               \y [txn (conj mop :y)]
                               \z [txn (conj mop :z)]
                               (let [e (if (= \_ c)
                                         nil
                                         (Long/parseLong (str c)))]
                                 [txn [f k e]])))
                           [[] nil]
                           string)
         txn (-> txn
                 (subvec 1)
                 (conj mop))]
     {:process 0, :type :ok, :value txn}))
  ([process type string]
   (assoc (op string) :process process :type type)))

(defn fail
  "Fails an op."
  [op]
  (assoc op :type :fail))

(defn pair
  "Takes a completed op and returns an [invocation, completion] pair."
  [completion]
  [(-> completion
       (assoc :type :invoke)
       (update :value (partial map (fn [[f k v :as mop]]
                                        (if (= :r f)
                                          [f k nil]
                                          mop)))))
   completion])

(deftest op-test
  (is (= {:process 0, :type :ok, :value [[:w :x 1] [:r :x 2]]}
         (op "wx1rx2"))))

(deftest ext-index-test
  (testing "empty"
    (is (= {} (ext-index txn/ext-writes (h/history [])))))
  (testing "writes"
    (let [[w1 w2 :as h]
          (h/history
            [{:process 0, :type :ok, :value [[:w :x 1] [:w :y 3] [:w :x 2]]}
             {:process 1, :type :ok, :value [[:w :y 3] [:w :x 4]]}])]
      (is (= {:x {2 [w1], 4 [w2]}
              :y {3 [w2 w1]}}
             (ext-index txn/ext-writes h))))))

(deftest internal-cases-test
  (testing "empty"
    (is (= nil (internal-cases (h/history [])))))

  (testing "good"
    (is (= nil (internal-cases (h/history [(op "ry2wx2rx2wx1rx1")])))))

  (testing "stale"
    (let [[stale :as h] (h/history [(op "rx1wx2rx1")])]
      (is (= [{:op stale, :mop [:r :x 1], :expected 2}]
             (internal-cases h))))))

(deftest g1a-cases-test
  (testing "empty"
    (is (= nil (g1a-cases (h/history [])))))

  (testing "good"
    (is (= nil (g1a-cases (h/history [(op "wx1")
                                      (op "rx1")])))))

  (testing "bad"
    (let [[r w :as h] (h/history [(op "rx2") (fail (op "wx2"))])]
      (is (= [{:op r, :writer, w :mop [:r :x 2]}]
             (g1a-cases h))))))

(deftest g1b-cases-test
  (testing "empty"
    (is (= nil (g1b-cases (h/history [])))))

  (testing "good"
    (is (= nil (g1b-cases (h/history [(op "wx1wx2")
                                      (op "rx_rx2")])))))

  (testing "bad"
    (let [[r w :as h] (h/history [(op "rx2")
                                  (op "wx2wx1")])]
      (is (= [{:op r, :writer, w :mop [:r :x 2]}]
             (g1b-cases h))))))

(deftest wr-graph-test
  ; helper fns for constructing histories
  (let [pair (fn [txn] [{:process 0, :type :invoke, :f :txn, :value txn}
                        {:process 0, :type :ok,     :f :txn, :value txn}])
        check (fn [& txns]
                (let [h (h/history (mapcat pair txns))]
                  (elle/check {:analyzer wr-graph} h)))]
    (testing "empty history"
      (is (= {:valid? true, :scc-count 0, :cycles []}
             (check []))))
    (testing "write and read"
      (is (= {:valid? true, :scc-count 0, :cycles []}
             (check [[:w :x 0]]
                    [[:w :x 0]]))))
    (testing "chain on one register"
      (is (false? (:valid? (check [[:r :x 0] [:w :x 1]]
                                  [[:r :x 1] [:w :x 0]])))))
    (testing "chain across two registers"
      (is (false? (:valid? (check [[:r :x 0] [:w :y 1]]
                                  [[:r :y 1] [:w :x 0]])))))
    (testing "write skew"
      ; This violates SI, but doesn't introduce a w-r conflict, so it's legal
      ; as far as this order is concerned.
      (is (true? (:valid? (check [[:r :x 0] [:r :y 0] [:w :x 1]]
                                 [[:r :x 0] [:r :y 0] [:w :y 1]])))))))

(deftest ext-key-graph-test
  (let [ekg (fn [tg] (-> tg g/map->bdigraph ext-key-graph g/->clj))
        ; Helper to construct ops
        op  (fn [index string]
              (h/op (assoc (op string) :index index)))]
    (testing "empty"
      (is (= {}
             (ekg {}))))

    (testing "simple"
      (is (= {(op 0 "rx1") {:x #{(op 1 "rx2")}}
              (op 1 "rx2") {}}
             (ekg {(op 0 "rx1") [(op 1 "rx2")]}))))

    (testing "transitive"
      (is (= {(op 1 "wx1") {:x #{(op 2 "wx2")}}
              (op 2 "wx2") {:x #{(op 3 "wx3")}}
              (op 3 "wx3") {:x #{(op 4 "wx4")}}
              (op 4 "wx4") {}}
             (ekg {(op 1 "wx1") [(op 2 "wx2")]
                   (op 2 "wx2") [(op 3 "wx3")]
                   (op 3 "wx3") [(op 4 "wx4")]}))))

    (testing "transitive w diff keys"
      (is (= {(op 1 "wx1") {:x #{(op 2 "wx2wy2")}
                            :y #{(op 2 "wx2wy2")}
                            :z #{(op 3 "wy3wz3")}}
              (op 2 "wx2wy2") {:y #{(op 3 "wy3wz3")}
                               :z #{(op 3 "wy3wz3")}}
              (op 3 "wy3wz3") {:z #{(op 4 "wz4")}}
              (op 4 "wz4") {}}
             (ekg {(op 1 "wx1")     [(op 2 "wx2wy2")]
                   (op 2 "wx2wy2")  [(op 3 "wy3wz3")]
                   (op 3 "wy3wz3")  [(op 4 "wz4")]}))))))

(deftest ext-key-graph-cache-test
  ; Trying to make sure this isn't quadratic; we construct a chain of ops and
  ; ask for its ext-key-graph.
  (let [ekg (fn [tg] (-> tg g/map->bdigraph ext-key-graph g/->clj))
        ; Helper to construct ops
        op  (fn [index string]
              (h/op (assoc (op string) :index index)))]
    (let [; A linear transaction graph
          t1 (op 1 "wx1")
          t2 (op 2 "wx2")
          t3 (op 3 "wx3")
          t4 (op 4 "wx4")
          t5 (op 5 "wx5")
          tg {t1 [t2] t2 [t3] t3 [t4] t4 [t5]}]
      ;(println (kg-str (ekg tg)))
      )))

(deftest transaction-graph->version-graphs-test
  ; Turn transaction graphs (in clojure maps) into digraphs, then into version
  ; graphs, then back into clojure.
  (let [vg (fn [txn-graph]
             (-> txn-graph
                 g/map->bdigraph
                 transaction-graph->version-graphs
                 g/->clj))
        ; A little helper for making Op objects
        Op (fn Op
             ([index string] (h/op (assoc (op string)
                                    :index index
                                    :time  -1)))
             ([index process type string]
              (h/op (assoc (op process type string)
                           :index index
                           :time -1))))]
    (testing "empty"
      (is (= {}
             (vg {}))))

    (testing "r->w"
      (is (= {:x {1 #{2}
                  2 #{}}}
             (vg {(Op 0 "rx1") [(Op 1 "wx2")]}))))

    (testing "fork-join"
      (is (= {:x {1 #{2 3}
                  2 #{4}
                  3 #{4}
                  4 #{}}}
             (vg {(Op 1 "rx1") [(Op 2 "wx2") (Op 3 "wx3")]
                  (Op 2 "wx2") [(Op 4 "rx4")]
                  (Op 3 "wx3") [(Op 4 "rx4")]}))))

    (testing "external ww"
      (is (= {:x {2 #{4}, 4 #{}}}
             ; 3 is an internal version; we want to generate 2->4!
             (vg {(Op 0 "wx1wx2") [(Op 1 "wx3wx4rx5")]}))))

    (testing "external wr"
      (is (= {:x {2 #{3}, 3 #{}}}
             (vg {(Op 0 "wx1wx2") [(Op 1 "rx3rx4wx5")]}))))

    (testing "external rw"
      (is (= {:x {1 #{4}, 4 #{}}}
             (vg {(Op 0 "rx1rx2") [(Op 1 "wx3wx4rx5")]}))))

    (testing "external rr"
      (is (= {:x {1 #{3}, 3 #{}}}
             (vg {(Op 0 "rx1rx2") [(Op 1 "rx3rx4wx5")]}))))

    (testing "don't infer v1 -> v1 deps"
      (is (= {}
             (vg {(Op 0 "wx1") [(Op 1 "rx1")]}))))

    (testing "don't infer deps on failed or crashed reads"
      (is (= {:x {}}
             (vg {(Op 1 "wx1") [(Op 2 0 :fail "rx2")
                                (Op 3 0 :info "rx3")]
                  (Op 4 0 :fail "rx4") [(Op 5 "rx5")]
                  (Op 6 0 :info "rx6") [(Op 7 "rx7")]}))))

    (testing "don't infer deps on failed writes, but do infer crashed"
      (is (= {:x {1 #{4}, 4 #{}
                  8 #{9}, 9 #{}}}
             (vg {(Op 1 "wx1") [(Op 2 0 :fail "wx2")
                                ; Note that we ignore this read, but use write
                                (Op 3 0 :info "rx3wx4")]
                  (Op 5 0 :fail "wx5") [(Op 6 "rx6")]
                   ; I don't know why you'd be able to get this graph, but if
                   ; you DID, it'd be legal to infer
                   (Op 8 0 :info "wx8") [(Op 9 "rx9")]}))))

    (testing "see through failed/crashed Ops"
      (is (= {:x {1 #{3}, 3 #{}}
              :y {1 #{3}, 3 #{}}}
             (vg {(Op 0 "wx1") [(Op 1 0 :info "rx_") (Op 2 "rx3")]
                  (Op 3 "wy1") [(Op 4 0 :fail "wy2") (Op 5 "ry3")]}))))

    (testing "see through seq. failed/crashed Ops"
      (is (= {:x {1 #{3}, 3 #{}}}
             (vg {(Op 0 "wx1")          [(Op 1 0 :info "rx_")]
                  (Op 1 0 :info "rx_")  [(Op 2 0 :fail "wx2")]
                  (Op 2 0 :fail "wx2")  [(Op 3 0 :ok "wx3")]}))))))

(deftest version-graphs->transaction-graphs-test
  (testing "empty"
    (is (= {}
           (g/->clj (version-graphs->transaction-graph
                      (h/history [])
                      (g/digraph))))))
  (testing "rr"
    ; We don't generate rr edges, under the assumption they'll be covered by
    ; rw/wr/ww edges.
    (is (= {}
           (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                (version-graphs->transaction-graph
                  (h/history [(op "rx1") (op "rx2")]))
                g/->clj))))

  (testing "wr"
    ; We don't emit wr edges here--wr-graph does that for us. Maybe we should
    ; later? Wouldn't be hard...
    (is (= {}
           (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                (version-graphs->transaction-graph
                  (h/history [(op "wx1") (op "rx1")]))
                g/->clj))))

  (testing "ww"
    (let [[w1 w2 :as h] (h/history [(op "wx1") (op "wx2")])]
      (is (= {w1 #{w2}, w2 #{}}
             (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                  (version-graphs->transaction-graph h)
                  g/->clj)))))

  (testing "rw"
    (let [[r w :as h] (h/history [(op "rx1") (op "wx2")])]
      (is (= {r #{w}, w #{}}
             (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                  (version-graphs->transaction-graph h)
                  g/->clj)))))

  (testing "ignores internal writes/reads"
    (is (= {}
           (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                (version-graphs->transaction-graph
                  (h/history [(op "wx1wx2") (op "rx2rx3")]))
                g/->clj)))))

(let [c (fn [checker-opts history]
					(-> (check checker-opts (h/history history))
              ; We don't need to clutter up our test with these; they're just
              ; for humans
              (dissoc :also-not)))]
	(deftest checker-test
    (testing "Read doesn't return what was just been written"
      (let [[t1 t1'] (pair (op "wx1"))
            [t2 t2'] (pair (op "rx2"))]
        ; TODO: this represents a bug! We should detect this as invalid.
        (is (= {:valid? true}
               (c {:consistency-models [:strict-serializable]
                   :linearizable-keys? true } [t1 t1' t2 t2'])))))

    (testing "Read read returns what was just been written"
      (let [[t1 t1'] (pair (op "wx1"))
            [t2 t2'] (pair (op "rx2"))
            [t3 t3'] (pair (op "rx1"))]
        (is (= {:valid? false
                :anomaly-types '(:cyclic-versions)
                :anomalies
               {:cyclic-versions
                [{:key :x,
                  :scc #{1 2},
                  :sources [:initial-state :linearizable-keys]}]},
               :not #{:read-uncommitted}}
               (c {:consistency-models [:strict-serializable]
                   :linearizable-keys? true } [t1 t1' t2 t2' t3 t3'])))))
    (testing "G0"
      ; What (could be) a pure write cycle: T1 < T2 on x, T2 < T1 on y.
      (let [[t1 t1'] (pair (op 0 :ok "wx1wy2"))
            [t2 t2'] (pair (op 1 :ok "wx2wy1"))]
        ; Of course we can't detect this naively: there's no wr-cycle, and we
        ; can't say anything about versions. This *isn't* illegal yet!
        (is (= {:valid? :unknown
                :anomaly-types  [:empty-transaction-graph]
                :anomalies      {:empty-transaction-graph true}
                :not            #{}}
               (c {:consistency-models nil
                   :anomalies          [:G0]} (h/history [t1 t2]))))

        ; But let's say we observe a read *after* both transactions which shows
        ; that the final value of x and y are both 2? We can infer this from
        ; sequential keys alone, as long as the version order aligns.
        (let [[t3 t3'] (pair (op 0 :ok "rx2"))
              [t4 t4'] (pair (op 1 :ok "ry2"))
                         [t1 t1' t2 t2' t3 t3' t4 t4' :as h]
              (h/history [t1 t1' t2 t2' t3 t3' t4 t4'])]
          (is (= {:valid?         false
                  :anomaly-types  [:G0]
                  :not            #{:read-uncommitted}
                  :anomalies      {:G0 [{:cycle [t1' t2' t1']
                                        :steps
                                        [{:key :x,
                                          :value 1,
                                          :value' 2,
                                          :type :ww,
                                          :a-mop-index 0,
                                          :b-mop-index 0}
                                         {:key :y,
                                          :value 1,
                                          :value' 2,
                                          :type :ww,
                                          :a-mop-index 1,
                                          :b-mop-index 1}],
                                        :type :G0}]}}
                 (c {:consistency-models  nil
                     :anomalies           [:G0]
                     :sequential-keys?    true}
                    [t1 t1' t2 t2' t3 t3' t4 t4']))))))

    (testing "G1a"
      (let [; T2 sees T1's failed write
            t1 (fail (op "wx1"))
            t2 (op "rx1")
            [t2 t1 :as h] (h/history [t2 t1])]
        (is (= {:valid? false
                :anomaly-types [:G1a :empty-transaction-graph]
                :not           #{:read-committed}
                :anomalies {:empty-transaction-graph true
                            :G1a [{:op      t2
                                   :writer  t1
                                   :mop     [:r :x 1]}]}}
               (c {:consistency-models nil, :anomalies [:G1]} [t2 t1])))))

    (testing "G1b"
      (let [; T2 sees T1's intermediate write
            t1 (op "wx1wx2")
            t2 (op "rx1")
            [t1 t2 :as h] (h/history [t1 t2])]
        ; G0 checker won't catch this. The txn graph is empty though,
        ; because the read dep isn't external.
        (is (= {:valid?         :unknown
                :anomaly-types  [:empty-transaction-graph]
                :anomalies      {:empty-transaction-graph true}
                :not            #{:read-committed}}
               (c {:consistency-models  nil
                   :anomalies           [:G0]}
                  h)))

        ; G1 will, as will a read-committed checker.
        (is (= {:valid? false
                :anomaly-types [:G1b :empty-transaction-graph]
                :not       #{:read-committed}
                :anomalies {:empty-transaction-graph true
                              :G1b [{:op    t2
                                   :writer  t1
                                   :mop     [:r :x 1]}]}}
               (c {:consistency-models nil
                   :anomalies          [:G1]}
                  h)
               (c {:consistency-models [:repeatable-read]}
                  h)))))

    (testing "G1c"
      (let [; T2 observes T1's write of x, and vice versa on y.
            t1 (op "wx1ry1")
            t2 (op "wy1rx1")
            [t1 t2 :as h] (h/history [t1 t2])
            msg {:cycle [t1 t2 t1]
                 :steps
                 [{:type :wr,
                   :key :x,
                   :value 1,
                   :a-mop-index 0,
                   :b-mop-index 1}
                  {:type :wr,
                   :key :y,
                   :value 1,
                   :a-mop-index 0,
                   :b-mop-index 1}],
                 :type :G1c}]
        ; G0/read-uncommitted won't see this
        (is (= {:valid? true}
               (c {:consistency-models nil
                   :anomalies [:G0]}
                  h)))
        (is (= {:valid? true}
               (c {:consistency-models [:read-uncommitted]}
                  h)))

        ; But G1 will, as will a read-committed checker.
        (let [res {:valid? false
                   :anomaly-types  [:G1c]
                   :not            #{:read-committed}
                   :anomalies {:G1c [msg]}}]
          (is (= res (c {:consistency-models  nil
                         :anomalies           [:G1]}
                        h)))
          (is (= res (c {:consistency-models  [:read-committed]}
                        h))))

        ; A checker looking for G2 alone won't care about this, because G1c is
        ; not G2
        (is (= {:valid? true}
               (c {:consistency-models  nil
                   :anomalies           [:G2]}
                  h)))

        ; But a serializable checker will catch this, because serializability
        ; proscribes both G1 and G2.
        (is (= {:valid? false
                :not            #{:read-committed}
                :anomaly-types  [:G1c]
                :anomalies      {:G1c [msg]}}
               (c {:consistency-models [:serializable]}
                  h)))))

    (testing "writing files"
      (let [; T2 observes T1's write of x, and vice versa on y.
            t1 (op "wx1ry1")
            t2 (op "wy1rx1")
            [t1 t2 :as h] (h/history [t1 t2])
            msg "G1c #0\nLet:\n  T1 = {:index 0, :time -1, :type :ok, :process 0, :f nil, :value [[:w :x 1] [:r :y 1]]}\n  T2 = {:index 1, :time -1, :type :ok, :process 0, :f nil, :value [[:w :y 1] [:r :x 1]]}\n\nThen:\n  - T1 < T2, because T1 wrote :x = 1, which was read by T2.\n  - However, T2 < T1, because T2 wrote :y = 1, which was read by T1: a contradiction!"]
        ; Write out file and check for a cycle txt file
        (c {:consistency-models nil
            :anomalies [:G1]
            :plot-format :png
            :directory "test-output"} h)
        (is (= msg (slurp "test-output/G1c.txt")))))

    (testing "G2-item"
      (let [[t1 t1'] (pair (op 0 :ok "rx1ry1"))  ; Establish the initial state
            [t2 t2'] (pair (op 1 :ok "rx1wy2"))  ; Advance y
            [t3 t3'] (pair (op 2 :ok "ry1wx2"))  ; Advance x
            h        [t1 t1' t2 t3 t3' t2']]
        ; G2 should catch this, so long as we can use the linearizable key
        ; assumption to infer that t2 and t3's writes of 2 follow
        ; the initial states of 1.
        (let [res {:valid?         false
                   :anomaly-types  [:G2-item]
                   :not            #{:serializable}
                   :anomalies {:G2 [{:cycle
                                     [{:type :ok,
                                       :value [[:r :x 1] [:w :y 2]],
                                       :process 1,
                                       :index 5}
                                      {:type :ok,
                                       :value [[:r :y 1] [:w :x 2]],
                                       :process 2,
                                       :index 4}
                                      {:type :ok,
                                       :value [[:r :x 1] [:w :y 2]],
                                       :process 1,
                                       :index 5}],
                                     :steps
                                     [{:key :x,
                                       :value 1,
                                       :value' 2,
                                       :type :rw,
                                       :a-mop-index 0,
                                       :b-mop-index 1}
                                      {:key :y,
                                       :value 1,
                                       :value' 2,
                                       :type :rw,
                                       :a-mop-index 0,
                                       :b-mop-index 1}],
                                     :type :G2-item}]}}]
          ; Read committed won't see this, since it's G2-item.
          (is (= {:valid? true}
                 (c {:consistency-models [:read-committed]
                     :linearizable-keys? true}
                    h)))
          ; But repeatable read will!
          (c {:consistency-models nil
              :anomalies         [:G2]
              :linearizable-keys? true}
             [t1 t1' t2 t3 t3' t2']))))

    (testing "internal"
      (let [t1 (op "rx1rx2")
            [t1 :as h] (h/history [t1])]
        (is (= {:valid? false
                :anomaly-types [:empty-transaction-graph :internal]
                :not       #{:read-atomic}
                :anomalies {:internal [{:op       t1
                                        :mop      [:r :x 2]
                                        :expected 1}]
                            :empty-transaction-graph true}}
               (c {:consistency-models nil, :anomalies [:internal]} h)))))

    (testing "initial state"
      (let [[t1 t1'] (pair (op 0 :ok "rx_ry1"))
            [t2 t2'] (pair (op 0 :ok "wy1wx2"))
            [t1 t2 t2' t1'] (h/history [t1 t2 t2' t1'])]
        ; We can infer, on the basis that nil *must* precede every non-nil
        ; value, plus the direct wr dep, that this constitutes a G-single
        ; anomaly!
        (is (= {:valid? false
                :anomaly-types [:G-single-item]
                :not           #{:consistent-view :repeatable-read}
                :anomalies {:G-single-item
                            [{:cycle [t1' t2' t1']
                              :steps
                              [{:key :x,
                                :value nil,
                                :value' 2,
                                :type :rw,
                                :a-mop-index 0,
                                :b-mop-index 1}
                               {:type :wr,
                                :key :y,
                                :value 1,
                                :a-mop-index 0,
                                :b-mop-index 1}],
                              :type :G-single-item}]}}
               (c {:consistency-models [:serializable]} [t1 t2 t2' t1'])))))

    (testing "wfr"
      (let [t1 (op 0 :ok "ry1wx1wy2")  ; Establishes y: 1 -> 2
            t2 (op 0 :ok "rx1ry1") ; t1 <wr t2, on x, but also t2 <rw t1, on y!
            [t1 t2 :as h] (h/history [t1 t2])]
        ; We can't see this without knowing the version order on y
        (is (= {:valid? true}
               (c {:wfr-keys?           false
                   :consistency-models  [:serializable]}
                  h)))
        ; But if we use WFR, we know 1 < 2, and can see the G-single
        (is (= {:valid? false
                :anomaly-types [:G-single-item]
                :not           #{:consistent-view :repeatable-read}
                :anomalies {:G-single-item
                            [{:cycle [t2 t1 t2]
                              :steps
                              [{:key :y,
                                :value 1,
                                :value' 2,
                                :type :rw,
                                :a-mop-index 1,
                                :b-mop-index 2}
                               {:type :wr,
                                :key :x,
                                :value 1,
                                :a-mop-index 1,
                                :b-mop-index 0}],
                              :type :G-single-item}]}}
               (c {:wfr-keys? true
                   :consistency-models [:serializable]}
                  h)))))

    (testing "cyclic version order"
      (let [[t1 t1'] (pair (op 0 :ok "wx1"))
            [t2 t2'] (pair (op 0 :ok "wx2"))
            [t3 t3'] (pair (op 0 :ok "rx1"))]
        (is (= {:valid?         false
                :not            #{:read-uncommitted}
                :anomaly-types  [:cyclic-versions]
                :anomalies      {:cyclic-versions
                                 [{:key :x, :scc #{1 2} :sources [:initial-state
                                                                  :sequential-keys]}]}}
               (c {:sequential-keys? true}
                  [t1 t1' t2 t2' t3 t3']))))))

  (deftest type-sanity
    (is (thrown-with-msg? java.lang.AssertionError #"a mix of integer types"
                          (c {}
                             [{:process 0, :type :ok, :value [[:r :x (short 1)]]}
                              {:process 0, :type :ok, :value [[:r :x (long 1)]]}]))))


  (deftest lost-update-test
    ; For a lost update, we need two transactions which read the same value of
    ; some key and both write to it.
    (let [[t1 t1'] (pair (op 0 :ok "rx0wx1"))
          [t2 t2'] (pair (op 1 :ok "rx0wx2"))
          [t1 t1' t2 t2' :as h] (h/history [t1 t1' t2 t2'])]
      (is (= {:valid? false
              :not    #{:update-atomic :cursor-stability}
              :anomaly-types [:lost-update]
              :anomalies {:lost-update
                          [{:key :x
                            :value 0
                            :txns [t1' t2']}]}}
             (c {} h)))))

	)

; This is here for pasting in experimental histories when we hit checker bugs.
; It's a helpful skeleton for refining a test case.
(comment
(deftest foo-test
  (let [h [

           ]]
    (is (= {:valid? false}
           (checker/check (checker {:additional-graphs  [cycle/realtime-graph]
                                    :consistency-models [:snapshot-isolation]
                                    :sequential-keys?   true
                                    :wfr-keys?          true})
                          nil
                          (h/history h)
                          nil)))))
)

(comment
  (deftest g-single-misattribution-test
    ; This captures a problem with the current design: it's not necessarily
    ; clear what anomalies mean when there are extra edges in the dependency
    ; graph. For instance, this history contains a G-single anomaly if you
    ; consider that it only requires one rw edge (the other edge is a process
    ; edge) for the cycle. However, the explainer prefers to use wr, ww, rw,
    ; and *then* additional graphs, so it explains this "g-single" anomaly as
    ; if it were G2--using both anti-dependency cycles, rather than process
    ; order.
    ;
    ; TODO: I don't know how to fix this yet, but I'm leaving it here for an
    ; enterprising individual (hi future Kyle!?) to address if it ever comes up
    ; again. I have a vague feeling that we could augment Cycle DataExplainer so
    ; that it has some concept of, like, what *kind* of anomaly it's being asked
    ; to explain? Or maybe we should just order rw-edges last and be done with
    ; it? That doesn't feel right, because IMO a pure rw cycle is *more*
    ; interesting than, say, an rw+realtime cycle.
    ;
    ; Also this suggests that we should stop faffing about calling cycles with
    ; realtime edges "G0" etc, and define *additional* anomaly classes. Maybe
    ; call them G0+, when we use additional graphs?
    (let [h [{:type :invoke,
              :f :txn,
              :value [[:w 499 14] [:w 503 1]],
              :process 4}
             {:type :ok,
              :f :txn,
              :value [[:w 499 14] [:w 503 1]],
              :process 4}
             {:type :invoke,
              :f :txn,
              :value [[:r 503 nil] [:w 503 11]],
              :process 4}
             {:type :ok,
              :f :txn,
              :value [[:r 503 1] [:w 503 11]],
              :process 4}
             {:type :invoke,
              :f :txn,
              :value [[:r 503 nil] [:w 503 13]],
              :process 4}
             {:type :ok,
              :f :txn,
              :value [[:r 503 1] [:w 503 13]],
              :process 4}]]
      (is (= {:valid? false,
              :anomaly-types [:G-single :G2],
              :anomalies
              ; This G-single is currently misreported. TODO: uncomment this
              ; test and fix, when we feel like it's important.
              {:G-single
               ["Let:\n  T1 = {:type :ok, :f :txn, :value [[:r 503 1] [:w 503 13]], :process 4, :index 5}\n  T2 = {:type :ok, :f :txn, :value [[:r 503 1] [:w 503 11]], :process 4, :index 3}\n\nThen:\n  - T1 < T2, because T1 read key 503 = 1, and T2 set it to 11, which came later in the version order.\n  - However, T2 < T1, because process whatever executed T1 before T2: a contradiction!"],
               ; This G2 is real
               :G2
               ["Let:\n  T1 = {:type :ok, :f :txn, :value [[:r 503 1] [:w 503 11]], :process 4, :index 3}\n  T2 = {:type :ok, :f :txn, :value [[:r 503 1] [:w 503 13]], :process 4, :index 5}\n\nThen:\n  - T1 < T2, because T1 read key 503 = 1, and T2 set it to 13, which came later in the version order.\n  - However, T2 < T1, because T2 read key 503 = 1, and T1 set it to 11, which came later in the version order: a contradiction!"]}}
             (checker/check (checker {:additional-graphs [cycle/process-graph]
                                      ; As an aside, if you were to use sequential keys
                                      ; here, you'd see key 503 go from 1 -> 11
                                      ; -> 1, which would imply a version cycle.
                                      ; :sequential-keys? true
                                      :wfr-keys? true})
                            nil
                            (history/index h)
                            nil))))))

(deftest ^:perf ext-key-graph-perf-test
  ; Generate a random history
  (let [history (atom [])
        x       (atom 0)
        state   (atom {})
        threads (real-pmap
                  (fn [p]
                    (dotimes [i 1000]
                      ; Simulate a generation and random key
                      (let [k [(mod i 32) (rand-int 5)]
                            x (swap! x inc)]
                        (swap! history conj {:type :invoke, :process p, :value [[:w k x]]})
                        (swap! state assoc k x)
                        (swap! history conj {:type :ok, :process p, :value [[:w k x]]}))))
                    (range 5))
        history (h/history @history)
        graph   (:graph (elle/realtime-graph history))]
		; (prn graph)
    ; (println (ext-key-graph graph))
    (time
			(ext-key-graph graph))))

(deftest ^:perf perfect-perf-test
  ; An end-to-end performance test based on a perfect strict-1SR DB.
  (let [n (long 1e5)
        ; Takes state and txn, returns [state' txn'].
        apply-txn (fn apply-txn [state txn]
                    (loopr [state' (transient state)
                            txn'   (transient [])]
                           [[f k v :as mop] txn]
                           (case f
                             :w (recur (assoc! state' k v)
                                       (conj! txn' mop))
                             :r (recur state'
                                       (conj! txn' [f k (get state' k)])))
                           [(persistent! state')
                            (persistent! txn')]))
        t0 (System/nanoTime)
        ; Build history
        h (loopr [history (transient [])
                  state   {}
                  i       0]
                 [op (take n (gen))]
                 (let [process        (rand-int 10)
                       op (h/op       (assoc op
                                             :index i
                                             :time i
                                             :process process))
                       history'       (conj! history op)
                       [state' txn']  (apply-txn state (:value op))
                       i'             (inc i)
                       op'            (assoc op :index i', :time i',
                                             :type :ok, :value txn')
                       history'       (conj! history' op')]
                   (recur history' state' (inc i')))
                 (h/history (persistent! history)
                            {:dense-indices? true
                             :have-indices? true
                             :already-ops? true}))
        t1 (System/nanoTime)
        _ (is (= (* 2 n) (count h)))
        analysis (check {:sequential-keys? true} h)
        t2 (System/nanoTime)
        run-time   (/ (- t1 t0) 1e9)
        check-time (/ (- t2 t1) 1e9)]
    (is (= true (:valid? analysis)))
    (println (format "rw-register-perf-test: %d ops run in %.2f s (%.2f ops/sec); checked in %.2f s (%.2f ops/sec)"
                     n run-time (/ n run-time)
                     check-time (/ n check-time)))))
