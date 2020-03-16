(ns elle.rw-register-test
  (:refer-clojure :exclude [test])
  (:require [clojure.pprint :refer [pprint]]
            [dom-top.core :refer [real-pmap]]
						[elle [core :as elle]
                  [graph :as g]
                  [rw-register :refer :all]
                  [util :refer [map-vals]]]
            [jepsen.txn :as txn]
            [knossos [history :as history]
                     [op :as op]]
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
     {:type :ok, :value txn}))
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
  (is (= {:type :ok, :value [[:w :x 1] [:r :x 2]]}
         (op "wx1rx2"))))

(deftest ext-index-test
  (testing "empty"
    (is (= {} (ext-index txn/ext-writes []))))
  (testing "writes"
    (let [w1 {:type :ok, :value [[:w :x 1] [:w :y 3] [:w :x 2]]}
          w2 {:type :ok, :value [[:w :y 3] [:w :x 4]]}]
      (is (= {:x {2 [w1], 4 [w2]}
              :y {3 [w2 w1]}}
             (ext-index txn/ext-writes [w1 w2]))))))

(deftest internal-cases-test
  (testing "empty"
    (is (= nil (internal-cases []))))

  (testing "good"
    (is (= nil (internal-cases [(op "ry2wx2rx2wx1rx1")]))))

  (testing "stale"
    (let [stale (op "rx1wx2rx1")]
      (is (= [{:op stale, :mop [:r :x 1], :expected 2}]
             (internal-cases [stale]))))))

(deftest g1a-cases-test
  (testing "empty"
    (is (= nil (g1a-cases []))))

  (testing "good"
    (is (= nil (g1a-cases [(op "wx1")
                           (op "rx1")]))))

  (testing "bad"
    (let [w (fail (op "wx2"))
          r (op "rx2")]
      (is (= [{:op r, :writer, w :mop [:r :x 2]}]
             (g1a-cases [r w]))))))

(deftest g1b-cases-test
  (testing "empty"
    (is (= nil (g1b-cases []))))

  (testing "good"
    (is (= nil (g1b-cases [(op "wx1wx2")
                           (op "rx_rx2")]))))

  (testing "bad"
    (let [w (op "wx2wx1")
          r (op "rx2")]
      (is (= [{:op r, :writer, w :mop [:r :x 2]}]
             (g1b-cases [r w]))))))

(deftest wr-graph-test
  ; helper fns for constructing histories
  (let [op (fn [txn] [{:type :invoke, :f :txn, :value txn}
                      {:type :ok,     :f :txn, :value txn}])
        check (fn [& txns]
                (let [h (mapcat op txns)]
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
      ; this violates si, but doesn't introduce a w-r conflict, so it's legal
      ; as far as this order is concerned.
      (is (true? (:valid? (check [[:r :x 0] [:r :y 0] [:w :x 1]]
                                 [[:r :x 0] [:r :y 0] [:w :y 1]])))))))

(deftest ext-key-graph-test
  (let [ekg (fn [tg] (-> tg g/map->bdigraph ext-key-graph g/->clj))]
    (testing "empty"
      (is (= {}
             (ekg {}))))

    (testing "simple"
      (is (= {(op "rx1") {:x #{(op "rx2")}}
              (op "rx2") {}}
             (ekg {(op "rx1") [(op "rx2")]}))))

    (testing "transitive"
      (is (= {(op "wx1") {:x #{(op "wx2")}}
              (op "wx2") {:x #{(op "wx3")}}
              (op "wx3") {:x #{(op "wx4")}}
              (op "wx4") {}}
             (ekg {(op "wx1") [(op "wx2")]
                   (op "wx2") [(op "wx3")]
                   (op "wx3") [(op "wx4")]}))))

    (testing "transitive w diff keys"
      (is (= {(op "wx1") {:x #{(op "wx2wy2")}
                          :y #{(op "wx2wy2")}
                          :z #{(op "wy3wz3")}}
              (op "wx2wy2") {:y #{(op "wy3wz3")}
                             :z #{(op "wy3wz3")}}
              (op "wy3wz3") {:z #{(op "wz4")}}
              (op "wz4") {}}
             (ekg {(op "wx1")     [(op "wx2wy2")]
                   (op "wx2wy2")  [(op "wy3wz3")]
                   (op "wy3wz3")  [(op "wz4")]}))))))


(deftest transaction-graph->version-graphs-test
  ; Turn transaction graphs (in clojure maps) into digraphs, then into version
  ; graphs, then back into clojure.
  (let [vg (fn [txn-graph]
             (-> txn-graph
                 g/map->bdigraph
                 transaction-graph->version-graphs
                 g/->clj))]
    (testing "empty"
      (is (= {}
             (vg {}))))

    (testing "r->w"
      (is (= {:x {1 #{2}
                  2 #{}}}
             (vg {(op "rx1") [(op "wx2")]}))))

    (testing "fork-join"
      (is (= {:x {1 #{2 3}
                  2 #{4}
                  3 #{4}
                  4 #{}}}
             (vg {(op "rx1") [(op "wx2") (op "wx3")]
                  (op "wx2") [(op "rx4")]
                  (op "wx3") [(op "rx4")]}))))

    (testing "external ww"
      (is (= {:x {2 #{4}, 4 #{}}}
             ; 3 is an internal version; we want to generate 2->4!
             (vg {(op "wx1wx2") [(op "wx3wx4rx5")]}))))

    (testing "external wr"
      (is (= {:x {2 #{3}, 3 #{}}}
             (vg {(op "wx1wx2") [(op "rx3rx4wx5")]}))))

    (testing "external rw"
      (is (= {:x {1 #{4}, 4 #{}}}
             (vg {(op "rx1rx2") [(op "wx3wx4rx5")]}))))

    (testing "external rr"
      (is (= {:x {1 #{3}, 3 #{}}}
             (vg {(op "rx1rx2") [(op "rx3rx4wx5")]}))))

    (testing "don't infer v1 -> v1 deps"
      (is (= {:x {}}
             (vg {(op "wx1") [(op "rx1")]}))))

    (testing "don't infer deps on failed or crashed reads"
      (is (= {:x {}}
             (vg {(op "wx1") [(op 0 :fail "rx2")
                              (op 0 :info "rx3")]
                  (op 0 :fail "rx4") [(op "rx5")]
                  (op 0 :info "rx6") [(op "rx7")]}))))

    (testing "don't infer deps on failed writes, but do infer crashed"
      (is (= {:x {1 #{4}, 4 #{}
                  8 #{9}, 9 #{}}}
              (vg {(op "wx1") [(op 0 :fail "wx2")
                               ; Note that we ignore this read, but use write
                               (op 0 :info "rx3wx4")]
                   (op 0 :fail "wx5") [(op "rx6")]
                   ; I don't know why you'd be able to get this graph, but if
                   ; you DID, it'd be legal to infer
                   (op 0 :info "wx8") [(op "rx9")]}))))

    (testing "see through failed/crashed ops"
      (is (= {:x {1 #{3}, 3 #{}}
              :y {1 #{3}, 3 #{}}}
             (vg {(op "wx1") [(op 0 :info "rx_") (op "rx3")]
                  (op "wy1") [(op 0 :fail "wy2") (op "ry3")]}))))

    (testing "see through seq. failed/crashed ops"
      (is (= {:x {1 #{3}, 3 #{}}}
             (vg {(op "wx1")          [(op 0 :info "rx_")]
                  (op 0 :info "rx_")  [(op 0 :fail "wx2")]
                  (op 0 :fail "wx2")  [(op 0 :ok "wx3")]}))))))

(deftest version-graphs->transaction-graphs-test
  (testing "empty"
    (is (= {}
           (g/->clj (version-graphs->transaction-graph
                      []
                      (g/digraph))))))
  (testing "rr"
    ; We don't generate rr edges, under the assumption they'll be covered by
    ; rw/wr/ww edges.
    (is (= {}
           (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                (version-graphs->transaction-graph [(op "rx1") (op "rx2")])
                g/->clj))))

  (testing "wr"
    ; We don't emit wr edges here--wr-graph does that for us. Maybe we should
    ; later? Wouldn't be hard...
    (is (= {}
           (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                (version-graphs->transaction-graph [(op "wx1") (op "rx1")])
                g/->clj))))

  (testing "ww"
    (is (= {(op "wx1") #{(op "wx2")}
            (op "wx2") #{}}
           (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                (version-graphs->transaction-graph [(op "wx1") (op "wx2")])
                g/->clj))))

  (testing "rw"
    (is (= {(op "rx1") #{(op "wx2")}
            (op "wx2") #{}}
           (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                (version-graphs->transaction-graph [(op "rx1") (op "wx2")])
                g/->clj))))

  (testing "ignores internal writes/reads"
    (is (= {}
           (->> {:x (g/map->bdigraph {1 [2], 2 [3]})}
                (version-graphs->transaction-graph [(op "wx1wx2")
                                                    (op "rx2rx3")])
                g/->clj)))))

(let [c (fn [checker-opts history]
					(-> (check checker-opts (history/index history))
              ; We don't need to clutter up our test with these; they're just
              ; for humans
              (dissoc :also-not)))]
	(deftest checker-test
    (testing "G0"
      ; What (could be) a pure write cycle: T1 < T2 on x, T2 < T1 on y.
      (let [[t1 t1'] (pair (op 0 :ok "wx1wy2"))
            [t2 t2'] (pair (op 1 :ok "wx2wy1"))]
        ; Of course we can't detect this naively: there's no wr-cycle, and we
        ; can't say anything about versions. This *isn't* illegal yet!
        (is (= {:valid?         :unknown
                :anomaly-types  [:empty-transaction-graph]
                :not            #{}
                :anomalies      {:empty-transaction-graph true}}
               (c {:anomalies [:G0]} [t1 t2])))

        ; But let's say we observe a read *after* both transactions which shows
        ; that the final value of x and y are both 2? We can infer this from
        ; sequential keys alone, as long as the version order aligns.
        (let [[t3 t3'] (pair (op 0 :ok "rx2"))
              [t4 t4'] (pair (op 1 :ok "ry2"))]
          (is (= {:valid?         false
                  :anomaly-types  [:G0]
                  :not            #{:read-uncommitted}
                  :anomalies      {:G0 [{:cycle
                                        [{:type :ok,
                                          :value [[:w :x 1] [:w :y 2]],
                                          :process 0,
                                          :index 1}
                                         {:type :ok,
                                          :value [[:w :x 2] [:w :y 1]],
                                          :process 1,
                                          :index 3}
                                         {:type :ok,
                                          :value [[:w :x 1] [:w :y 2]],
                                          :process 0,
                                          :index 1}],
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
                 (c {:anomalies         [:G0]
                     :sequential-keys?  true}
                    [t1 t1' t2 t2' t3 t3' t4 t4']))))))

    (testing "G1a"
      (let [; T2 sees T1's failed write
            t1 (fail (op "wx1"))
            t2 (op "rx1")]
        (is (= {:valid? false
                :anomaly-types [:G1a :empty-transaction-graph]
                :not           #{:read-atomic :read-committed}
                :anomalies {:empty-transaction-graph true
                            :G1a [{:op      (assoc t2 :index 0)
                                   :writer  (assoc t1 :index 1)
                                   :mop     [:r :x 1]}]}}
               (c {:anomalies [:G1]} [t2 t1])))))

    (testing "G1b"
      (let [; T2 sees T1's intermediate write
            t1 (op "wx1wx2")
            t2 (op "rx1")
            h  [t1 t2]]
        ; G0 checker won't catch this
        (is (= {:valid?         :unknown
                :anomaly-types  [:empty-transaction-graph]
                :not            #{}
                :anomalies {:empty-transaction-graph true}}
               (c {:anomalies [:G0]} h)))

        ; G1 will
        (is (= {:valid? false
                :anomaly-types [:G1b :empty-transaction-graph]
                :not       #{:read-committed}
                :anomalies {:empty-transaction-graph true
                              :G1b [{:op      (assoc t2 :index 1)
                                   :writer  (assoc t1 :index 0)
                                   :mop     [:r :x 1]}]}}
               (c {:anomalies [:G1]} h)))))

    (testing "G1c"
      (let [; T2 observes T1's write of x, and vice versa on y.
            t1 (op "wx1ry1")
            t2 (op "wy1rx1")
            h  [t1 t2]
            msg {:cycle
                  [{:type :ok, :value [[:w :y 1] [:r :x 1]], :index 1}
                   {:type :ok, :value [[:w :x 1] [:r :y 1]], :index 0}
                   {:type :ok, :value [[:w :y 1] [:r :x 1]], :index 1}],
                  :steps
                  [{:type :wr,
                    :key :y,
                    :value 1,
                    :a-mop-index 0,
                    :b-mop-index 1}
                   {:type :wr,
                    :key :x,
                    :value 1,
                    :a-mop-index 0,
                    :b-mop-index 1}],
                  :type :G1c}]
        ; G0 won't see this
        (is (= {:valid? true} (c {:anomalies [:G0]} h)))
        ; But G1 will!
        (is (= {:valid? false
                :anomaly-types  [:G1c]
                :not            #{:read-committed}
                :anomalies {:G1c [msg]}}
               (c {:anomalies [:G1]} h)))
        ; As will G2
        (is (= {:valid? false
                :not           #{:read-committed}
                :anomaly-types [:G1c]
                :anomalies {:G1c [msg]}}
               (c {:anomalies [:G2]} h)))))

    (testing "writing files"
      (let [; T2 observes T1's write of x, and vice versa on y.
            t1 (op "wx1ry1")
            t2 (op "wy1rx1")
            h  [t1 t2]
            msg "G1c #0\nLet:\n  T1 = {:type :ok, :value [[:w :y 1] [:r :x 1]], :index 1}\n  T2 = {:type :ok, :value [[:w :x 1] [:r :y 1]], :index 0}\n\nThen:\n  - T1 < T2, because T1 wrote :y = 1, which was read by T2.\n  - However, T2 < T1, because T2 wrote :x = 1, which was read by T1: a contradiction!"]
        ; Write out file and check for a cycle txt file
        (c {:anomalies [:G1]
            :plot-format :png
            :directory "test-output"} h)
        (is (= msg (slurp "test-output/G1c.txt")))))

    (testing "G2"
      (let [[t1 t1'] (pair (op 0 :ok "rx1ry1"))  ; Establish the initial state
            [t2 t2'] (pair (op 1 :ok "rx1wy2"))  ; Advance y
            [t3 t3'] (pair (op 2 :ok "ry1wx2"))] ; Advance x
        ; G2 should catch this, so long as we can use the linearizable key
        ; assumption to infer that t2 and t3's writes of 2 follow
        ; the initial states of 1.
        (is (= {:valid?         false
                :anomaly-types  [:G2]
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
                                  :type :G2}]}}
               (c {:anomalies         [:G2]
                   :linearizable-keys? true}
                  [t1 t1' t2 t3 t3' t2'])))))

    (testing "internal"
      (let [t1 (op "rx1rx2")
            h  [t1]]
        (is (= {:valid? false
                :anomaly-types [:empty-transaction-graph :internal]
                :not       #{:read-atomic}
                :anomalies {:internal [{:op       (assoc t1 :index 0)
                                        :mop      [:r :x 2]
                                        :expected 1}]
                            :empty-transaction-graph true}}
               (c {:anomalies [:internal]} h)))))

    (testing "initial state"
      (let [[t1 t1'] (pair (op 0 :ok "rx_ry1"))
            [t2 t2'] (pair (op 0 :ok "wy1wx2"))]
        ; We can infer, on the basis that nil *must* precede every non-nil
        ; value, plus the direct wr dep, that this constitutes a G-single
        ; anomaly!
        (is (= {:valid? false
                :anomaly-types [:G-single]
                :not           #{:consistent-view}
                :anomalies {:G-single [{:cycle
                                        [{:type :ok,
                                          :value [[:r :x nil] [:r :y 1]],
                                          :process 0,
                                          :index 3}
                                         {:type :ok,
                                          :value [[:w :y 1] [:w :x 2]],
                                          :process 0,
                                          :index 2}
                                         {:type :ok,
                                          :value [[:r :x nil] [:r :y 1]],
                                          :process 0,
                                          :index 3}],
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
                                        :type :G-single}]}}
               (c {} [t1 t2 t2' t1'])))))

    (testing "wfr"
      (let [t1 (op 0 :ok "ry1wx1wy2")  ; Establishes y: 1 -> 2
            t2 (op 0 :ok "rx1ry1")]    ; t1 <wr t2, on x, but also t2 <rw t1, on y!
        ; We can't see this without knowing the version order on y
        (is (= {:valid? true}
               (c {:wfr-keys? false} [t1 t2])))
        ; But if we use WFR, we know 1 < 2, and can see the G-single
        (is (= {:valid? false
                :anomaly-types [:G-single]
                :not           #{:consistent-view}
                :anomalies {:G-single
                            [{:cycle
                              [{:type :ok,
                                :value [[:r :x 1] [:r :y 1]],
                                :process 0,
                                :index 1}
                               {:type :ok,
                                :value [[:r :y 1] [:w :x 1] [:w :y 2]],
                                :process 0,
                                :index 0}
                               {:type :ok,
                                :value [[:r :x 1] [:r :y 1]],
                                :process 0,
                                :index 1}],
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
                              :type :G-single}]}}
               (c {:wfr-keys? true} [t1 t2])))))

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
                             [{:value [[:r :x (short 1)]]}
                              {:value [[:r :x (long 1)]]}]))))

	)

; This is here for pasting in experimental histories when we hit checker bugs.
; It's a helpful skeleton for refining a test case.
(comment
(deftest ^:test-refresh/focus foo-test
  (let [h [

           ]]
    (is (= {:valid? false}
           (checker/check (checker {:additional-graphs  [cycle/realtime-graph]
																		:anomalies [:G-single :G1a :G1b :internal]
                                    :sequential-keys?   true
                                    :wfr-keys?          true})
                          nil
                          (history/index h)
                          nil)))))
)

(comment
  (deftest g-single-misattribution-test
    ; This captures a problem with the current design: it's not necessarily clear
    ; what anomalies mean when there are extra edges in the dependency graph. For
    ; instance, this history contains a G-single anomaly if you consider that it
    ; only requires one rw edge (the other edge is a process edge) for the cycle.
    ; However, the explainer prefers to use wr, ww, rw, and *then* additional
    ; graphs, so it explains this "g-single" anomaly as if it were G2--using both
    ; anti-dependency cycles, rather than process order.
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

(deftest ^:perf e-graph-test-perf
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
        history (history/index @history)
        graph   (:graph (elle/realtime-graph history))]
		; (prn graph)
    ; (println (ext-key-graph graph))
    (time
			(ext-key-graph graph))))
