(ns elle.rw-register-test
  (:refer-clojure :exclude [test])
  (:require [bifurcan-clj [core :as b]
                          [map :as bm]
                          [set :as bs]
                          [graph :as bg]]
            [clojure.pprint :refer [pprint]]
            [clojure.test.check.generators :as gen]
            [com.gfredericks.test.chuck.clojure-test :refer [checking]]
            [dom-top.core :refer [loopr real-pmap]]
						[elle [core :as elle]
                  [core-test :refer [read-history]]
                  [graph :as g]
                  [rw-register :refer :all]
                  [util :refer [map-vals]]]
            [jepsen [history :as h]
                    [txn :as txn]]
            [clojure.test :refer :all]
            [clj-commons.slingshot :refer [try+ throw+]]))

(def test-check-n
  "Number of iterations for generative tests."
  1000)

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
             (internal-cases h)))))

  (testing "nil read"
    (let [[op :as h] (h/history [(op "rx_rx2")])]
      (is (= [{:op op, :mop [:r :x 2], :expected nil}]
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
(def mop-gen
  "Generator of a micro-op."
  (gen/tuple (gen/elements [:r :w])
             (gen/elements [:x :y :z])
             (gen/elements [0 1 2 3])))

(def op-gen
  "Generates a transaction op."
  (gen/fmap (fn [[process value]]
              (h/op {:index -1
                     :time -1
                     :type :ok
                     :process process
                     :f :txn
                     :value value}))
            (gen/tuple (gen/elements [0 1 2])
                       (gen/vector mop-gen 0 4))))

(defn assocv
  "Assoc for vectors with infinite extent. Adds nils if necessary."
  [v i x]
  (if (<= i (count v))
    (assoc v i x)
    (recur (conj v nil) i x)))

(defn next-free-index
  "Takes a vector v and an index i. Returns the index of the next free
  (nonexistent or nil) element of v, at i or later."
  [v ^long i]
  (if (<= (count v) i)
    i
    (if (nil? (nth v i))
      i
      (recur v (inc i)))))

(defn history-gen-unfold-invoke-ok
  "Takes a vector of steps for history-gen and unfolds them into a vector of
  invoke and ok ops based on the ok-delay."
  [steps]
  (loopr [i   0         ; Our index into the ops vector
          ops []        ; Vector of ops
          busy-til {}]  ; Map of process ID to the next index when it can invoke something
         [[op ok-delay invoke-index-step invoke-time-step ok-index-step
           ok-time-step] steps]
         (let [process (:process op)
               invoke (assoc op
                             :type        :invoke
                             :index-step  invoke-index-step
                             :time-step   invoke-time-step)
               ok     (assoc op
                             :type        :ok
                             :index-step  ok-index-step
                             :time-step   ok-time-step)
               ; Where can we put the invoke?
               invoke-i (next-free-index ops (max i (busy-til process 0)))
               ops (assocv ops invoke-i invoke)
               ; Where can we put the complete?
               ok-i (next-free-index ops (+ invoke-i ok-delay))
               ops (assocv ops ok-i ok)
               ; Which means this process will be busy until that point
               busy-til (assoc busy-til process (max (busy-til process 0)
                                                     ok-i))]
           (recur invoke-i ops busy-til))

         ; Finally, strip out nils.
         (vec (remove nil? ops))))

(defn history-gen-ensure-single-threaded
  "For history-gen, rolls through the history and ensures that no process
  executes something concurrently."
  [ops]
  ; Build a map of process to indexes in the ops vector where that process did something.
  (loopr [ops' []
         ; A map of process to pending completion
         pending {}]
         [{:keys [process] :as op} ops]
         (if (h/invoke? op)
           (if-let [p (get pending process)]
             ; We need to complete this first
             (recur (conj ops' p op)
                    (assoc pending process op))
             ; Idle processes can start an invoke
             (recur (conj ops' op)
                    (assoc pending process op)))
           ; Complete an op
           (recur (conj ops' op)
                  (dissoc pending process)))
         ops'))

(defn history-gen-unroll-indexes-times
  "For history-gen, turn each op's :index-step and :time-step into a monotonic
  :index and :time."
  [ops]
  (loopr [ops'  []
          index 0
          time  0]
          [{:keys [index-step time-step] :as op} ops]
          (let [index' (+ index index-step)
                time'  (+ time time-step)]
            (recur (conj ops' (-> op
                                  (dissoc :index-step :time-step)
                                  (assoc :index index' :time time')))
                   index'
                   time'))
          ops'))

(def history-gen
  "Generates a history of txn operations."
  (gen/fmap
    (fn [steps]
      (-> steps
          history-gen-unfold-invoke-ok
          history-gen-ensure-single-threaded
          history-gen-unroll-indexes-times
          h/history))
    (gen/vector
      (gen/tuple op-gen                                       ; op
                 (gen/large-integer* {:min 1 :max 3})         ; How many ops later does the OK happen?
                 (gen/large-integer* {:min 1, :max 1024})     ; invoke index step
                 (gen/large-integer* {:min 0, :max 1024})     ; invoke time step
                 (gen/large-integer* {:min 1, :max 1024})     ; ok index step
                 (gen/large-integer* {:min 0, :max 1024}))))) ; ok time step

(defn naive-ext-key-graph-search
  "Takes a txn graph g, a key k, and an op. Returns a vector of all downstream
  ops that externally interacted with k--either [op], or operations following
  op in g."
  [g k op]
  (if (contains? (set (ext-keys op)) k)
    ; Done here
    [op]
    ; Search all children
    (reduce into []
            (map (partial naive-ext-key-graph-search g k)
                 (bg/out g op)))))

(defn naive-ext-key-graph
  "A simple model of ext-key-graph that we use for generative tests. Takes a
  transaction graph g, and returns an external key graph: a map of operations a
  to keys k to downstream operations [b1 b2 ...], such that if a externally
  interacted with k, b1, b2, ... did as well, and b1, b2, ... all follow a in
  g."
  ([g]
   (loopr [ekg bm/empty]
          [op (bg/vertices g)]
          (recur
            (bm/put ekg op (naive-ext-key-graph g op)))))
  ; Computes the naive ext key graph for a single operation.
  ([g op]
   (loopr [ekg bm/empty]
          [k (ext-keys op)]
          (recur
            (let [ops (->> (bg/out g op)
                           (map (partial naive-ext-key-graph-search g k))
                           (reduce into []))]
              (if (seq ops)
                (bm/put ekg k ops)
                ekg))))))

(deftest ext-key-graph-spec
  (checking "ext-key-graph" test-check-n
            [h history-gen]
            (pprint h)
            (let [g        (:graph (elle/realtime-graph h))
                  expected (naive-ext-key-graph g)
                  actual   (ext-key-graph g)]
              (println g)
              (println (kg-str expected))
              (is (= expected actual)))))

(defn tig
  "A more compact data structure representation of a transaction graph. A
  Clojure map of index -> #{i1 i2 ...}."
  [g]
  (reduce (fn [tig op]
            (assoc tig (:index op)
                   (into (sorted-set) (map :index (bg/out g op)))))
          (sorted-map)
          (bg/vertices g)))

(deftest ^:focus ext-key-graph-examples
  (let [h (h/history
            [{:index 1, :time 0, :type :invoke, :process 0, :f :txn, :value []}
             {:index 2, :time 0, :type :ok, :process 0, :f :txn, :value []}
             {:index 3, :time 0, :type :invoke, :process 0, :f :txn, :value [[:r :x 0]]}
             {:index 4, :time 0, :type :ok, :process 0, :f :txn, :value [[:r :x 0]]}])
        g        (:graph (elle/realtime-graph h))
        expected (naive-ext-key-graph g)
        actual   (ext-key-graph g)]
    (println "History")
    (mapv prn h)

    (println "\nGraph")
    (pprint (tig g))

    (println "\nExpected")
    (print (kg-str expected))

    (println "\nActual")
    (print (kg-str actual))

    (is (= expected actual))))


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

      (testing "G-single transaction-order"
        (let [
              t1 (op "rx_wy2")
              t2 (op "wx3wy4")
              [t1 t2 :as h] (h/history [t1 t2])
              msg {:cycle [t1 t2 t1]
                   :steps
                   [{:type :rw,
                     :key :x,
                     :value nil,
                     :value' 3,
                     :a-mop-index 0,
                     :b-mop-index 0}
                    {:type :ww,
                     :key :y,
                     :value 4,
                     :value' 2,
                     :a-mop-index 1,
                     :b-mop-index 1}],
                   :type :G-single-item}]
          ; Without explicit transaction order specified, the rw edge between T1 and T2 will not be inferred.
          (is (= {:valid? true}
                 (c {:consistency-models [:serializable]}
                    h)))
          ;; With explicitly specified transaction order, the rw edge will be inferred and G-single should manifest
          (is (= {:valid? false
                  :anomaly-types [:G-single-item]
                  :not       #{:consistent-view :repeatable-read}
                  :anomalies {:G-single-item [msg]}}
                 (c {:consistency-models [:serializable] 
                     ;; Txn commit order: T2 -> T1
                     :transaction-order {0 2 1 1}}
                    h)))          
          ))
    
    (testing "G2-item transaction-order"
      (let [t1 (op "wx1wy2wz3")
            t2 (op "rx1wy5")
            t3 (op "rz3wx4")
            t4 (op "wz7wy8")
            [t1 t2 t3 t4 :as h] (h/history [t1 t2 t3 t4])
            msg {:cycle [t2 t3 t4 t2]
                 :steps
                 [{:type :rw,
                   :key :x,
                   :value 1,
                   :value' 4,
                   :a-mop-index 0,
                   :b-mop-index 1}
                  {:type :rw,
                   :key :z,
                   :value 3,
                   :value' 7,
                   :a-mop-index 0,
                   :b-mop-index 0}
                  {:type :ww,
                   :key :y,
                   :value 8,
                   :value' 5,
                   :a-mop-index 1,
                   :b-mop-index 1}],
                 :type :G2-item}]
        ;; Without explicit transaction order specified, the rw/ww edges will not be inferred.
        (is (= {:valid? true}
               (c {:consistency-models [:serializable]}
                  h)))
        ;; With explicitly specified transaction order, the ww and rw edges will be inferred and G2-item should manifest.
        (is (= {:valid? false
                :anomaly-types [:G2-item]
                :not       #{:repeatable-read}
                :anomalies {:G2-item [msg]}}
               (c {:consistency-models [:serializable] 
                   ;; Txn commit order: T1 -> T3 -> T4 -> T2    
                   :transaction-order {
                                       0 1 
                                       1 4 
                                       2 2 
                                       3 3}}
                  h)))
        ))

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

  (deftest scc-sort-bug-test
    ; Here, linearizable keys tell us the version order went 1, nil, but that
    ; contradicts the initial version order.
    (let [[t1 t1'] (pair (op 0 :ok "rx1"))
          [t2 t2'] (pair (op 0 :ok "rx_"))
          ; Now the version order goes 4, 3 by wfr, but 3,4 by time
          [t3 t3'] (pair (op 0 :ok "rx4wx3"))
          [t4 t4'] (pair (op 0 :ok "wx4"))
          [t1 t1' t2 t2' t3 t3' t4 t4' :as h]
          (h/history [t1 t1' t2 t2' t3 t3' t4 t4'])]
      (is (= {:valid? false
              :anomaly-types [:G1c-realtime :cyclic-versions]
              :not #{:read-uncommitted}
              :anomalies
              {:G1c-realtime
               [{:type :G1c-realtime
                 :cycle [t3' t4' t3']
                 :steps [{:type :realtime
                          :a' t3'
                          :b t4}
                         {:type :wr
                          :key :x
                          :value 4
                          :a-mop-index 0
                          :b-mop-index 0}]}]
               :cyclic-versions
               [{:key :x
                 :scc #{nil 1}
                 :sources [:initial-state :wfr-keys :linearizable-keys]}
                {:key :x
                 :scc #{3 4}
                 :sources [:initial-state :wfr-keys :linearizable-keys]}]}}
             (c {:consistency-models  [:strong-serializable]
                 :wfr-keys?           true
                 :linearizable-keys?  true}
                h)))
              #_(read-history "histories/wr-scc-sort-bug.edn")
              ))

    (deftest cyclic-versions-bug-test
      ; This was a bug in ext-key-graph which inappropriately took the union of
      ; linear sets of dependencies, causing Elle to infer incorrectly that
      ; there were version order cycles. It depended specifically on the iteration order
      ; through the history, which is why we need these *specific* indexes to trigger it.
      ;
      ; Six hours, one word fix: changing from LinearSet to Set. Wow.
      (let [h (h/history
                [{:index 1,   :time 33189116, :type :invoke,  :process 0, :f :txn, :value []}
                 {:index 2,   :time 34621247, :type :ok,      :process 0, :f :txn, :value []}
                 {:index 3,   :time 36022782, :type :invoke,  :process 0, :f :txn, :value [[:r 1 nil]]}
                 {:index 4,   :time 36230324, :type :invoke,  :process 1, :f :txn, :value [[:w 1 4]]}
                 {:index 5,   :time 36827540, :type :invoke,  :process 2, :f :txn, :value []}
                 ; Why is this index special? Why 320 exactly?
                 {:index 320, :time 37708797, :type :ok,      :process 0, :f :txn, :value [[:r 1 nil]]}
                 {:index 322, :time 37894295, :type :ok,      :process 1, :f :txn, :value [[:w 1 4]]}
                 {:index 323, :time 37992467, :type :ok,      :process 2, :f :txn, :value []}
                 {:index 324, :time 38532405, :type :invoke,  :process 0, :f :txn, :value []}
                 {:index 325, :time 39475568, :type :ok,      :process 0, :f :txn, :value []}
                 {:index 326, :time 39956694, :type :invoke,  :process 0, :f :txn, :value [[:r 1 nil]]}
                 {:index 327, :time 40746079, :type :ok,      :process 0, :f :txn, :value [[:r 1 4]]}])
            r (c {:consistency-models [:serializable]
                  :linearizable-keys? true}
                 h)]
        (is (:valid? r))))
)

; This is here for pasting in experimental histories when we hit checker bugs.
; It's a helpful skeleton for refining a test case.
(comment
  (deftest foo-test
    (let [h [

             ]]
      (is (= {:valid? false}
             (check {:additional-graphs  [cycle/realtime-graph]
                     :consistency-models [:snapshot-isolation]
                     :sequential-keys?   true
                     :wfr-keys?          true})
             (h/history h)
             ))))
)

(deftest version-order-test
  (let [h (read-history "histories/cyclic-versions.edn")
        r (check {:consistency-models [:strong-snapshot-isolation]
                  :linearizable-keys? true}
                 h)]
    (pprint r)
    (is (:valid? r))))

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
             (check (checker {:additional-graphs [cycle/process-graph]
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
