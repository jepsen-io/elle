(ns elle.list-append-test
  (:refer-clojure :exclude [test])
  (:require [clojure [pprint :refer [pprint]]
                     [set :as set]
                     [test :refer [deftest is testing]]
                     [walk :as walk]]
            [clojure.java.io :as io]
            [clojure.test.check [generators :as gen]]
            [com.gfredericks.test.chuck.clojure-test :refer
             [checking for-all]]
            [dom-top.core :refer [loopr real-pmap]]
            [elle [core :as elle]
                  [core-test :refer [read-history]]
                  [list-append :refer :all]
                  [graph :as g]
                  [util :refer [map-vals]]]
            [jepsen [history :as h]
                    [txn :as txn]]
            [jepsen.history [sim :as sim]]
            [slingshot.slingshot :refer [try+ throw+]])
  (:import (java.util ArrayList
                      HashMap)))

(defn just-graph
  "Takes ops, makes a history, uses the given analyzer function to construct a
  graph+explainer, extracts just the graph, converts it to Clojure."
  [analyzer ops]
  (->> ops
       h/history
       analyzer
       :graph
       g/->clj
       (into {})))

(defn op
  "Generates an operation from a string language like so:

  ax1       append 1 to x
  ry12      read y = [1 2]
  ax1ax2    append 1 to x, append 2 to x"
  ([string]
   (let [[txn mop] (reduce (fn [[txn [f k v :as mop]] c]
                             (case c
                               \a [(conj txn mop) [:append]]
                               \r [(conj txn mop) [:r]]
                               \x [txn (conj mop :x)]
                               \y [txn (conj mop :y)]
                               \z [txn (conj mop :z)]
                               \t [txn (conj mop :t)]
                               \u [txn (conj mop :u)]
                               (let [e (Long/parseLong (str c))]
                                 [txn [f k (case f
                                             :append e
                                             :r      (conj (or v []) e))]])))
                           [[] nil]
                           string)
         txn (-> txn
                 (subvec 1)
                 (conj mop))]
     {:time 0, :process 0, :type :ok, :f :txn, :value txn}))
  ([process type string]
   (assoc (op string) :process process :type type)))

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
  (is (= {:time 0, :type :ok, :f :txn, :process 0,
          :value [[:append :x 1] [:append :x 2]]}
         (op "ax1ax2"))))

(deftest ww-graph-test
  (let [g (partial just-graph ww-graph)
        [t1 t2 t3 :as h]
        (h/history [(op "ax1")
                    (op "ax2")
                    (op "rx12")])]
    (testing "write-write"
      ; Notice that T3 doesn't depend on T2, because we don't detect wr edges!
      (is (= {t1 #{t2} t2 #{}}
             (g h))))))

(deftest wr-graph-test
  (let [g (partial just-graph wr-graph)]
    (testing "basic read"
      (let [[t1 t2 t3 t4 :as h]
            (h/history [(op "ax1")
                        (op "rx1")
                        (op "ax2")
                        (op "rx12")])]
        ; Note that t2 doesn't precede t3, because the wr graph doesn't encode
        ; anti-dependency edges, and t1 doesn't precede t3, because there are
        ; no ww edges here.
        (is (= {t1 #{t2}, t2 #{}, t3 #{t4}, t4 #{}}
               (g h)))))))

(deftest graph-test
  (let [g (comp (partial just-graph graph) vector)
        [ax1 ax2 ax1ay1 ax1ry1 ax2ay1 ax2ay2 az1ax1ay1 rxay1 ryax1 rx121 rx1ry1 rx1ay2 ry12az3 rz13 rx rx1 rx12 rx12ry1 rx12ry21 :as h]
        (h/history
          [{:process 0, :type :ok, :value [[:append :x 1]]}
           {:process 0, :type :ok, :value [[:append :x 2]]}
           {:process 0, :type :ok, :value [[:append :x 1] [:append :y 1]]}
           {:process 0, :type :ok, :value [[:append :x 1] [:r :y [1]]]}
           {:process 0, :type :ok, :value [[:append :x 2] [:append :y 1]]}
           {:process 0, :type :ok, :value [[:append :x 2] [:append :y 2]]}
           {:process 0, :type :ok, :value [[:append :z 1]
                                           [:append :x 1]
                                           [:append :y 1]]}
           {:process 0, :type :ok, :value [[:r :x nil] [:append :y 1]]}
           {:process 0, :type :ok, :value [[:r :y nil] [:append :x 1]]}
           {:process 0, :type :ok, :value [[:r :x [1 2 1]]]}
           {:process 0, :type :ok, :value [[:r :x [1]] [:r :y [1]]]}
           {:process 0, :type :ok, :value [[:r :x [1]] [:append :y 2]]}
           {:process 0, :type :ok, :value [[:r :y [1 2]] [:append :z 3]]}
           {:process 0, :type :ok, :value [[:r :z [1 3]]]}
           {:process 0, :type :ok, :value [[:r :x nil]]}
           {:process 0, :type :ok, :value [[:r :x [1]]]}
           {:process 0, :type :ok, :value [[:r :x [1 2]]]}
           {:process 0, :type :ok, :value [[:r :x [1 2]] [:r :y [1]]]}
           {:process 0, :type :ok, :value [[:r :x [1 2]] [:r :y [2 1]]]}])]
    (testing "empty history"
      (is (= {} (g))))

    (testing "one append"
      (is (= {} (g ax1))))

    (testing "empty read"
      (is (= {} (g rx))))

    (testing "one append one read"
      (is (= {ax1 #{rx1}, rx1 #{}}
             (g ax1 rx1))))

    (testing "read empty, append, read"
      ; This verifies anti-dependencies.
      ; We need the third read in order to establish ax1's ordering
      (is (= {rx #{ax1} ax1 #{rx1} rx1 #{}}
             (g rx ax1 rx1))))

    (testing "append, append, read"
      ; This verifies write dependencies
      (is (= {ax1 #{ax2}, ax2 #{rx12}, rx12 #{}}
             (g ax2 ax1 rx12))))

    (testing "serializable figure 3 from Adya, Liskov, O'Neil"
      (is (= {az1ax1ay1 #{rx1ay2 ry12az3}
              rx1ay2    #{ry12az3}
              ry12az3   #{rz13}
              rz13      #{}}
             (g az1ax1ay1 rx1ay2 ry12az3 rz13))))

    (testing "G0: write cycle"
      (let [t1 ax1ay1
            t2 ax2ay2
            ; Establishes that the updates from t1 and t2 were applied in
            ; different orders
            t3 rx12ry21]
        (is (= {t1 #{t2 t3}, t2 #{t1 t3}, t3 #{}}
               (g t1 t2 t3)))))

    ; TODO: we should do internal consistency checks here as well--see G1a and
    ; G1b.


    (testing "G1c: circular information flow"
      ; G0 is a special case of G1c, so for G1c we'll construct a cycle with a
      ; ww dependency on x and a wr dependency on y. The second transaction
      ; overwrites the first on x, but the second's write of y is visible to
      ; the first's read.
      (let [t1 ax1ry1
            t2 ax2ay1
            t3 rx12]
        (is (= {t1 #{t2}, t2 #{t3 t1}, t3 #{}}
               (g t1 t2 t3)))))

    (testing "G2: anti-dependency cycle"
      ; Here, two transactions observe the empty state of a key that the other
      ; transaction will append to.
      (is (= {rxay1 #{ryax1 rx1ry1}, ryax1 #{rxay1 rx1ry1}, rx1ry1 #{}}
             (g rxay1 ryax1 rx1ry1)))
      (is (= {:valid? false
              :scc-count 1
              :cycles ["Let:\n  T1 = {:index 8, :time -1, :type :ok, :process 0, :f nil, :value [[:r :y nil] [:append :x 1]]}\n  T2 = {:index 7, :time -1, :type :ok, :process 0, :f nil, :value [[:r :x nil] [:append :y 1]]}\n\nThen:\n  - T1 < T2, because T1 observed the initial (nil) state of :y, which T2 created by appending 1.\n  - However, T2 < T1, because T2 observed the initial (nil) state of :x, which T1 created by appending 1: a contradiction!"]}
             (elle/check {:analyzer graph} (h/history [rxay1 ryax1 rx1ry1])))))

    ; We can't infer anything about an info's nil reads: an :ok read of nil
    ; means we saw the initial state, but an :info read of nil means we don't
    ; know what was observed.
    (testing "info reads"
      ; T1 appends 2 to x after T2, so we can infer T2 < T1.
      ; However, T1's crashed read of y = nil does NOT mean T1 < T2.
      (let [[t1 t2 t3 :as h]
            (h/history [{:type :info, :value [[:append :x 2] [:r :y nil]]}
                        {:type :ok,   :value [[:append :x 1] [:append :y 1]]}
                        {:type :ok,   :value [[:r :x [1 2]] [:r :y [1]]]}])]
        (is (= {t1 #{t3}, t2 #{t3 t1}, t3 #{}}
               (g t1 t2 t3)))))

    ; Special case: when there's only one append for a key, we can trivially
    ; infer the version order for that key, even if we never observe it in a
    ; read: it has to go from nil -> [x].
    (testing "single appends without reads"
      (is (= {rx #{ax1} ax1 #{}} (g rx ax1))))

    (testing "multiple appends without reads"
      ; With two appends, we can't infer a precise order, but we still know ax1
      ; and ax2 both had to come after rx!
      (is (= {rx #{ax1 ax2} ax1 #{} ax2 #{}} (g rx ax1 ax2))))

    (testing "duplicate inserts attempts"
      (let [ax1ry  {:index 0, :type :invoke, :value [[:append :x 1] [:r :y nil]]}
            ay2ax1 {:index 1, :type :invoke, :value [[:append :y 2] [:append :x 1]], :f nil, :time -1, :process nil}
            e (try+ (g ax1ry ay2ax1)
                    false
                    (catch [:type :duplicate-appends] e e))]
        (is (= (h/op ay2ax1) (:op e)))
        (is (= :x (:key e)))
        (is (= 1 (:value e)))))))

(deftest g1a-cases-test
  (testing "empty"
    (is (= nil (g1a-cases (h/history [])))))
  (testing "valid and invalid reads"
    (let [[t2 t3 t1 :as h]
          (h/history [(op "rx1ax2")
                      (op "rx12ry3")
                      {:process 0, :type :fail, :value [[:append :x 1]]}])]
      (is (= [{:op        t2
               :mop       [:r :x [1]]
               :writer    t1
               :element   1}
              {:op        t3
               :mop       [:r :x [1 2]]
               :writer    t1
               :element   1}]
             (g1a-cases h))))))

(deftest g1b-cases-test
  (testing "empty"
    (is (= nil (g1b-cases (h/history [])))))

  (testing "valid and invalid reads"
    ; t1 has an intermediate append of 1 which should never be visible alone.
    (let [[t2 t3 t1 t4 :as h]
          (h/history [(op "rx1")
                      (op "rx12ry3")
                      (op "ax1ax2")
                      (op "rx123")])]
      (is (= [{:op        t2
               :mop       [:r :x [1]]
               :writer    t1
               :element   1}]
             (g1b-cases h)))))

  (testing "internal reads"
    (let [[t1 :as h] (h/history [(op "ax1rx1ax2")])]
      (is (= nil (g1b-cases h))))))

(deftest internal-cases-test
  (testing "empty"
    (is (= {} (internal-cases (h/history [])))))

  (testing "good"
    (is (= {} (internal-cases (h/history
                                [{:process 0,
                                  :type :ok,
                                  :value [[:r :y [5 6]]
                                          [:append :x 3]
                                          [:r :x [1 2 3]]
                                          [:append :x 4]
                                          [:r :x [1 2 3 4]]]}])))))

  (testing "read-append-read"
    (let [[stale bad-prefix extension short-read :as h]
          (h/history [{:process 0, :type :ok, :value [[:r :x [1 2]]
                                                      [:append :x 3]
                                                      [:r :x [1 2]]]}
                      {:process 0, :type :ok, :value [[:r :x [1 2]]
                                                      [:append :x 3]
                                                      [:r :x [0 2 3]]]}
                      {:process 0, :type :ok, :value [[:r :x [1 2]]
                                                      [:append :x 3]
                                                      [:r :x [1 2 3 4]]]}
                      {:process 0, :type :ok, :value [[:r :x [1 2]]
                                                      [:append :x 3]
                                                      [:r :x [1]]]}])]
      (is (= {:internal [{:op stale
                          :mop [:r :x [1 2]]
                          :expected [1 2 3]}
                         {:op bad-prefix
                          :mop [:r :x [0 2 3]]
                          :expected [1 2 3]}
                         {:op extension
                          :mop [:r :x [1 2 3 4]]
                          :expected [1 2 3]}
                         {:op short-read
                          :mop [:r :x [1]]
                          :expected [1 2 3]}]}
           (internal-cases h)))))

  (testing "append-read"
    (let [[disagreement short-read :as h]
          (h/history [{:process 0, :type :ok, :value [[:append :x 3]
                                                      [:r :x [1 2 3 4]]]}
                      {:process 0, :type :ok, :value [[:append :x 3]
                                                      [:r :x []]]}])]
      (is (= {:internal [{:op disagreement
                          :mop [:r :x [1 2 3 4]]
                          :expected ['... 3]}
                         {:op short-read
                          :mop [:r :x []]
                          :expected ['... 3]}]}
           (internal-cases h)))))

  (testing "FaunaDB example"
    (let [[t1 t2 :as h]
          (h/history
            [{:type :invoke, :f :txn, :value [[:append 0 6] [:r 0 nil]]
              :process 1, :index 20, :time 1}
             {:type :ok, :f :txn, :value [[:append 0 6] [:r 0 nil]]
              :process 1, :index 21, :time 2}])]
      (is (= {:internal [{:expected '[... 6],
                          :mop [:r 0 nil],
                          :op t2}]}
             (internal-cases h)))))

  (testing "future read external"
    (let [[t1 t1' :as h]
          (h/history (pair (op "rx012ax1")))]
      (is (= {:future-read [{:op t1'
                             :mop [:r :x [0 1 2]]
                             :element 1}]}
             (internal-cases h)))))

  (testing "future read internal"
    (let [[t1 t1' :as h] (h/history (pair (op "ax1rx01ax0ax3")))]
      (is (= {:future-read [{:op t1'
                             :mop [:r :x [0 1]]
                             :element 0}]}
             (internal-cases h))))))

(defn c
  "Check a history."
  [opts history]
  (-> (check opts history)
      ; We don't care about these; it's kinda redundant.
      (dissoc :also-not)))

(defn cf
  "Checks a file"
  [opts filename]
  (c opts (read-history filename)))

(deftest checker-test
  (testing "G0"
    (let [; A pure write cycle: x => t1, t2; but y => t2, t1
          [t1 t2 t3 :as h]
          (h/history [(op "ax1ay1")
                      (op "ax2ay2")
                      (op "rx12ry21")])
          msg {:cycle [t1 t2 t1]
               :steps
               [
                {:type :ww,
                 :key :x,
                 :value 1,
                 :value' 2,
                 :a-mop-index 0,
                 :b-mop-index 0}
                {:type :ww,
                 :key :y,
                 :value 2,
                 :value' 1,
                 :a-mop-index 1,
                 :b-mop-index 1}
                ]
               :type :G0}]
      ; G1 and G0 both catch this, because technically G0 *is* G1.
      (is (= {:valid? false
              :anomaly-types  [:G0]
              :not            #{:read-uncommitted}
              :anomalies {:G0 [msg]}}
             (c {:consistency-models nil, :anomalies [:G0]} h)))
      (is (= {:valid? false
              :anomaly-types  [:G0]
              :not            #{:read-uncommitted}
              :anomalies {:G0 [msg]}}
             (c {:consistency-models nil, :anomalies [:G1]} h)))
      ; G2 doesn't actually include G0, so it won't.
      (is (= {:valid? true}
             (c {:consistency-models nil, :anomalies [:G2]} h)))))

  (testing "G1a"
    (let [; T2 sees T1's failed write
          t1 {:process 0, :type :fail, :value [[:append :x 1]]}
          t2 (op "rx1")
          [t1 t2 :as h] (h/history [t1 t2])]
      ; Read-uncommitted won't catch this
      (is (= {:valid?         :unknown
              :anomaly-types  [:empty-transaction-graph]
              :anomalies      {:empty-transaction-graph true}
              ; Right now, it'll see that it's not RC/RA, though it won't tell
              ; you WHY.
              :not #{:read-committed}}
             (c {:consistency-models [:read-uncommitted]} h)))
      ; Read-committed will, of course
      (is (= {:valid? false
              :anomaly-types  [:G1a :empty-transaction-graph]
              :not            #{:read-committed}
              :anomalies {:empty-transaction-graph true
                          :G1a [{:op      t2
                                 :writer  t1
                                 :mop     [:r :x [1]]
                                 :element 1}]}}
             (c {:consistency-models [:read-committed]} h)))
      ; Just asking for G2 won't complain about this, though it *will* complain
      ; about the empty transaction graph.
      (is (= {:valid? :unknown
              :anomaly-types [:empty-transaction-graph]
              :anomalies {:empty-transaction-graph true}
              ; Right now, it'll see that it's not RC/RA, though it won't tell
              ; you WHY.
              :not #{:read-committed}}
             (c {:consistency-models nil, :anomalies [:G2]} h)))
      ; But a repeatable-read checker will see it, because they prohibit both
      ; G1 and G2-item.
      (is (= {:valid? false
              :anomaly-types  [:G1a :empty-transaction-graph]
              :not            #{:read-committed}
              :anomalies {:empty-transaction-graph true
                          :G1a [{:op      t2
                                 :writer  t1
                                 :mop     [:r :x [1]]
                                 :element 1}]}}
             (c {:consistency-models [:repeatable-read]} h)))))

  (testing "G1b"
    (let [; T2 sees T1's intermediate write
          [t1 t1'] (pair (op "ax1ax2"))
          [t2 t2'] (pair (op "rx1"))
          [t1 t1' t2 t2' :as h] (h/history [t1 t1' t2 t2'])]
      ; This is not only G1b, since it has an intermediate read, but also
      ; G-single, since rx1 observes ax1 but does not observe ax2!

      ; G0 checker won't catch this
      (is (= {:valid? true} (c {:consistency-models nil, :anomalies [:G0]} h)))
      ; G1 will
      (is (= {:valid? false
              :anomaly-types  [:G1b]
              :not            #{:read-committed}
              :anomalies {:G1b [{:op      t2'
                                 :writer  t1'
                                 :mop     [:r :x [1]]
                                 :element 1}]}}
             (c {:consistency-models nil, :anomalies [:G1]} h)))
      ; G2 catches G-single but won't actually report G1b: even though the
      ; graph covers G1c, we filter out the G1b anomaly since we weren't asked
      ; for it. Still report that it's not read-committed, which is... maybe
      ; questionable. Might change this later?
      (is (= {:valid? false
              :not #{:read-committed}
              :anomaly-types [:G-single-item]}
             (-> (c {:consistency-models nil, :anomalies [:G2]} h)
                 (select-keys [:valid? :not :anomaly-types]))))
      ; But, say, strict-1SR will
      (is (= {:valid? false
              :anomaly-types  [:G-single-item :G1b]
              :not            #{:read-committed}
              :anomalies {:G1b [{:op      t2'
                                 :writer  t1'
                                 :mop     [:r :x [1]]
                                 :element 1}]
                          :G-single-item
                          [{:cycle [t2' t1' t2']
                            :steps
                            [{:type :rw,
                              :key :x,
                              :value 1,
                              :value' 2,
                              :a-mop-index 0,
                              :b-mop-index 1}
                             {:type :wr,
                              :key :x,
                              :value 1,
                              :a-mop-index 0,
                              :b-mop-index 0}],
                            :type :G-single-item}]}}
             (c {:consistency-models [:strict-serializable]} h)))))

  (testing "G1c"
    (let [; T2 writes x after T1, but T1 observes T2's write on y.
          [t1 t2 t3 :as h]
          (h/history [(op "ax1ry1")
                      (op "ax2ay1")
                      (op "rx12ry1")])
          msg {:cycle [t2 t1 t2]
               :steps
               [{:type :wr,
                 :key :y,
                 :value 1,
                 :a-mop-index 1,
                 :b-mop-index 1}
                {:type :ww,
                 :key :x,
                 :value 1,
                 :value' 2,
                 :a-mop-index 0,
                 :b-mop-index 0}],
               :type :G1c}]
      ; G0 won't see this
      (is (= {:valid? true} (c {:consistency-models nil, :anomalies [:G0]} h)))
      ; But G1 will!
      (is (= {:valid? false
              :anomaly-types  [:G1c]
              :not            #{:read-committed}
              :anomalies {:G1c [msg]}}
             (c {:consistency-models nil, :anomalies [:G1]} h)))
      ; G2 won't
      (is (= {:valid? true}
             (c {:consistency-models nil, :anomalies [:G2]} h)))))

  (testing "G-single"
    (let [[t1 t2 t3 :as h]
          (h/history [(op "ax1ay1") ; T1 writes y after T1's read
                      (op "ax2ry")  ; T2 writes x after T1
                      (op "rx12")])
          msg {:cycle [t2 t1 t2]
               :steps
               [{:type :rw,
                 :key :y,
                 :value :elle.list-append/init,
                 :value' 1,
                 :a-mop-index 1,
                 :b-mop-index 1}
                {:type :ww,
                 :key :x,
                 :value 1,
                 :value' 2,
                 :a-mop-index 0,
                 :b-mop-index 0}],
               :type :G-single-item}]
      ; G0 and G1 won't catch this
      (is (= {:valid? true} (c {:consistency-models nil, :anomalies [:G0]} h)))
      (is (= {:valid? true} (c {:consistency-models nil, :anomalies [:G1]} h)))
      ; But G-single and G2 will!
      (is (= {:valid? false
              :anomaly-types [:G-single-item]
              :not           #{:consistent-view :repeatable-read}
              :anomalies {:G-single-item [msg]}}
             (c {:consistency-models nil, :anomalies [:G-single]} h)))
      (is (= {:valid? false
              :anomaly-types [:G-single-item]
              :not           #{:consistent-view :repeatable-read}
              :anomalies {:G-single-item [msg]}}
             (c {:consistency-models nil, :anomalies [:G2]} h)))))

  (testing "G2"
    (let [; A pure anti-dependency cycle
          [t1 t2 :as h]
          (h/history [(op "ax1ry")
                      (op "ay1rx")])]
      ; G0 and G1 won't catch this
      (is (= {:valid? true} (c {:consistency-models nil, :anomalies [:G0]} h)))
      (is (= {:valid? true} (c {:consistency-models nil, :anomalies [:G1]} h)))
      ; Nor will checkers for, say, read committed.
      (is (= {:valid? true} (c {:consistency-models [:read-committed]} h)))
      ; But G2 will
      (let [err {:valid? false
                 :anomaly-types  [:G2-item]
                 :not            #{:repeatable-read}
                 :anomalies
                 {:G2-item [{:cycle [t1 t2 t1]
                             :steps
                             [
                              {:type :rw,
                               :key :y,
                               :value :elle.list-append/init,
                               :value' 1,
                               :a-mop-index 1,
                               :b-mop-index 0}
                              {:type :rw,
                               :key :x,
                               :value :elle.list-append/init,
                               :value' 1,
                               :a-mop-index 1,
                               :b-mop-index 0}
                              ]
                             :type :G2-item}]}}]
      (is (= err (c {:consistency-models nil, :anomalies [:G2]} h)))
      ; As will a serializable checker.
      (is (= err (c {:consistency-models [:serializable]} h)))
      ; And repeatable-read
      (is (= err (c {:consistency-models [:repeatable-read]} h)))
      )))

  (testing "Strong SI violation"
    (let [; T1 anti-depends on T2, but T1 happens first in wall-clock order.
          t0  {:process 0, :index 0, :type :invoke, :value [[:append :x 1]]}
          t0' {:process 0, :index 1, :type :ok,     :value [[:append :x 1]]}
          t1  {:process 1, :index 2, :type :invoke, :value [[:append :x 2]]}
          t1' {:process 1, :index 3, :type :ok,     :value [[:append :x 2]]}
          t2  {:process 2, :index 4, :type :invoke, :value [[:r :x nil]]}
          t2' {:process 2, :index 5, :type :ok,     :value [[:r :x [1]]]}
          t3  {:process 3, :index 6, :type :invoke, :value [[:r :x nil]]}
          t3' {:process 3, :index 7, :type :ok,     :value [[:r :x [1 2]]]}
                     [t0 t0' t1 t1' t2 t2' t3 t3' :as h]
          (h/history [t0 t0' t1 t1' t2 t2' t3 t3'])]
      ; G2 won't catch this by itself
      (is (= {:valid? true}
             (c {:consistency-models nil, :anomalies [:G2]} h)))
      ; Nor will a serializable checker
      (is (= {:valid? true}
             (c {:consistency-models [:serializable]} h)))
      ; But it will if we ask for strict-serializable.
      (is (= {:valid?         false
              :anomaly-types  [:G-single-item-realtime]
              :not            #{:strong-snapshot-isolation}
              :anomalies
              {:G-single-item-realtime
               [{:cycle [t2' t1' t2']
                 :steps
                 [{:type :rw,
                   :key :x,
                   :value 1,
                   :value' 2,
                   :a-mop-index 0,
                   :b-mop-index 0}
                  {:type :realtime,
                   :a' t1'
                   :b  t2}],
                 :type :G-single-item-realtime}]}}
             (c {:consistency-models [:strict-serializable]}
                h)))))

  (testing "Strong Session SI violation"
    (let [; T1 anti-depends on T2, but T1 happens first in process order.
          t0  {:process 0, :index 0, :type :invoke, :value [[:append :x 1]]}
          t0' {:process 0, :index 1, :type :ok,     :value [[:append :x 1]]}
          t1  {:process 1, :index 2, :type :invoke, :value [[:append :x 2]]}
          t1' {:process 1, :index 3, :type :ok,     :value [[:append :x 2]]}
          t2  {:process 1, :index 4, :type :invoke, :value [[:r :x nil]]}
          t2' {:process 1, :index 5, :type :ok,     :value [[:r :x [1]]]}
          t3  {:process 2, :index 6, :type :invoke, :value [[:r :x nil]]}
          t3' {:process 2, :index 7, :type :ok,     :value [[:r :x [1 2]]]}
                     [t0 t0' t1 t1' t2 t2' t3 t3' :as h]
          (h/history [t0 t0' t1 t1' t2 t2' t3 t3'])]
      ; A serializable checker won't catch this
      (is (= {:valid? true}
             (c {:consistency-models [:serializable]} h)))
      ; But it will if we ask for strict-serializable.
      (is (= {:valid?         false
              :anomaly-types  [:G-single-item-process]
              :not            #{:strong-session-snapshot-isolation}
              :anomalies
              {:G-single-item-process
               [{:cycle [t2' t1' t2']
                 :steps
                 [{:type :rw,
                   :key :x,
                   :value 1,
                   :value' 2,
                   :a-mop-index 0,
                   :b-mop-index 0}
                  {:type :process
                   :process 1}]
                 :type :G-single-item-process}]}}
             (c {:consistency-models [:strong-session-snapshot-isolation]}
                h)))))

  (testing "G-nonadjacent-process"
    ; This one was submitted by Tsunaou. It depends on a combination of
    ; process order and nonadjacent RW edges, but our checker, until recently,
    ; only knew about G-single-realtime.
    ; https://github.com/jepsen-io/elle/issues/17
    (let [; wr: observes t3's append on z
          t0  {:process 0, :index 0, :type :invoke, :value [[:r :x nil] [:r :z nil]]}
          t0' {:process 0, :index 1, :type :ok,     :value [[:r :x nil] [:r :z [1]]]}
          ; rw: t0 did not see the append to x
          t1  {:process 1, :index 2, :type :invoke, :value [[:append :x 1]]}
          t1' {:process 1, :index 3, :type :ok,     :value [[:append :x 1]]}
          ; process: still p1
          t2  {:process 1, :index 4, :type :invoke, :value [[:r :z nil]]}
          t2' {:process 1, :index 5, :type :ok,     :value [[:r :z nil]]}
          ; rw: t2 did not observe append of z.
          t3  {:process 2, :index 6, :type :invoke, :value [[:append :z 1]]}
          t3' {:process 2, :index 7, :type :ok,     :value [[:append :z 1]]}
                     [t0 t0' t1 t1' t2 t2' t3 t3' :as h]
          (h/history [t0 t0' t1 t1' t2 t2' t3 t3'])]
      ; A serializable checker won't catch this
      (is (= {:valid? true}
             (c {:consistency-models [:serializable]} h)))
      ; But it will if we ask for strong session SI.
      (is (= {:valid?         false
              :anomaly-types  [:G-nonadjacent-item-process]
              :not            #{:strong-session-snapshot-isolation}
              :anomalies
              {:G-nonadjacent-item-process
               [{:cycle [t2' t3' t0' t1' t2']
                 :steps [{:type :rw, :key :z, :value :elle.list-append/init
                          :value' 1
                          :a-mop-index 0
                          :b-mop-index 0}
                         {:type :wr
                          :key :z
                          :value 1
                          :a-mop-index 0
                          :b-mop-index 1}
                         {:type :rw,
                          :key :x
                          :value :elle.list-append/init
                          :value' 1
                          :a-mop-index 0
                          :b-mop-index 0}
                         {:type :process, :process 1}
                         ]
                 :type :G-nonadjacent-item-process}]}}
             (c {:consistency-models [:strong-session-snapshot-isolation]}
                h)))))

  (testing "contradictory read orders"
    (let [t1 (op "ax1ry1")  ; append to 1, read t3's ay1
          t2 (op "ax2")     ; after t1, t2 appends
          t3 (op "ax3ay1")  ; after t2, t3 appends
          t4 (op "rx13")
          t5 (op "rx123")
          [t1 t2 t3 t4 t5 :as h]
          (h/history (h/strip-indices [t1 t2 t3 t4 t5]))]
      ; Delete output files
      (->> (file-seq (io/file "test-output"))
           reverse
           (mapv io/delete-file))
      (is (= {:valid? false
              :anomaly-types [:G1c :incompatible-order]
              :not           #{:read-committed}
              :anomalies
              {:incompatible-order [{:key :x, :values [[1 3] [1 2 3]]}]
               :G1c [{:cycle [t3 t1 t2 t3]
                      :steps
                      [{:type        :wr,
                        :key         :y,
                        :value       1,
                        :a-mop-index 1,
                        :b-mop-index 1}
                       {:type        :ww
                        :key         :x
                        :value       1
                        :value'      2
                        :a-mop-index 0
                        :b-mop-index 0}
                       {:type        :ww
                        :key         :x
                        :value       2
                        :value'      3
                        :a-mop-index 0,
                        :b-mop-index 0}]
                      :type :G1c}]}}
             (c {:consistency-models nil
                 :anomalies [:G1]
                 :directory "test-output"}
                h)))
      ; Check that we wrote the file
      (is (= "<html><head><style>th { text-align: left; }</style></head><body><h1>All Reads of :x</h1><table><thead><tr><th>Index</th><th>Time (s)</th><th>Process</th><th>Fun</th><th colspan=\"32\">Value</th></tr></thead><tbody><tr><td>3</td><td>0.00</td><td>0</td><td>txn</td><td>1</td><td style=\"background: #d6aa9d\">3</td></tr><tr><td>4</td><td>0.00</td><td>0</td><td>txn</td><td>1</td><td>2</td><td>3</td></tr></tbody></table></body></html>"
             (slurp "test-output/incompatible-order/:x.html")))
      ))

  (testing "dirty update"
    (testing "none"
      (let [[t1 :as h] (h/history [(op 0 :fail "ax1")])]
        (is (= {:valid?         :unknown
                :anomaly-types  [:empty-transaction-graph]
                :not            #{}
                :anomalies      {:empty-transaction-graph true}}
               (c {:consistency-models nil, :anomalies [:dirty-update]} h)))))

    (testing "direct"
      (let [[t1 t2 t3 :as h] (h/history [(op 0 :fail "ax1")
                                         (op 1 :ok   "ax2")
                                         (op 2 :ok   "rx12")])]
        (is (= {:valid? false
                :anomaly-types [:dirty-update]
                :not           #{:read-committed}
                :anomalies {:dirty-update [{:key        :x
                                            :values     [1 2]
                                            :txns       [t1 '... t2]}]}}
               (c {:consistency-models nil, :anomalies [:dirty-update]} h)))))

    (testing "indirect"
      (let [[t1 t2 t3 t4 :as h]
            (h/history [(op 0 :fail "ax1")
                        (op 1 :info "ax2")
                        (op 2 :ok   "ax3")
                        (op 3 :ok   "rx123")])]
        (is (= {:valid? false
                :anomaly-types [:dirty-update]
                :not           #{:read-committed}
                :anomalies {:dirty-update [{:key        :x
                                            :values     [1 2 3]
                                            :txns       [t1 '... t3]}]}}
               (c {:consistency-models nil, :anomalies [:dirty-update]} h))))))

  (testing "duplicated elements"
    ; This is also an instance of G1c.
    (let [t1 (op "ax1ry1") ; read t2's write of y
          t2 (op "ax2ay1")
          t3 (op "rx121")
          [t1 t2 t3 :as h] (h/history (h/strip-indices [t1 t2 t3]))]
      (is (= {:valid? false
              :anomaly-types [:G1c :duplicate-elements]
              :not           #{:read-uncommitted}
              :anomalies
              {:duplicate-elements [{:op t3
                                     :mop [:r :x [1 2 1]]
                                     :duplicates {1 2}}]
               :G1c [{:cycle [t2 t1 t2],
                      :steps
                      [{:type :wr,
                        :key :y,
                        :value 1,
                        :a-mop-index 1,
                        :b-mop-index 1}
                       {:type :ww,
                        :key :x,
                        :value 1,
                        :value' 2,
                        :a-mop-index 0,
                        :b-mop-index 0}],
                      :type :G1c}]}}
             ; We flag this as an instance of G-single, because the x = [1 2 1]
             ; read looks like 1 was appended most recently. Whether you want
             ; consider this "real" seems up for debate, cuz duplicate elements
             ; break everything. Let's do read-committed for now to avoid
             ; seeing it.
             (c {:consistency-models [:read-committed]} h)))))

  (testing "internal consistency violation"
    (let [[t1 t2 :as h] (h/history [(op "ax1ax2ax4")
                                    (op "ax3rx1234")])]
      (is (= {:valid?         false
              :anomaly-types  [:internal]
              ; Read-atomic ruled out by internal, read-uncommitted by the G0.
              :not            #{:read-uncommitted}
              :anomalies      {:internal [{:op t2
                                           :mop [:r :x [1 2 3 4]]
                                           :expected '[... 3]}]}}
             ; There's a G0 here too, but we don't care.
             (c {:consistency-models nil, :anomalies [:internal]} h))))))

(deftest unobserved-write-test
  ; When we see [:r :x [1 2]], and 1 was written by t1, 2 written by t2, and 3
  ; written by t3, we can infer a dependency not only from the transaction 1 ->
  ; 2 but *also* from 2 -> 3: transactions which are not observed in the
  ; longest read must fall after the transaction which generated that value!
  ;
  ; To test this, we perform writes of 1, 2, and 3 to both x and y, but let y
  ; fail to observe 1.
  (let [[w1 w1'] (pair (op "ax1ay1"))
        [w2 w2'] (pair (op "ax2ay2"))
        [w3 w3'] (pair (op "ax3ay3"))
        [rx rx'] (pair (op "rx12"))
        [ry ry'] (pair (op "ry2"))
                   [w1 w2 w3 rx ry w1' w2' w3' rx' ry' :as h]
        (h/history [w1 w2 w3 rx ry w1' w2' w3' rx' ry'])]
    ; w1 -ww-> w2, by rx12
    ; w2 -ww-> w1, by ry2
    ; ry -rw-> w1, since y fails to observe w1
    ; w3 is a red herring; just there to create multiple final edges
    (is (= {:valid?         false
            :anomaly-types  [:G-single-item :G0]
            :anomalies
            ; We know this is G-single because ry -rw-> w1 -ww-> w2 -wr-> ry
            {:G-single-item
             [{:cycle [ry' w1' w2' ry']
               :steps
               [{:type :rw,
                 :key :y,
                 :value 2,
                 :value' 1,
                 :a-mop-index 0,
                 :b-mop-index 1}
                {:type :ww,
                 :key :x,
                 :value 1,
                 :value' 2,
                 :a-mop-index 0,
                 :b-mop-index 0}
                {:type :wr,
                 :key :y,
                 :value 2,
                 :a-mop-index 1,
                 :b-mop-index 0}],
               :type :G-single-item}],
             ; But worse, it's G0 because w2 -ww-> w1 -ww->w2
             :G0
             [{:cycle [w2' w1' w2']
               :steps
               [{:type :ww,
                 :key :y,
                 :value 2,
                 :value' 1,
                 :a-mop-index 1,
                 :b-mop-index 1}
                {:type :ww,
                 :key :x,
                 :value 1,
                 :value' 2,
                 :a-mop-index 0,
                 :b-mop-index 0}]
               :type :G0}]},
            :not #{:read-uncommitted}}
           (-> (c {:consistency-models [:serializable]} h)
               (dissoc :also-not))))))

(deftest repeatable-read-test
  ; This is a G2-item, by virtue of its only cycle being two anti-dependency
  ; edges. We shouldn't be able to detect this with read-committed, but
  ; repeatable-read should fail.
  (let [t1 (op "rxay1")
        t2 (op "ryax1")
        [t1 t2 :as h] (h/history [t1 t2])]
    (is (= {:valid? true}
           (c {:consistency-models [:read-committed]} h)))
    (is (= {:valid?         false
            :not            #{:repeatable-read}
            :anomaly-types  [:G2-item]
            :anomalies {:G2-item [{:cycle
                                   [t1 t2 t1]
                                   :steps
                                   [
                                    {:type :rw,
                                     :key :x,
                                     :value :elle.list-append/init,
                                     :value' 1,
                                     :a-mop-index 0,
                                     :b-mop-index 1}
                                    {:type :rw,
                                     :key :y,
                                     :value :elle.list-append/init,
                                     :value' 1,
                                     :a-mop-index 0,
                                     :b-mop-index 1}
                                    ],
                                   :type :G2-item}]}}
           (c {:consistency-models [:repeatable-read]} h)))))

(deftest ^:perf huge-scc-test
  (let [r (cf {} "histories/huge-scc.edn")]
    ; There's a full explanation here but... it's long, and all we care about
    ; is that we can fall back to saying SOMETHING about this enormous SCC.
    (is (not (:valid? r)))
    (is (= #{:strong-snapshot-isolation} (:not r)))
    (is (= [:G2-item-realtime
            :cycle-search-timeout
            :strong-snapshot-isolation-cycle-exists]
           (:anomaly-types r)))
    (let [cst (-> r :anomalies :cycle-search-timeout first)]
      ; This might change if we get faster or adjust timeouts
      (is (= []                      (:does-not-contain cst)))
      (is (= :G-single-item-realtime (:anomaly-spec-type cst)))
      (is (number?                   (:scc-size cst))))))

(deftest G-nonadjacent-test
  ; For G-nonadjacent, we need two rw edges (just one would be G-single), and
  ; they can't be adjacent, so that's four edges altogether.
  (let [[t1 t1'] (pair (op "ax1"))
        [t2 t2'] (pair (op "rx1ry"))
        [t3 t3'] (pair (op "ay1"))
        [t4 t4'] (pair (op "ry1rx"))
        h (h/history [t1 t1' t2 t2' t3 t3' t4 t4'])]
    (is (= {:valid?         false
            :not            #{:snapshot-isolation :repeatable-read}
            :anomaly-types  [:G-nonadjacent-item]
            :anomalies      {:G-nonadjacent-item
                             [{:cycle (mapv h [7 1 3 5 7])
                               :steps [
                                       {:type :rw,
                                        :key :x,
                                        :value :elle.list-append/init,
                                        :value' 1,
                                        :a-mop-index 1,
                                        :b-mop-index 0}
                                       {:type :wr,
                                        :key :x,
                                        :value 1,
                                        :a-mop-index 0,
                                        :b-mop-index 0}
                                       {:type :rw,
                                        :key :y,
                                        :value :elle.list-append/init,
                                        :value' 1,
                                        :a-mop-index 1,
                                        :b-mop-index 0}
                                       {:type :wr,
                                        :key :y,
                                        :value 1,
                                        :a-mop-index 0,
                                        :b-mop-index 0}
                                       ]
                               :type :G-nonadjacent-item}]}}
                             (c {} h))))

  ; We should *not* detect a cycle like rw rw wr rw wr, because two of the rw
  ; edges are adjacent.
  (let [[t1 t1'] (pair (op "rx5ay1")) ; wr: observes ax5
        [t2 t2'] (pair (op "ryaz2"))  ; rw: fails to observe ay1
        [t3 t3'] (pair (op "rzat3"))  ; rw: fails to observe az2
        [t4 t4'] (pair (op "rt3au4")) ; wr: observes at3
        [t5 t5'] (pair (op "ruax5"))  ; rw: fails to observe au4
        h (h/history [t1 t1' t2 t2' t3 t3' t4 t4' t5 t5'])]
    (is (= {:valid? true} (c {:consistency-models [:snapshot-isolation]} h)))))

(deftest lost-update-test
  ; For a lost update, we need two transactions which read the same value (e.g.
  ; 0) of some key (e.g. x) and both append to x.
  (let [[t0 t0'] (pair (op "ax0"))
        [t1 t1'] (pair (op "rx0ax1"))
        [t2 t2'] (pair (op "rx0ax2"))
        [t0 t0' t1 t1' t2 t2' :as h] (h/history [t0 t0' t1 t1' t2 t2'])]
    (is (= {:valid?         false
            :not            #{:update-atomic :cursor-stability}
            :anomaly-types  [:G2-item :lost-update]
            :anomalies      {:lost-update
                             [{:key   :x
                               :value [0]
                               :txns  [t1' t2']}]
                             ; We're also clever enough to infer a rw-rw cycle
                             ; here because neither t1 nor t2 saw each other's
                             ; effects, making this G2-item
                             :G2-item
                             [{:cycle [t2' t1' t2']
                               :steps [
                                       {:type :rw,
                                        :key :x,
                                        :value 0,
                                        :value' 1,
                                        :a-mop-index 0,
                                        :b-mop-index 1}
                                      {:type :rw,
                                        :key :x,
                                        :value 0,
                                        :value' 2,
                                        :a-mop-index 0,
                                        :b-mop-index 1}
                                       ],
                               :type :G2-item}]}}
           (c {} h))))

  ; It's not illegal for a single txn to write over a read twice though
  (testing "one txn, double write"
    (let [[t0 t0'] (pair (op "rxax1ax2"))
          ; Just to avoid empty txn graphs
          [t1 t1'] (pair (op "rx12"))
          h        (h/history [t0 t0' t1 t1'])]
      (is (= {:valid? true}
             (c {} h))))))

(deftest wr-process-test
  ; An anomaly reported in https://github.com/jepsen-io/elle/issues/21. Elle
  ; detected this as a violation of strong serializability, but did not
  ; originally consider it a violation of strong session SI
  (let [[t0 t0' t1 t1' t2 t2' :as h]
        (h/history
          [{:process 1, :type :invoke, :f :txn, :value [[:r :x] [:append :y 1]], :index 0}
           {:process 1, :type :ok, :f :txn, :value [[:r :x [1]] [:append :y 1]], :index 1}
           {:process 2, :type :invoke, :f :txn, :value [[:r :y]], :index 2}
           {:process 2, :type :ok, :f :txn, :value [[:r :y [1]]], :index 3}
           {:process 2, :type :invoke, :f :txn, :value [[:append :x 1]], :index 4}
           {:process 2, :type :ok, :f :txn, :value [[:append :x 1]], :index 5}])]
    ; t0 -wr-> t1 -process-> t2 -wr-> t1
    (is (= {:valid? false
            :anomaly-types [:G1c-process],
           :anomalies
           {:G1c-process
            [{:cycle [t2' t0' t1' t2']
              :steps
              [
               {:type :wr,
                :key :x,
                :value 1,
                :a-mop-index 0,
                :b-mop-index 0}
               {:type :wr,
                :key :y,
                :value 1,
                :a-mop-index 1,
                :b-mop-index 0}
               {:type :process, :process 2}
               ],
              :type :G1c-process}]},
           :not #{:strong-session-read-committed}}
           (c {:consistency-models [:strong-session-snapshot-isolation]} h)))))

(deftest rr-g-single-item-test
  ; Repeatable Read prohibits some, but not all, G-single anomalies. This
  ; prevented us from identifying repeatable read violations when all such
  ; violations were G-single. We now have a special G-single-item anomaly which
  ; does not involve predicates.
  (let [[t1 t1'] (pair (op "ax1ay1"))  ; rw: appends y=1 after t2 reads
        [t2 t2'] (pair (op "rx1ry")) ; wr: observes t1's append of 1 to x
        [t1 t1' t2 t2' :as h] (h/history [t1 t1' t2 t2'])
        r (c {:consistency-models [:repeatable-read]} h)]
    (is (= {:valid? false,
            :anomaly-types [:G-single-item],
            :anomalies
            {:G-single-item
             [{:cycle [t2' t1' t2']
               :steps
               [{:type :rw,
                 :key :y,
                 :value :elle.list-append/init,
                 :value' 1,
                 :a-mop-index 1,
                 :b-mop-index 1}
                {:type :wr, :key :x, :value 1, :a-mop-index 0, :b-mop-index 0}],
               :type :G-single-item}]},
            :not #{:consistent-view :repeatable-read}}
           r))))

(deftest rr-g-nonadjacent-item-test
  ; Repeatable Read prohibits some, but not all, G-nonadjacent anomalies. This
  ; prevented us from identifying repeatable read violations when all such
  ; violations were G-nonadjacent. We now have a special G-nonadjacent-item
  ; anomaly which does not involve predicates.
  (let [[t1 t1' t2 t2' t3 t3' t4 t4' :as h]
        (h/history (mapcat (comp pair op)
                           ["ax1at1"     ; rw: overwrites t4's read of t=nil
                            "rx1ry"      ; wr: observes t1's append to x
                            "ay1az2"     ; rw: overwrites t2's read of y=nil
                            "rz2rt"]))    ; wr: observes t3's append to z
        r (c {:consistency-models [:repeatable-read]} h)]
    (is (= {:valid? false,
            :anomaly-types [:G-nonadjacent-item],
            :anomalies
            {:G-nonadjacent-item
             [{:cycle [t4' t1' t2' t3' t4']
               :steps [
                       {:type :rw,
                        :key :t,
                        :value :elle.list-append/init,
                        :value' 1,
                        :a-mop-index 1,
                        :b-mop-index 1}
                       {:type :wr,
                        :key :x,
                        :value 1,
                        :a-mop-index 0,
                        :b-mop-index 0}
                       {:type :rw,
                        :key :y,
                        :value :elle.list-append/init,
                        :value' 1,
                        :a-mop-index 1,
                        :b-mop-index 0}
                       {:type :wr,
                        :key :z,
                        :value 2,
                        :a-mop-index 1,
                        :b-mop-index 0}
                       ]
               :type :G-nonadjacent-item}]}
            :not #{:repeatable-read :snapshot-isolation}}
           r))))

(deftest future-read-test
  ; When a transaction performs an external read of its own external writes, we
  ; consider that also a violation of internal consistency. Why? Writes are
  ; unique.
  (let [[t0 t0' :as h]
        (h/history
          [{:process 0, :type :invoke, :f :txn, :value [[:r :x [1]] [:append :x 1]]}
           {:process 0, :type :ok,     :f :txn, :value [[:r :x [1]] [:append :x 1]]}])]
  (is (= {:valid? false
          :anomaly-types [:empty-transaction-graph :future-read],
          :anomalies
          {:empty-transaction-graph true
           :future-read
           [{:op t0'
             :mop [:r :x [1]]
             :element 1}]}
          :not #{:read-committed}}
         (c {:consistency-models [:read-committed]} h)))))

(deftest intermediate-sequential-extension-test
  ; An experiment with sequential extension incorrectly left intermediate
  ; vertices present in the graph, causing us to claim e.g. SI violations which
  ; did not actually exist.
  (let [r (cf {:consistency-models [:snapshot-isolation :repeatable-read]}
              "histories/si-without-g-single.edn")]
    (is (= [:G2-item] (:anomaly-types r)))
    (is (= #{:repeatable-read} (:not r)))))

(deftest unfindable-g-single
  ; NOTE: This test depends on performance: if Elle gets faster, it may start
  ; failing. Tune up n and noise-n until you start getting timeouts again.
  ;
  ; In this test, we construct a single G-single cycle awash in a sea of
  ; spurious G2-item cycles. This cycle times out our G-single search, but our
  ; cycle-exists pass can prove that a G-single or weaker must exist by finding
  ; an SCC.
  (let [n          1000
        noise-n    30
        ring (for [i (range n)]
                {:type :ok
                 :process 0
                 :value [; We append 0, 1, 2, ... to get a ww chain
                         [:append :ring i]
                         (condp = i
                          ; First one writes :anti
                          0 [:append :anti :first]

                          ; Last one fails to read anti; that's a G-single
                          (dec n) [:r :anti nil]

                          ; Everyone else does noop writes
                          [:append i 0])]})
        ; To see the ring, we need a version order on :ring
        ring-vo-read [{:type    :ok
                       :process 1
                       :value   [[:r :ring (vec (range n))]]}]
        ; Now we flood the history with appends of integer keys dangling off
        ; the ring, to slow down cycle BFS. They terminate in a read of key i,
        ; to establish the version order of i, and a rw-rw hop to the first op
        ; in the ring. This means they have a *non* G-single cycle, so they
        ; won't be pruned by our initial SCC restriction pass.
        noise (for [i (range 1 (dec n))
                    j (range 1 noise-n)]
                (let [penultimate? (= j (- noise-n 2))
                      last?        (= j (dec noise-n))]
                  {:type    :ok
                   :process 2
                   :value
                   (cond penultimate?
                         [; Penultimate does a read of i so we have an order
                          [:r i (vec (range (- noise-n 2)))]
                          ; And also a read of a special anti-i key, so we can
                          ; rw to the last.
                          [:r [:anti i] nil]]

                         last?
                         [; Last writes that special anti-i key
                          [:append [:anti i] 0]
                          ; Last does a read of :ring just prior to the first
                          ; ring entry
                          [:r :ring nil]]

                         ; Every other link are just appends: a ww chain
                         true
                         [[:append i j]])}))

        h (->> (concat ring ring-vo-read noise)
               (mapcat pair)
               h/history)
        res (c {:consistency-models [:snapshot-isolation]} h)]
    ;(println "G-single SCC")
    ;(pprint (->> res :anomalies :snapshot-isolation-cycle-exists first :scc
    ;             (mapv (partial h/get-index h))
    ;             (mapv :value)))
    (is (= {:valid?         false
            :not            #{:snapshot-isolation
                              ; TODO: our clever little search system finds a
                              ; G2-item even though we didn't ask it to, and
                              ; although it won't *show* that in the output...
                              ; it still knows.
                              :repeatable-read}
            :anomaly-types  [:PL-SI-cycle-exists :cycle-search-timeout]
            :anomalies      {:PL-SI-cycle-exists
                             [{:type      :PL-SI-cycle-exists
                               :not       :snapshot-isolation
                               :subgraph  [:extension [:union :ww :wwp :wr :wrp]
                                           [:union :rw :rwp]]
                               ; Note that we don't include the linchpin txn,
                               ; because of our sequential extension trick.
                               :scc-size  (dec n)
                               :scc       (set (map #(inc (* 2 %))
                                                    (range (dec n))))}]
                             :cycle-search-timeout
                              [{:type :cycle-search-timeout,
                                :anomaly-spec-type :G-single-item,
                                :does-not-contain [],
                                :scc-size (dec (/ (count h) 2))}]
                             }}
           res))))

;; Generative tests

(deftest sim-prefix-test
  ; A short prefix-consistent history has all kinds of errors
  (let [h  (:history (sim/run {:db    :prefix
                               :limit 32}))
        r (c {:consistency-models [:serializable]} h)]

    (is (= [:G0 :incompatible-order] (:anomaly-types r)))
    ; Lost updates yields incompatible orders
    (is (= [{:key 8, :values [[1 2 3 4 8] [1 2 3 4 5]]}
            {:key 9, :values [[3] [1]]}]
           (:incompatible-order (:anomalies r))))
    ; 35 [[:append 8 6] [:r 8 [1 2 3 4 6]] [:r 9 [3 4 5 6 7 10]] [:append 8 7]]
    ; 57 [[:append 8 12] [:append 9 22] [:append 8 13]]
    ; 62 [[:append 9 26] [:r 9 [3 4 5 6 7 10 13 14 17 18 22 26]] [:r 9 [3 4 5 6 7 10 13 14 17 18 22 26]]]
    ; 23 [[:append 8 4] [:r 8 [1 2 3 4]] [:append 9 9]]
    (is (= {:type :G0
            :cycle (mapv h [35 57 62 23 35])
            :steps [{:type :ww
                     :key 8
                     :value 7
                     :value' 12     ; 12 never appears in key 8, must follow 7
                     :a-mop-index 3
                     :b-mop-index 0}
                    {:type :ww
                     :key 9
                     :value 22
                     :value' 26     ; ... 22 26
                     :a-mop-index 1
                     :b-mop-index 0}
                    {:type :ww,
                     :key 9,
                     :value 26,
                     :value' 9,    ; 9 missing from longest read
                     :a-mop-index 0,
                     :b-mop-index 2}
                    {:type :ww,
                     :key 8,
                     :value 4,
                     :value' 6,    ; [1 2 3 4 6]
                     :a-mop-index 0,
                     :b-mop-index 0}]}
           (first (:G0 (:anomalies r)))))
    ;(mapv prn h)
    ;(pprint r)
    ))

(deftest sim-si-test
  ; A snapshot isolation history will exhibit g2-item
  (let [h (:history (sim/run {:db          :si
                              :limit       20
                              :concurrency 10}))
        r (c {:consistency-models [:serializable]} h)]
    ;(mapv (comp prn h) [18 10 22])
    (is (= {:valid? false,
            :anomaly-types [:G2-item],
            :anomalies
            {:G2-item
             [{:cycle (mapv h [18 10 22 18])
               :steps
               [; doesn't see 10's append of 5 to 9
                {:type :rw,
                 :key 9,
                 :value :elle.list-append/init,
                 :value' 5,
                 :a-mop-index 1,
                 :b-mop-index 0}
                ; writes of 9 are visible to 22
                {:type :wr, :key 9, :value 6, :a-mop-index 1, :b-mop-index 0}
                ; failed to observe 18's append to 6
                {:type :rw,
                 :key 6,
                 :value :elle.list-append/init,
                 :value' 1,
                 :a-mop-index 1,
                 :b-mop-index 0}],
               :type :G2-item}]},
            :not #{:repeatable-read}}
           r))))

(deftest sim-ssi-test
  ; A serializable snapshot isolation history won't have any errors
  (let [h (:history (sim/run {:db          :ssi
                              :limit       1000
                              :concurrency 5}))
        r (c {:consistency-models [:strict-serializable]} h)]
    (is (= {:valid? true} r))))

;; Perf testing

(deftest ^:perf scc-search-perf-test
  ; A case where even small SCCs caused the cycle search to time out
  (time (cf {:consistency-models [:strong-snapshot-isolation]}
            "histories/small-slow-scc.edn")))

(defn perf-check
  "Takes a test name, the time it started generating the history, options for
  check, and the history. Checks it and prints out perf statistics. Returns
  analysis."
  [test-name t0 opts h]
  (let [n  (/ (count h) 2)
        t1 (System/nanoTime)
        analysis (check opts
                        ;{:cycle-search-timeout 10000}
                        h)
        t2 (System/nanoTime)
        run-time   (/ (- t1 t0) 1e9)
        check-time (/ (- t2 t1) 1e9)]
    (println (format "%s: %d ops run in %.2f s (%.2f ops/sec); checked in %.2f s (%.2f ops/sec)"
                     test-name n run-time (/ n run-time)
                     check-time (/ n check-time)))
    analysis))

(deftest ^:perf sim-prefix-perf-test
  ; Performance test on a long prefix consistent history
  (let [n   (long 3e5)
        t0  (System/nanoTime)
        h   (:history (sim/run {:db :prefix, :limit n, :concurrency 10}))
        res (perf-check "sim-prefix-perf-test" t0 {} h)
        as  (:anomalies res)]
      (is (= (* 2 n) (count h)))
      (is (= false (:valid? res)))
      (is (= #{:read-uncommitted} (:not res)))
      (is (= {:incompatible-order 11164
              :lost-update 5226
              ; :PL-1-cycle-exists 1 ; Slower machines might see this instead of finding the G0/G-single-item-realtime
              :G0 1
              :G-nonadjacent-item 1
              :G-single-item-realtime 1
              :cycle-search-timeout 1}
            (into {} (map (juxt key (comp count val)) (:anomalies res)))))
      ))

(deftest ^:perf sim-si-perf-test
  ; Performance test on a long snapshot isolated history
  (let [n   (long 1e6)
        t0  (System/nanoTime)
        h   (:history (sim/run {:db :si, :limit n, :concurrency 10}))
        res (perf-check "sim-si-perf-test" t0 {} h)
        as  (:anomalies res)]
      (is (= (* 2 n) (count h)))
      (is (= false (:valid? res)))
      (is (= #{:repeatable-read} (:not res)))
      (is (= [:G2-item :G2-item-realtime] (:anomaly-types res)))
      (is (= 16336 (count (:G2-item as))))
      (is (= 3986 (count (:G2-item-realtime as))))
      ))

(deftest ^:perf sim-si-strong-session-serializable-perf-test
  ; Performance test on a long snapshot isolated history, checking strong
  ; session serializable. We want to stress the parallel fold for the process
  ; graph.
  (let [n   (long 1e6)
        t0  (System/nanoTime)
        h   (:history (sim/run {:db :si, :limit n, :concurrency 10}))
        res (perf-check "sim-si-strong-session-serializable-perf-test" t0
                        {:consistency-models [:strong-session-serializable]}
                        h)
        as  (:anomalies res)]
      (is (= (* 2 n) (count h)))
      (is (= false (:valid? res)))
      (is (= #{:repeatable-read} (:not res)))
      (is (= [:G2-item :G2-item-process] (:anomaly-types res)))
      ; It's a little weird that this finds fewer G2-items than the full
      ; strong-1SR test above. Not quite sure what to make of that.
      (is (= 16352 (count (:G2-item as))))
      (is (= 1685 (count (:G2-item-process as))))
      ))

(deftest ^:perf sim-ssi-perf-test
  ; Performance test on a long serializable snapshot isolated history
  (let [n   (long 1e6)
        t0  (System/nanoTime)
        h   (:history (sim/run {:db :ssi, :limit n, :concurrency 10}))
        res (perf-check "sim-ssi-perf-test" t0 {} h)
        as  (:anomalies res)]
      (is (= (* 2 n) (count h)))
      (is (= {:valid? true} res))))

(deftest ^:perf perfect-perf-test
  ; An end-to-end performance test based on a perfect strict-1SR system
  (let [n (long 1e6)
        ; Takes a state, a txn, and a volatile for the completed txn to go to.
        ; Applies txn to state, returning new state, and updating volatile.
        apply-txn (fn apply-txn [state txn txn'-volatile]
                    (loopr [state' (transient state)
                            txn'  (transient [])]
                           [[f k v :as mop] txn]
                           (case f
                             :r (recur state'
                                       (conj! txn' [f k (get state' k)]))
                             :append (recur (assoc! state' k
                                                    (conj (get state' k []) v))
                                            (conj! txn' mop)))
                           (do (vreset! txn'-volatile (persistent! txn'))
                               (persistent! state'))))
        t0 (System/nanoTime)
        ; Build history
        txn' (volatile! nil)
        h (loopr [history (transient [])
                  state   {}
                  i       0]
                 [op (take n (gen))]
                 (let [process  (rand-int 10)
                       op       (h/op (assoc op
                                             :index i,
                                             :time i,
                                             :process process))
                       history' (conj! history op)
                       state'   (apply-txn state (:value op) txn')
                       i'       (inc i)
                       op'      (assoc op :index i' :time i', :type :ok,
                                       :value @txn')
                       history' (conj! history' op')]
                   (recur history' state' (inc i')))
                 (h/history (persistent! history)
                            {:dense-indices? true
                             :have-indices? true
                             :already-ops? true}))]
    (is (= (* 2 n) (count h)))
    (is (= true (:valid? (perf-check "perfect-perf-test" t0 {} h))))))

(deftest ^:perf sloppy-perf-test
  ; An end-to-end performance test based on a sloppy database which takes
  ; locks... sometimes.
  (let [n           (long 1e6)
        concurrency 4
        ; Our state is all mutated in place using a global lock.
        lock        (Object.)
        state       (HashMap.)
        apply-txn!
        (fn apply-txn! [txn]
          ; Whoops! Sometimes we forget the global lock!
          (let [lock? (< 0.05 (rand))]
            (try
              (when lock? (monitor-enter lock))
              (loopr [txn' (transient [])]
                     [[f k v :as mop] txn]
                     (case f
                       :r
                       (recur (conj! txn' [f k (vec (.get state k))]))

                       :append
                       (let [; Ensure we have a list of elements
                             vs (or (.get state k)
                                    (locking state ; prevent races in HashMap
                                      (let [l (ArrayList.)]
                                        (.put state k l)
                                        l)))]
                         ; Mutate it in place
                         (locking vs (.add vs v)) ; prevent races in ArrayList
                         (recur (conj! txn' mop))))
                     (persistent! txn'))
              (finally
                (when lock? (monitor-exit lock))))))
        ; Build history
        ops      (atom (take n (gen)))
        take-op! (fn poll-op! []
                   (let [opv (volatile! nil)]
                     (swap! ops (fn [ops]
                                  (if-let [op (first ops)]
                                    (do (vreset! opv op)
                                        (next ops))
                                    ; Exhausted
                                    (do (vreset! opv nil)
                                        ops))))
                     @opv))
        h    (atom [])
        t0   (System/nanoTime)]
    ; Go!
    (->> (range concurrency)
         (real-pmap (fn worker [process]
                      (loop []
                        (when-let [op (take-op!)]
                          (let [op   (assoc op :process process)
                                _    (swap! h conj op)
                                txn' (apply-txn! (:value op))
                                op'  (assoc op :type :ok, :value txn')]
                            (swap! h conj op')
                            (recur))))))
         dorun)
    (let [h   (h/history @h)
          res (perf-check "sloppy-perf-test" t0 {} h)
          as  (:anomalies res)]
      (is (= (* 2 n) (count h)))
      (is (= false (:valid? res)))
      (is (= #{:read-uncommitted} (:not res)))
      (is (< 1/100000 (/ (count (:G0 as)) n)))
      (is (< 1/100000 (/ (count (:G1c as)) n)))
      (is (< 1/100000 (/ (count (:G-single-item as)) n)))
      ;(is (< 1/100000 (/ (count (:G-nonadjacent as)) n)))
      ;(is (< 1/100000 (/ (count (:G2-item as)) n)))
      ;(pprint (:anomaly-types res))
      )))

; Example of checking a file, for later
;(deftest dirty-update-1-test
;  (cf {} "histories/dirty-update-1.edn")))

