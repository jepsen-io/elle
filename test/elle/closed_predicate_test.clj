(ns elle.closed-predicate-test
  (:refer-clojure :exclude [test])
  (:require [clojure [pprint :refer [pprint]]
                     [set :as set]
                     [test :refer [deftest is testing]]
                     [walk :as walk]]
            [clojure.test.check [generators :as gen]]
            [com.gfredericks.test.chuck.clojure-test :refer
             [checking for-all]]
            [dom-top.core :refer [loopr]]
            [elle [core :as elle]
                  [core-test :refer [read-history]]
                  [closed-predicate :refer :all]
                  [graph :as g]
                  [util :refer [map-vals]]]
            [jepsen [history :as h]
                    [txn :as txn]]
            [slingshot.slingshot :refer [try+ throw+]]))

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

(deftest versions-after-test
  (is (= nil (versions-after {} :x 4)))
  (is (= [3 4] (versions-after {:x [1 2 3 4]} :x 2)))
  (is (= nil (versions-after {:x [1 2 3 4]} :x 4))))

(deftest version-after-test
  (is (= 2 (version-after {:x [1 2]} :x 1)))
  (is (= nil (version-after {:x [1 2]} :x 2))))

(deftest eval-pred-test
  (testing "unborn"
    (is (= false (eval-pred :true :elle/unborn))))

  (testing "dead"
    (is (= false (eval-pred :true :elle/dead))))

  (testing "true"
    (is (= true (eval-pred :true 5)))
    (is (= true (eval-pred :true false))))

  (testing "="
    (is (= true (eval-pred [:= 5] 5)))
    (is (= false (eval-pred [:= 5] 4))))

  (testing "mod"
    (is (= false (eval-pred [:mod 3 2] 4)))
    (is (= true  (eval-pred [:mod 3 2] 5)))
    (is (= false (eval-pred [:mod 3 2] 6)))))

(deftest write-mop-index-test
  (let [op {:f :txn, :value [[:delete 38 nil] [:w 31 8] [:delete 26 nil] [:insert 40 9]]}]
    (is (= 0 (write-mop-index op 38 :elle/dead)))
    (is (= 1 (write-mop-index op 31 8)))
    (is (= 2 (write-mop-index op 26 :elle/dead)))
    (is (= 3 (write-mop-index op 40 9)))))

(deftest g1c-predicate-read-seen-test
  (let [[t1 t1' t2 t2' :as h]
        (h/history
          [; T1 sets x = 1 and performs a predicate read, seeing y = 2.
           {:process 0, :type :invoke, :f :txn, :value [[:w :x 1] [:rp :true nil]]}
           {:process 0, :type :ok,     :f :txn, :value [[:w :x 1] [:rp :true {:y 2}]]}
           ; T2 sets y = 2 and predicate reads x = 1.
           {:process 1, :type :invoke, :f :txn, :value [[:w :y 2] [:rp :true nil]]}
           {:process 1, :type :ok,     :f :txn, :value [[:w :y 2] [:rp :true {:x 1}]]}])
        res (check h)]
    ; This forms a write-read cycle, G1c.
    (is (not (:valid? res)))
    (is (= [:G1c] (:anomaly-types res)))))

(deftest g2-predicate-read-unseen-test
  (let [[t1 t1' t2 t2' :as h]
        (h/history
          [; T1 sets x=1 and predicate reads nothing. Implicitly, the version
           ; set must be the unborn values of x and y.
           {:process 0, :type :invoke, :f :txn, :value [[:w :x 1] [:rp :true nil]]}
           {:process 0, :type :ok,     :f :txn, :value [[:w :x 1] [:rp :true {}]]}
           ; T2 sets y = 2 and also predicate reads nothing
           {:process 1, :type :invoke, :f :txn, :value [[:w :y 2] [:rp :true nil]]}
           {:process 1, :type :ok,     :f :txn, :value [[:w :y 2] [:rp :true {}]]}])
        res (check h)]
    ; T1 predicate rw precedes T2, because T1 performed a predicate read where
    ; VSet(P) must have covered the unborn version of y, and T2 wrote a version
    ; y = 2 which followed y = unborn, and that also changed whether the
    ; predicate matched.
    ;
    ; This also happens to be a strong SI violation. We don't catch it because
    ; there are two edges from T1->T2: one is RT, and the other is RW. When
    ; looking for a realtime cycle, we choose edges which are *solely*
    ; realtime. This actually makes our analysis less precise than it should
    ; be. Thankfully, the cycle-exists checker catches this.
    ;
    ; Later we should consider hand-rolling a better state machine for the BFS.
    (is (not (:valid? res)))
    (is (= [:G2 :strong-snapshot-isolation-cycle-exists]
           (:anomaly-types res)))))

(deftest g1c-predicate-read-unseen-universe-delete-test
  (let [[t1 t1' t2 t2' :as h]
        (h/history
          [; We begin with a universe where x and y are 0.
           {:process 0, :type :invoke, :f :init, :value {:x 0, :y 0}}
           {:process 0, :type :ok,     :f :init, :value {:x 0, :y 0}}
           ; T1 deletes x and predicate reads nothing. Implicitly, the version
           ; set must be x = :dead and y = :dead.
           {:process 0, :type :invoke, :f :txn, :value [[:delete :x] [:rp :true nil]]}
           {:process 0, :type :ok,     :f :txn, :value [[:delete :x] [:rp :true {}]]}
           ; T2 deletes y and also predicate reads nothing
           {:process 1, :type :invoke, :f :txn, :value [[:delete :y] [:rp :true nil]]}
           {:process 1, :type :ok,     :f :txn, :value [[:delete :y] [:rp :true {}]]}])
        res (check h)]
    ; T1 wr precedes T2, because T1 deleted x, and T2 (implicitly) selected
    ; that deleted version for its predicate read. Likewise, T2 -wr-> T1.
    (is (not (:valid? res)))
    (is (= [:G1c] (:anomaly-types res)))))

(deftest g1c-predicate-read-unseen-universe-write-test
  (let [[t1 t1' t2 t2' :as h]
        (h/history
          [; We begin with a universe where x and y are 0.
           {:process 0, :type :invoke, :f :init, :value {:x 0, :y 0}}
           {:process 0, :type :ok,     :f :init, :value {:x 0, :y 0}}
           ; T1 predicate reads everything 0, sees x = 0 (which implies y = 1) and sets x = 1.
           {:process 0, :type :invoke, :f :txn, :value [[:rp [:= 0] nil]    [:w :x 1]]}
           {:process 0, :type :ok,     :f :txn, :value [[:rp [:= 0] {:x 0}] [:w :x 1]]}
           ; T2 predicate reads everything 0, sees y = 0 (which implies x = 1), and sets y = 1.
           {:process 1, :type :invoke, :f :txn, :value [[:rp [:= 0] nil]     [:w :y 1]]}
           {:process 1, :type :ok,     :f :txn, :value [[:rp [:= 0] {:y 0}]  [:w :y 1]]}])
        res (check h)]
    ; T1 wr precedes T2, because T1 deleted x, and T2 (implicitly) selected
    ; that deleted version for its predicate read. Likewise, T2 -wr-> T1.
    (is (not (:valid? res)))
    (is (= [:G1c] (:anomaly-types res)))))

(deftest g2-predicate-read-unseen-universe-write-test
  (let [[t1 t1' t2 t2' :as h]
        (h/history
          [; We begin with a universe where x and y are 0.
           {:process 0, :type :invoke, :f :init, :value {:x 0, :y 0}}
           {:process 0, :type :ok,     :f :init, :value {:x 0, :y 0}}
           ; T1 predicate reads everything 1, sees nothing (which implies y = 0) and sets x = 1.
           {:process 0, :type :invoke, :f :txn, :value [[:rp [:= 1] nil] [:w :x 1]]}
           {:process 0, :type :ok,     :f :txn, :value [[:rp [:= 1] {}]  [:w :x 1]]}
           ; Same, but flip x and y
           {:process 1, :type :invoke, :f :txn, :value [[:rp [:= 1] nil] [:w :y 1]]}
           {:process 1, :type :ok,     :f :txn, :value [[:rp [:= 1] {}]  [:w :y 1]]}])
        res (check {:directory "test-output/closed-predicate/g2-predicate-read-unseen-universe-write"} h)]
    ; T1 rw-predicate precedes T2, because T1 implicitly observed y = 0, and T2
    ; wrote y = 1, which followed in the version order and also changed the
    ; matches of the predicate. Ditto, T2 -rwp-> T1.
    (is (not (:valid? res)))
    ; This also happens to be a strong-SI violation, but we can't see it
    ; because our BFS isn't smart enough to realize it can take an RT when an
    ; RW is available.
    (is (= [:G2 :strong-snapshot-isolation-cycle-exists]
           (:anomaly-types res)))))

(deftest wr-g1c-item-test
  ; A cycle of all write-read edges, forming G1c.
  (let [[t0 t0' t1 t1' t2 t2' t3 t3' :as h]
        (h/history
          [; We begin with a universe where x is 0 and z is 0.
           {:process 0, :type :invoke, :f :init, :value {:x 0 :z 0}}
           {:process 0, :type :ok,     :f :init, :value {:x 0 :z 0}}
           ; T1 reads z = 3 from T3 and deletes x.
           {:process 0, :type :invoke, :f :txn, :value [[:r :z nil] [:delete :x]]}
           {:process 0, :type :ok,     :f :txn, :value [[:r :z 3]   [:delete :x]]}
           ; T2 reads x = nil (which we can prove is :dead) from T1 and inserts y = 2
           {:process 1, :type :invoke, :f :txn, :value [[:r :x nil] [:insert :y 2]]}
           {:process 1, :type :ok,     :f :txn, :value [[:r :x nil] [:insert :y 2]]}
           ; T3 reads y = 2 from T2 and writes z = 3.
           {:process 2, :type :invoke, :f :txn, :value [[:r :y nil] [:w :z 3]]}
           {:process 2, :type :ok,     :f :txn, :value [[:r :y 2]   [:w :z 3]]}])
        res (check {:directory "test-output/closed-predicate/wr-g1c-item"} h)]
    (is (not (:valid? res)))
    ; This is G1c.
    (is (= {:valid? false,
            :anomaly-types [:G1c],
           :anomalies
           {:G1c
            [{:cycle [t2' t3' t1' t2']
              :steps
              [{:type :wr,
                :key :y,
                :value 2,
                :a-mop-index 1,
                :b-mop-index 0}
               {:type :wr,
                :key :z,
                :value 3,
                :a-mop-index 1,
                :b-mop-index 0}
               {:type :wr,
                :key :x,
                :value :elle/dead,
                :a-mop-index 1,
                :b-mop-index 0}],
              :type :G1c}]},
           :not #{:read-committed},
           :also-not
           #{:consistent-view
             :cursor-stability
             :forward-consistent-view
             :monotonic-atomic-view
             :monotonic-snapshot-read
             :monotonic-view
             :repeatable-read
             :serializable
             :snapshot-isolation
             :strong-read-committed
             :strong-snapshot-isolation
             :strong-serializable
             :strong-session-read-committed
             :strong-session-serializable
             :strong-session-snapshot-isolation
             :update-serializable
             :update-atomic
             :causal-cerone
             :parallel-snapshot-isolation
             :prefix
             :read-atomic}}
           res))))

(deftest ww-wr-rw-item-test
  ; Full ww cycles are impossible if every key is mutated at most once (since
  ; all edges point from the init txn), but we *can* form loops including ww.
  (let [[t0 t0' t1 t1' t2 t2' :as h]
        (h/history
          [; We begin with a universe where x is 0.
           {:process 0, :type :invoke, :f :init, :value {:x 0 :z 0}}
           {:process 0, :type :ok,     :f :init, :value {:x 0 :z 0}}
           ; T1 deletes x, so T0 -ww-> T1. It inserts y.
           {:process 0, :type :invoke, :f :txn, :value [[:delete :x] [:insert :y 1]]}
           {:process 0, :type :ok,     :f :txn, :value [[:delete :x] [:insert :y 1]]}
           ; T2 reads y, so T1 -> wr T2. However, it *fails* to observe z, which means T2 -rw-> T0
           {:process 1, :type :invoke, :f :txn, :value [[:r :y nil] [:r :z nil]]}
           {:process 1, :type :ok,     :f :txn, :value [[:r :y 1]   [:r :z nil]]}])
        res (check {:directory "test-output/closed-predicate/ww-wr-rw-item"} h)]
    (is (= {:valid? false,
           :anomaly-types [:G-single-item],
           :anomalies
           {:G-single-item
            [{:cycle [t2' t0' t1' t2']
              :steps
              [{:type :rw,
                :key :z,
                :value :elle/unborn,
                :value' 0,
                :a-mop-index 1,
                :b-mop-index 0}
               {:type :ww,
                :key :x,
                :value 0,
                :value' :elle/dead,
                :a-mop-index 0,
                :b-mop-index 0}
               {:type :wr,
                :key :y,
                :value 1,
                :a-mop-index 1,
                :b-mop-index 0}],
              :type :G-single-item}]},
           :not #{:consistent-view :repeatable-read},
           :also-not
           #{:forward-consistent-view
             :serializable
             :snapshot-isolation
             :strong-serializable
             :strong-session-serializable
             :strong-session-snapshot-isolation
             :strong-snapshot-isolation
             :update-serializable}}
           res))))

(deftest failure-to-observe-test
  ; When a predicate read fails to see something we KNOW must have been there,
  ; we report that separately.
  (let [[t0 t0' t1 t1' :as h]
        (h/history
          [{:index 0, :type :invoke, :process 0, :f :init, :value {5 3}}
           {:index 5, :type :ok, :process 0, :f :init, :value {5 3}}
           {:index 8, :type :invoke, :process 1, :f :txn, :value [[:rp [:mod 2 1] nil] [:rp [:= 3] nil]]}
           {:index 52, :type :ok, :process 1, :f :txn, :value [[:rp [:mod 2 1] {}] [:rp [:= 3] {}]]}])
        res (check h)]
    (is (= {:valid? false,
            :anomaly-types [:predicate-read-miss],
            :anomalies
            {:predicate-read-miss
             [{:op t1'
               :mop [:rp [:mod 2 1] {}],
               :key 5,
               :versions [3]}
              {:op t1'
               :mop [:rp [:= 3] {}],
               :key 5,
               :versions [3]}]},
            :not #{:serializable},
            :also-not
            #{:strong-serializable :strong-session-serializable}}
           res))))

(deftest init-g-single-pred-test
  ; This catches a bug in wr-explainer when a cycle involves the init txn.
  (let [[t0 t0' t1 t1' :as h]
        (h/history
          ; T0 init creates key 7 = 1
          [{:index 1, :type :invoke, :process 4, :f :init, :value {7 1}}
           {:index 4, :type :ok, :process 4, :f :init, :value {7 1}}
           ; T1 implicitly selects version 1 of 7 in its predicate read, since
           ; there can't have been any other possible value. However, it also
           ; fails to read key 7! This is G-single-item: wrp / rw.
           {:index 72, :type :invoke, :process 7, :f :txn, :value [[:rp [:mod 2 0] nil] [:r 7 nil]]}
           {:index 82, :type :ok, :process 7, :f :txn, :value [[:rp [:mod 2 0] {}] [:r 7 nil]]}])
        res (check {:directory "test-output/closed-predicate/init-g-single-pred"} h)]
    (is (= {:valid? false,
           :anomaly-types [:G-single-item],
           :anomalies
           {:G-single-item
            [{:cycle [t1' t0' t1']
              :steps
              [{:type :rw,
                :key 7,
                :value :elle/unborn,
                :value' 1,
                :a-mop-index 1,
                :b-mop-index 0}
               {:type :wrp,
                :key 7,
                :value 1,
                :predicate-read [:rp [:mod 2 0] {}],
                :a-mop-index 0,
                :b-mop-index 0}],
              :type :G-single-item}]},
           :not #{:consistent-view :repeatable-read},
           :also-not
           #{:forward-consistent-view
             :serializable
             :snapshot-isolation
             :strong-serializable
             :strong-session-serializable
             :strong-session-snapshot-isolation
             :strong-snapshot-isolation
             :update-serializable}}
           res))))

(deftest g1c-multi-key-delete-test
  ; A G1c cycle where T2 deletes two keys (38 and 26), and the delete of 38
  ; occurs after T1's predicate read, but the delete of 26 occurs *before* it.
  (let [[t0 t0' t1 t1' t2 t2' :as h]
        (h/history
          [{:type :invoke, :process 2, :f :init, :value {26 0, 31 0, 38 0}}
           {:type :ok, :process 2, :f :init, :value {26 0, 38 0}}
           {:type :invoke, :process 2, :f :txn, :value [[:delete 38] [:w 31 8] [:delete 26] [:w 40 9]]}
           {:type :ok, :process 2, :f :txn, :value [[:delete 38 nil] [:w 31 8] [:delete 26 nil] [:w 40 9]]}
           {:type :invoke, :process 3, :f :txn, :value [[:rp :true nil]]}
           {:type :ok, :process 3, :f :txn, :value [[:rp :true {31 0, 38 0}]]}])
        res (check {:directory "test-output/closed-predicate/g1c-multi-key-delete-test"} h)]
    (is (= {:valid? false,
           :anomaly-types [:G-single],
           :anomalies
           {:G-single
            [{:cycle [t2' t1' t2']
              :steps
              [{:type :rwp,
                :key 38,
                :value 0,
                :value' :elle/dead,
                :predicate? true,
                :predicate-read [:rp :true {31 0, 38 0}],
                :a-mop-index 0,
                :b-mop-index 0}
               {:type :wrp,
                :key 26,
                :value :elle/dead,
                :predicate-read [:rp :true {31 0, 38 0}],
                :a-mop-index 2,
                :b-mop-index 0}],
              :type :G-single}]},
           :not #{:consistent-view},
           :also-not
           #{:forward-consistent-view
             :serializable
             :snapshot-isolation
             :strong-serializable
             :strong-session-serializable
             :strong-session-snapshot-isolation
             :strong-snapshot-isolation
             :update-serializable}}
           res))))
