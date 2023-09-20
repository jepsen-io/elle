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

(deftest g1c-predicate-read-seen-test
  (let [[t1 t1' t2 t2' :as h]
        (h/history
          [; T1 sets x=0 and performs a predicate read, seeing y = 2.
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
          [; T1 sets x=0 and predicate reads nothing. Implicitly, the version
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
    (is (not (:valid? res)))
    (is (= [:G2] (:anomaly-types res)))))

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
        res (check h)]
    ; T1 rw-predicate precedes T2, because T1 implicitly observed y = 0, and T2
    ; wrote y = 1, which followed in the version order and also changed the
    ; matches of the predicate.
    (is (not (:valid? res)))
    (is (= [:G2] (:anomaly-types res)))))

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
        res (check h)]
    (is (not (:valid? res)))
    ; This is both G1c and G-Single.
    (is (= #{:G-single :G1c} (set (:anomaly-types res))))))

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
           ; T2 reads y, so T1  -> wr T2. However, it *fails* to observe z, which means T2 -rw-> T0
           {:process 1, :type :invoke, :f :txn, :value [[:r :y nil] [:r :z nil]]}
           {:process 1, :type :ok,     :f :txn, :value [[:r :y 1]   [:r :z nil]]}])
        res (check h)]
    (is (not (:valid? res)))
    ; This is G-single.
    (is (= [:G-single] (:anomaly-types res)))))
