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
    ; TODO: we call this G2-item, but it's actually G2. We have to extend
    ; elle.txn to know about predicate edges.
    (is (= [:G2-item] (:anomaly-types res)))))

(deftest g1c-predicate-read-unseen-universe-test
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
