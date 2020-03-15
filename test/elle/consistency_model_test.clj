(ns elle.consistency-model-test
  "Elle finds anomalies in histories. This namespace helps turn those anomalies
  into claims about what kind of consistency models are supported by, or ruled
  out by, a given history."
  (:require [clojure [pprint :refer [pprint]]
                     [test :refer :all]]
            [elle.consistency-model :refer :all]))

(deftest all-implied-anomalies-test
  (is (= [:G-SI] (seq (all-implied-anomalies [:G-SI])))))

(let [as #(into (sorted-set)
                (map friendly-model-name (anomalies->impossible-models %)))]

  (deftest anomaly->impossible-models-test
    (testing "G-single"
    (is (= #{:forward-consistent-view
             :full-serializable
             :consistent-view
             :strict-serializable
             :update-serializable}
           (as [:G-single]))))

    (testing "G-SI"
      (is (= #{:snapshot-isolation
               :serializable
               :strict-serializable}
             (as [:G-SI]))))

    (testing "dirty update"
      (is (= #{:read-committed
               :monotonic-atomic-view
               :snapshot-isolation
               :repeatable-read
               :serializable
               :strict-serializable
               :update-serializable
               :cursor-stability
               :forward-consistent-view
               :consistent-view
               :monotonic-view
               :monotonic-snapshot-read
               :full-serializable
               }
             (as [:dirty-update]))))

    (testing "internal"
      (is (= #{:causal-cerone
               :parallel-snapshot-isolation
               :prefix
               :read-atomic
               :serializable
               :snapshot-isolation
               :strict-serializable
               }
             (as [:internal]))))))
