(ns elle.consistency-model-test
  "Elle finds anomalies in histories. This namespace helps turn those anomalies
  into claims about what kind of consistency models are supported by, or ruled
  out by, a given history."
  (:require [clojure [pprint :refer [pprint]]
                     [test :refer :all]]
            [elle.consistency-model :refer :all]))

(deftest all-implied-anomalies-test
  (is (= [:G-SI] (seq (all-implied-anomalies [:G-SI])))))

(deftest weakest-models-test
  (let [s #(set (map friendly-model-name (weakest-models %)))]
    (testing "empty"
      (is (= #{} (s []))))

    (testing "simple"
      (is (= #{:serializable}
             (s [:serializable :strict-serializable]))))

    (testing "independent"
      (is (= #{:read-your-writes
               :read-committed}
             (s [:repeatable-read
                 :read-committed
                 :sequential
                 :read-your-writes]))))))

(deftest strongest-models-test
  (let [s #(set (map friendly-model-name (strongest-models %)))]
    (testing "empty"
      (is (= #{} (s []))))

    (testing "simple"
      (is (= #{:strict-serializable}
             (s [:serializable :strict-serializable]))))

    (testing "independent"
      (is (= #{:repeatable-read
               :sequential}
             (s [:repeatable-read
                 :read-committed
                 :sequential
                 :read-your-writes]))))))

(let [as #(into (sorted-set)
                (map friendly-model-name (anomalies->impossible-models %)))]

  (deftest anomaly->impossible-models-test
    (testing "G-single"
    (is (= #{:forward-consistent-view
             :serializable
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

(deftest friendly-boundary-test
  (testing "empty"
    (is (= {:is-not #{}}
           (friendly-boundary []))))

  (testing "internal"
    (is (= {:is-not #{:read-atomic}}
           (friendly-boundary [:internal]))))

  (testing "G-single"
    (is (= {:is-not #{:consistent-view}}
           (friendly-boundary [:G-single]))))

  (testing "internal and G2"
    (is (= {:is-not #{:consistent-view :read-atomic}}
           (friendly-boundary [:G-single :internal])))))
