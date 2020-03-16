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
                 :read-your-writes]))))

    (testing "cerone-end-to-end"
      (is (= #{:read-atomic}
             (s [:serializable :read-atomic])
             (s [:read-atomic :serializable]))))))

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
                 :read-your-writes]))))

    (testing "cerone-end-to-end"
      (is (= #{:serializable}
             (s [:serializable :read-atomic])
             (s [:read-atomic :serializable]))))))

(let [as #(into (sorted-set)
                (map friendly-model-name (anomalies->impossible-models %)))]

  (deftest anomaly->impossible-models-test
    (testing "G-single"
    (is (= #{:forward-consistent-view
             :serializable
             :consistent-view
             :strict-serializable
             :update-serializable
             :snapshot-isolation}
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
               :causal-cerone
               :parallel-snapshot-isolation
               :prefix
               :read-atomic
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
    (is (= {:not       #{}
            :also-not  #{}}
           (friendly-boundary []))))

  (testing "cyclic-versions"
    (is (= {:not #{:read-uncommitted}
            :also-not #{:read-committed
                        :snapshot-isolation
                        ; Not sure about this one. PSI allows long fork, and
                        ; I think long fork explicitly looks like inconsistent
                        ; version orders. Then again, it's not so much that the
                        ; version orders themselves are inconsistent, as the
                        ; transactions using those orders are.
                        ; :parallel-snapshot-isolation
                        :repeatable-read
                        :serializable
                        :strict-serializable
                        :consistent-view
                        :cursor-stability
                        :monotonic-atomic-view
                        :monotonic-snapshot-read
                        :update-serializable
                        :forward-consistent-view
                        :monotonic-view}}
           (friendly-boundary [:cyclic-versions]))))

  (testing "internal"
    (is (= {:not #{:read-atomic}
            :also-not #{:causal-cerone
                        :parallel-snapshot-isolation
                        :prefix
                        :serializable
                        :snapshot-isolation
                        :strict-serializable}}
           (friendly-boundary [:internal]))))

  (testing "G1a"
    (is (= {:not      #{:read-atomic :read-committed}
            :also-not #{:causal-cerone :consistent-view :cursor-stability
                        :forward-consistent-view :monotonic-atomic-view
                        :monotonic-snapshot-read :monotonic-view
                        :parallel-snapshot-isolation :prefix :repeatable-read
                        :serializable :snapshot-isolation :strict-serializable
                        :update-serializable}}
           (friendly-boundary [:G1a]))))

  (testing "G-single"
    (is (= {:not #{:consistent-view}
            :also-not #{:snapshot-isolation
                        :serializable
                        :strict-serializable
                        :forward-consistent-view
                        :update-serializable}}
           (friendly-boundary [:G-single]))))

  (testing "internal and G2"
    (is (= {:not #{:read-atomic}
            :also-not #{:causal-cerone
                           :parallel-snapshot-isolation
                           :prefix
                           :snapshot-isolation
                           :serializable
                           :strict-serializable}}
           (friendly-boundary [:G2 :internal])))))
