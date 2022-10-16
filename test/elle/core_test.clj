(ns elle.core-test
  (:require [clojure [test :refer :all]
                     [edn :as edn]]
            [clojure.java.io :as io]
            [dom-top.core :refer [real-pmap]]
            [elle [core :refer :all]
                  [graph :as g]]
            [jepsen.txn :as txn]
            [knossos [history :as history]
                     [op :as op]]
            [slingshot.slingshot :refer [try+ throw+]])
  (:import (java.io PushbackReader)))

(defn read-history
  "Reads a history of op maps from a file."
  [filename]
  (with-open [r (PushbackReader. (io/reader filename))]
    (->> (repeatedly #(edn/read {:eof nil} r))
         (take-while identity)
         vec)))

(deftest process-graph-test
  (let [o1 {:index 0 :process 1 :type :ok}
        o2 {:index 1 :process 2 :type :ok}
        o3 {:index 2 :process 2 :type :ok}
        o4 {:index 3 :process 1 :type :ok}
        history [o1 o2 o3 o4]]
    (is (= {o1 #{o4}, o2 #{o3}, o3 #{}, o4 #{}}
           (g/->clj (:graph (process-graph history)))))))

(deftest monotonic-key-graph-test
  (testing "basics"
    (let [r1 {:index 0 :type :ok, :f :read, :value {:x 0, :y 0}}
          r2 {:index 2 :type :ok, :f :read, :value {:x 1, :y 0}}
          r3 {:index 4 :type :ok, :f :read, :value {:x 1, :y 1}}
          r4 {:index 5 :type :ok, :f :read, :value {:x 0, :y 1}}
          history [r1 r2 r3 r4]]
      (is (= {r1 #{r2 r3 r4}
              r2 #{r3 r4}
              r3 #{}
              r4 #{r2 r3}}
             (g/->clj (:graph (monotonic-key-graph history)))))))

  (testing "Can bridge missing values"
    (let [r1 {:index 0 :type :ok, :f :read, :value {:x 0, :y 0}}
          r2 {:index 2 :type :ok, :f :read, :value {:x 1, :y 1}}
          r3 {:index 4 :type :ok, :f :read, :value {:x 4, :y 1}}
          r4 {:index 5 :type :ok, :f :read, :value {:x 0, :y 1}}
          history [r1 r2 r3 r4]]
      (is (= {r1 #{r2 r3 r4}
              r2 #{r3}
              r3 #{}
              r4 #{r2}}
             (g/->clj (:graph (monotonic-key-graph history))))))))

(defn big-history-gen
  [v]
  (let [f    (rand-nth [:inc :read])
        proc (rand-int 100)
        k    (rand-nth [[:x] [:y] [:x :y]])
        type (rand-nth [:ok :ok :ok :ok :ok
                        :fail :info :info])]
    [{:process proc, :type :invoke, :f f, :value {k v}}
     {:process proc, :type type,    :f f, :value {k v}}]))

(deftest checker-test
  (testing "valid"
    (let [history [{:index 0 :type :invoke :process 0 :f :read :value nil}
                   {:index 1 :type :ok     :process 0 :f :read :value {:x 0 :y 0}}
                   {:index 2 :type :invoke :process 0 :f :inc :value [:x]}
                   {:index 3 :type :ok     :process 0 :f :inc :value {:x 1}}
                   {:index 4 :type :invoke :process 0 :f :read :value nil}
                   {:index 5 :type :ok     :process 0 :f :read :value {:x 1 :y 1}}]]
      (is (= {:valid?     true
              :scc-count  0
              :cycles     []}
             (check {:analyzer monotonic-key-graph} history)))))

  (testing "invalid"
    (let [r00  {:index 0 :type :invoke :process 0 :f :read :value nil}
          r00' {:index 1 :type :ok     :process 0 :f :read :value {:x 0 :y 0}}
          r10  {:index 2 :type :invoke :process 0 :f :read :value nil}
          r10' {:index 3 :type :ok     :process 0 :f :read :value {:x 1 :y 0}}
          r11  {:index 4 :type :invoke :process 0 :f :read :value nil}
          r11' {:index 5 :type :ok     :process 0 :f :read :value {:x 1 :y 1}}
          r01  {:index 6 :type :invoke :process 0 :f :read :value nil}
          r01' {:index 7 :type :ok     :process 0 :f :read :value {:x 0 :y 1}}
          history [r00 r00' r10 r10' r11 r11' r01 r01']]
      (is (= {:valid? false
              :scc-count 1
              :cycles ["Let:\n  T1 = {:index 3, :type :ok, :process 0, :f :read, :value {:x 1, :y 0}}\n  T2 = {:index 7, :type :ok, :process 0, :f :read, :value {:x 0, :y 1}}\n\nThen:\n  - T1 < T2, because T1 observed :y = 0, and T2 observed a higher value 1.\n  - However, T2 < T1, because T2 observed :x = 0, and T1 observed a higher value 1: a contradiction!"]}
             (check {:analyzer monotonic-key-graph} history)))))

  (testing "large histories"
    (let [history (->> (range)
                       (mapcat big-history-gen)
                       (take 10000)
                       vec)
          history  (map-indexed #(assoc %2 :index %1) history)
          r (check {:analyzer monotonic-key-graph} history)]
      (is (:valid? r)))))

(deftest monotonic+process-test
  ; Here, we construct an order which is legal on keys AND is sequentially
  ; consistent, but the key order is incompatible with process order.
  (let [[r1 r2 :as history]
        (history/index [{:type :ok, :process 0, :f :read, :value {:x 1}}
                        {:type :ok, :process 0, :f :read, :value {:x 0}}])]
    (testing "combined order"
      (let [{:keys [graph explainer]}
            ((combine monotonic-key-graph process-graph) history)]
        (is (= {r1 #{r2} r2 #{r1}}
               (g/->clj graph)))))
    (testing "independently valid"
      (is (= {:valid? true
              :scc-count 0
              :cycles []}
             (check {:analyzer monotonic-key-graph} history)))
      (is (= {:valid? true
              :scc-count 0
              :cycles []}
             (check {:analyzer process-graph} history))))
    (testing "combined invalid"
      (is (= {:valid? false
              :scc-count 1
              :cycles ["Let:\n  T1 = {:type :ok, :process 0, :f :read, :value {:x 0}, :index 1}\n  T2 = {:type :ok, :process 0, :f :read, :value {:x 1}, :index 0}\n\nThen:\n  - T1 < T2, because T1 observed :x = 0, and T2 observed a higher value 1.\n  - However, T2 < T1, because process 0 executed T2 before T1: a contradiction!"]}
             (check {:analyzer (combine monotonic-key-graph
                                         process-graph)}
                     history))))))

(defn read-only-gen
  [v]
  (let [proc (rand-int 100)]
    [{:process proc, :type :ok, :f :read, :value {:x v :y v}}]))

(deftest ^:overflow stackoverflow-test
  (testing "just inducing the depth limit problem"
    (let [history (->> (range)
                       (mapcat read-only-gen)
                       (take 1000000)
                       (map-indexed #(assoc %2 :index %1))
                       vec)]
      (time
       (dotimes [n 1]
         (print "Run" n ":")
         (time (let [r (check {:analyzer monotonic-key-graph} history)]
                 (is (:valid? r)))))))))

(defn graph
  "Takes a history, indexes it, uses the given analyzer function to construct a
  graph+explainer, extracts just the graph, converts it to Clojure, and removes
  indices from the ops."
  [analyzer history]
  (->> history
       history/index
       analyzer
       :graph
       g/->clj
       (map (fn [[k vs]]
              [(dissoc k :index)
               (map #(dissoc % :index) vs)]))
       (into {})))

(deftest realtime-graph-test
  ; We're gonna try a bunch of permutations of diff orders, so we'll index,
  ; analyze, then remove indices, to simplify comparison. This is safe because
  ; all ops are unique without indices.
  (let [o (comp (partial graph realtime-graph) vector)
        a  {:type :invoke, :process 1, :f :read, :value nil}
        a' {:type :ok      :process 1, :f :read, :value 1}
        b  {:type :invoke, :process 2, :f :read, :value nil}
        b' {:type :ok      :process 2, :f :read, :value 2}
        c  {:type :invoke, :process 3, :f :read, :value nil}
        c' {:type :ok      :process 3, :f :read, :value 3}
        d  {:type :invoke, :process 4, :f :read, :value nil}
        d' {:type :ok      :process 4, :f :read, :value 4}
        e  {:type :invoke, :process 5, :f :read, :value nil}
        e' {:type :ok      :process 5, :f :read, :value 5}]
    (testing "empty history"
      (is (= {} (o))))
    (testing "single op"
      (is (= {} (o a a'))))
    (testing "two sequential ops"
      (is (= {a' [b'], b' []}
             (o a a' b b'))))
    (testing "three ops in a row"
      (is (= {a' [b'], b' [c'], c' []}
             (o a a' b b' c c'))))
    (testing "one followed by two concurrent"
      (is (= {a' [b' c'], b' [], c' []}
             (o a a' b c c' b'))))
    (testing "two concurrent followed by one"
      (is (= {a' [c'], b' [c'], c' []}
             (o a b a' b' c c'))))
    (testing "two concurrent followed by two concurrent"
      (is (= {a' [d' c'], b' [d' c'], c' [], d' []}
             (o a b b' a' c d c' d'))))
    (testing "complex"
      ;   ==a==       ==c== ==e==
      ;         ==b==
      ;           ==d===
      ;
      (is (= {a' [b' d'], b' [c'], c' [e'], d' [e'], e' []}
             (o a a' b d b' c d' c' e e'))))))


(deftest ^:perf collapse-graph-test-perf
  ; Generate a random history
  (let [history (atom [])
        threads (real-pmap
                  (fn [p]
                    (dotimes [i 5000]
                      ; Simulate a generation and random key
                      (let [k [(mod i 32) (rand-int 5)]]
                        (swap! history conj {:type :invoke, :process p, :key k })
                        (swap! history conj {:type :ok, :process p, :key k}))))
                    (range 5))
        history (history/index @history)
        graph   (:graph (realtime-graph history))]
    (time
      (g/collapse-graph (comp #{[3 0]} :key) graph))))
