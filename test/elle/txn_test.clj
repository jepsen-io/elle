(ns elle.txn-test
  (:require [bifurcan-clj [core :as b]
                          [set :as bs]]
            [clojure [pprint :refer [pprint]]
                     [test :refer :all]]
            [elle [graph :as g]
                  [graph-test :refer [ops og]]
                  [rels :refer :all]
                  [txn :refer :all]]
            [jepsen [history :as h]
                    [random :as rand]]))

(defn valid-mop?
  [[f k v]]
  (is (#{:r :w} f))
  (is (integer? k))
  (case f
    :r (is (= nil v))
       (is (integer? v))))

(defn valid-txns?
  "Basic validation on transactions for wr-txns-test"
  [txns]
  (is (every? vector? txns))
  (is (every? #(<= 1 (count %) 4) txns))
  (let [mops (mapcat identity txns)]
    (is (every? valid-mop? mops))
    ; Grouped by key, each write should be distinct
    (doseq [[k mops] (->> mops
                          (filter (comp #{:w} first))
                          (group-by second))]
      (is (= (count mops)
             (count (set (map peek mops))))))))

(defn key-dist
  "Computes the frequency distribution of keys in a series of txns."
  [txns]
  (->> txns
       (mapcat identity)
       (map second)
       frequencies
       (into (sorted-map))))

(defn writes-per-key
  "Computes a map of keys to the number of writes of that key in a series of txns."
  [txns]
  (->> txns
       (mapcat identity)
       (filter (comp #{:w} first))
       (map second)
       frequencies
       (into (sorted-map))))

(deftest wr-txns-test
  (rand/with-seed 53
    ; We're intentioanally picking small histories here so we get a good look
    ; at the distributions *before* they saturate.
    (testing "exponential"
      (let [txns (take 100 (wr-txns {:key-count 3, :key-dist :exponential}))]
        (valid-txns? txns)
        (is (= {0 11, 7 59, 1 1, 4 47, 6 26, 3 15, 2 23, 9 15, 5 39, 8 16}
               (key-dist txns)))))

    (testing "uniform"
      (let [txns (take 100 (wr-txns {:key-count 3, :key-dist :uniform}))]
        (valid-txns? txns)
        (is (= {0 84, 1 72, 2 84, 3 8, 4 1, 5 11}
               (key-dist txns)))))

    (testing "zipf"
      (let [txns (take 100 (wr-txns {:key-count 3, :key-dist :zipf}))]
        (valid-txns? txns)
        (is (= {0 185, 1 62, 2 22, 3 1}
               (key-dist txns)))))

    (testing "key rotation"
      (let [txns (take 100 (wr-txns {:key-count 1, :max-writes-per-key 5}))]
        (valid-txns? txns)
        ; Never more than 5
        (is (every? (partial >= 5) (vals (writes-per-key txns))))
        ; And the distribution is zipfian
        (is (= {1 20, 4 5, 2 17, 3 4, 5 5}
               (frequencies (vals (writes-per-key txns)))))))))

(defn fg
  "Wraps a graph in a filtered-graphs fn."
  [g]
  #(g/project-rels % g))

(deftest cycle-exists-subgraph-test
  ; A simple G-single; stresses the AST interpreter for subgraphs, union,
  ; composition, extension.
  (let [[op0 op1 op2 op3] ops
        g (-> (g/op-digraph)
              (g/link op0 op1 wr)
              (g/link op1 op2 ww)
              (g/link op2 op0 rw)
              ; Double-rw link to op3
              (g/link op0 op3 rw))
        fg (fg g)]
    (testing "simple keyword"
      (is (= (-> (g/op-digraph)
                 (g/link op1 op2 ww))
             (cycle-exists-subgraph fg ww))))
    (testing "union"
      (is (= (-> (g/op-digraph)
                 (g/link op0 op1 wr)
                 (g/link op1 op2 ww))
             (cycle-exists-subgraph fg [:union ww wr]))))
    (testing "composition"
      (is (= (og op1 none op0) ; Through ww-rw
             (cycle-exists-subgraph fg [:composition ww rw]))))
    (testing "extension"
      (is (= (og op0 wr op1    ; Original wr edge
                 op1 ww op2    ; Original ww edge
                 op1 none op0) ; Through ww-rw
             (cycle-exists-subgraph fg [:extension [:union ww wr] rw]))))))

(deftest cycle-exists-cases-G-single-test
  ; A simple G-single; stresses the AST interpreter for subgraphs and also the
  ; sequential extension mechanism
  (let [[op0 op1] ops
        g (og op0 ww op1
              op1 rw op0)
        cases (cycle-exists-cases (fg g))]
    (is (= [{:type      :PL-SI-cycle-exists
             :not       :snapshot-isolation
             :subgraph  [:extension [:union :ww :wwp :wr :wrp]
                         [:union :rw :rwp]]
             :scc-size  1 ; Because of our sequential extension trick!
             :scc       #{0}}
            {:type      :PL-2.99-cycle-exists
             :not       :repeatable-read
             :subgraph  [:union :ww :wwp :wr :wrp :rw]
             :scc-size  2
             :scc       #{0 1}}]
           cases))))
