(ns elle.txn-test
  (:require [bifurcan-clj [core :as b]
                          [set :as bs]]
            [clojure [pprint :refer [pprint]]
                     [test :refer :all]]
            [elle [graph :as g]
                  [txn :refer :all]]
            [jepsen [history :as h]]))

(defn valid-mop?
  [[f k v]]
  (is (#{:r :w} f))
  (is (integer? k))
  (case f
    :r (is (= nil v))
       (is (integer? v))))

(deftest wr-txns-test
  (let [txns (take 100 (wr-txns {:key-count 3}))
        mops (mapcat identity txns)
        ks   (map second mops)
        key-dist (frequencies ks)]
    (is (every? vector? txns))
    (is (every? #(<= 1 (count %) 2) txns))
    (is (every? valid-mop? mops))
    ; This is gonna vary by RNG, but there are 3 keys per pool by default,
    ; and their frequency (for the first 3 anyway) should be in ascending order.
    (is (< (key-dist 0) (key-dist 1) (key-dist 2)))))

(deftest cycle-exists-subgraph-test
  ; A simple G-single; stresses the AST interpreter for subgraphs, union,
  ; composition, extension.
  (let [[op0 op1 op2] (map (fn [i] (h/op {:index i})) (range 3))
        g (-> (g/op-rel-graph)
              (g/link op0 op1 :wr)
              (g/link op1 op2 :ww)
              (g/link op2 op0 :rw))]
    (testing "simple keyword"
      (is (= (-> (g/named-graph (bs/from [:ww]))
                 (g/link op1 op2))
             (cycle-exists-subgraph g :ww))))
    (testing "union"
      (is (= (-> (g/op-rel-graph)
                 (g/link op0 op1 :wr)
                 (g/link op1 op2 :ww))
             (cycle-exists-subgraph g [:union :ww :wr]))))
    (testing "composition"
      (is (= (-> (g/digraph)
                 (g/link op1 op2)  ; Through ww-rw
                 (g/link op2 op0)) ; Through ww-rw
             (cycle-exists-subgraph g [:composition :ww :rw]))))
    (testing "extension"
      (is (= (-> (g/op-rel-graph)
                 (g/link op0 op1 :wr) ; Original wr edge
                 (g/link op1 op2 :ww) ; Original ww edge
                 (g/link op1 op2 :elle.graph/seq-comp)  ; Throw ww-rw
                 (g/link op2 op0 :elle.graph/seq-comp)) ; Through ww-rw
             (cycle-exists-subgraph g [:extension [:union :ww :wr] :rw]))))))

(deftest cycle-exists-cases-G-single-test
  ; A simple G-single; stresses the AST interpreter for subgraphs and also the
  ; sequential extension mechanism
  (let [[op0 op1] (map (fn [i] (h/op {:index i})) (range 2))
        g (-> (g/op-rel-graph)
              (g/link op0 op1 :ww)
              (g/link op1 op0 :rw))
        cases (cycle-exists-cases g)]
    (is (= [{:type :PL-SI-cycle-exists
             :not  :snapshot-isolation
             :subgraph [:extension [:union :ww :wr] :rw]
             :scc-size 2
             :scc #{0 1}}]
           cases))))
