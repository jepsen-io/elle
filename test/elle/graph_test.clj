(ns elle.graph-test
  (:require [bifurcan-clj [core :as b]
                          [graph :as bg]
                          [set :as bs]]
            [clojure [pprint :refer [pprint]]]
            [elle [graph :refer :all]
                  [rels :refer :all]]
            [jepsen [history :as h]
                    [txn :as txn]]
            [clojure.test :refer :all]
            [slingshot.slingshot :refer [try+ throw+]])
  (:import (io.lacuna.bifurcan IMap
                               Map)))

(defn op
  "Takes a number, returns an Op with that as its index."
  [index]
  (h/op {:index index}))

(defn op-graph
  "Takes a graph of integers and lifts them into a graph of Ops where the
  integers are their index fields. We do this because our graph search is
  optimized for Ops, but we don't want to write a zillion ops in testing."
  [g]
  (map-vertices op g))

(defn indices
  "Takes a collection of Ops and extracts their indexes."
  [ops]
  (mapv :index ops))

(deftest tarjan-test
  (let [tarjan (comp set tarjan)]
    (testing "Can analyze integer graphs"
      ;; From wikipedia
      (let [graph {1 #{2}   2 #{3}
                   3 #{1}   4 #{2 3 5}
                   5 #{4 6} 6 #{3 7}
                   7 #{6}   8 #{7 8}}]
        (is (= (tarjan graph)
               #{#{3 2 1} #{6 7} #{5 4}})))

      ;; Big lööp
      (let [graph {1 #{2} 2 #{3}
                   3 #{4} 4 #{5}
                   5 #{6} 6 #{7}
                   7 #{8} 8 #{1}}]
        (is (= (tarjan graph)
               #{#{1 2 3 4 5 6 7 8}})))

      ;; smol lööps
      (let [graph {0 #{1} 1 #{0}
                   2 #{3} 3 #{2}
                   4 #{5} 5 #{4}
                   6 #{7} 7 #{6}}]
        (is (= (tarjan graph)
               #{#{0 1} #{2 3}
                 #{4 5} #{6 7}}))))

    (testing "Can flag unlinked as solo sccs"
      (let [graph {1 #{} 2 #{}
                   3 #{} 4 #{}}]
        (is (= (tarjan graph)
               #{}))))

    (testing "Can flag self-ref as solo sccs"
      (let [graph {1 #{1} 2 #{2}
                   3 #{3} 4 #{4}}]
        (is (= (tarjan graph)
               #{}))))

    (testing "can check monotonic loop histories"
      ;; Linear
      (let [graph {0 #{1} 1 #{2}
                   2 #{3} 3 #{}}]
        (is (= (tarjan graph)
               #{})))

      ;; Loop
      (let [graph {0 #{1} 1 #{2}
                   2 #{1} 3 #{}}]
        (is (= (tarjan graph)
               #{#{1 2}})))

      ;; Linear but previously bugged case
      (let [graph {0 #{1} 1 #{2}
                   2 #{}  3 #{2 1}}]
        (is (= (tarjan graph)
               #{})))

      (let [graph {0 #{1} 1 #{0}
                   2 #{}  3 #{2 1}}]
        (is (= (tarjan graph)
               #{#{0 1}})))

      ;; FIXME Busted case
      (let [graph {1 #{7 3 5} 3 #{7 5}
                   5 #{}      7 #{3 5}}]
        (is (= (tarjan graph)
               #{#{3 7}}))))

    (testing "can check a one node graph"
      (let [graph {0 #{}}]
        (is (= (tarjan graph)
               #{}))))

    (testing "busted"
      (let [graph {1 #{7 3 5} 3 #{7 5}
                   5 #{}      7 #{3 5}}]
        (is (= (tarjan graph)
               #{#{3 7}}))))

    (testing "wiki"
      (let [graph {1 #{2}   2 #{3}
                   3 #{1}   4 #{2 3 5}
                   5 #{4 6} 6 #{3 7}
                   7 #{6}   8 #{7 8}}]
        (is (= (tarjan graph)
               #{#{3 2 1} #{6 7} #{5 4}}))))))

(deftest path-shells-test
  (let [g     (map->bdigraph {0 [1 2] 1 [3] 2 [3] 3 [0]})
        paths (path-shells g [[0]])]
    (is (= [[[0]]
            [[0 1] [0 2]]
            [[0 1 3]]
            [[0 1 3 0]]]
           (take 4 paths)))))

(deftest find-cycle-test
  (let [g (map->bdigraph {0 [1 2]
                          1 [4]
                          2 [3]
                          3 [4]
                          4 [0 2]})]
    (testing "basic cycle"
      (is (= [3 4 2 3]
             (indices (find-cycle (op-graph g))))))

    ; We may restrict a graph to a particular relationship and look for cycles
    ; in an SCC found in a larger graph; this should still work.
    (testing "scc without cycle in graph"
      (is (= nil
             (find-cycle (op-graph (bg/select g (bs/from #{0 2 4})))))))))

(deftest fallback-cycle-test
  (is (= [2 3 4 2] (fallback-cycle
                     (map->bdigraph {1 [2]
                                     2 [3]
                                     3 [4]
                                     4 [2]})))))

(deftest link-test
  (let [g (-> (digraph)
              (link 1 2 ww)
              (link 1 2 wr))]
    (is (= (union ww wr) (->clj (bg/edge g 1 2))))))

(deftest collapse-graph-test
  (testing "simple"
    (is (= (map->bdigraph {1 [3]})
           (->> (map->bdigraph {1 [2]
                                2 [3]})
                (collapse-graph odd?)))))

  (testing "complex"
    (is (= (map->bdigraph {1 [1 5 7]
                           3 [1 5 7 9]})
           (->> (map->bdigraph {1 [4]
                                3 [4 9]
                                4 [5 6 7]
                                6 [1]})
                (collapse-graph odd?))))))

(deftest map-vertices-test
  (testing "empty"
    (is (= (map->bdigraph {}) (map-vertices identity (map->bdigraph {})))))

  (testing "complex"
    (is (= (-> (b/linear (digraph))
               (link 1 1 ww)
               (link 1 2 wr)
               (link 1 2 rw))
           (map-vertices {1 1, 2 1, 3 2, 4 2}
                         (-> (b/linear (digraph))
                             (link 1 2 ww) ; becomes a self-edge
                             (link 1 3 wr) ; becomes 1->2
                             (link 2 4 rw) ; becomes 1->2
                             ))))))

(deftest rel-graph-test
  (let [[o0 o1 o2 o3 o4 o5 o6] (map #(h/op {:index %}) (range 7))
        a (-> (op-digraph)
              (link o1 o2 ww)
              (link o1 o3 ww))
        b (-> (op-digraph)
              (link o1 o2 wr)
              (link o1 o4 wr)
              (link o5 o6 wr))
        g (reduce digraph-union (digraph-union) [a b])]
    (is (= true (.isDirected g)))
    (is (= #{o1 o2 o3 o4 o5 o6} (->clj (.vertices g))))
    (is (= a (project-rels ww g)))
    (is (= b (project-rels wr g)))
    (is (= g (project-rels (union ww wr realtime) g)))
    (is (= #{o2 o3 o4} (->clj (.out g o1))))
    (is (thrown? IllegalArgumentException (->clj (.out g o0))))
    (is (= #{o6} (->clj (.out g o5))))))

(deftest sequential-composition-test
  (let [[x1 y1 y2 z1 z2 z3 q r s] (map (fn [i] (h/op {:index i})) (range 8))
        a (-> (bg/digraph)
              (bg/link x1 y1)
              (bg/link x1 y2)
              (bg/link r  s))
        b (-> (bg/digraph)
              (bg/link y1 z1)
              (bg/link y1 z2)
              (bg/link y2 z3)
              (bg/link r  q)
              (bg/link q  r))]
    (is (= (-> (bg/digraph)
               (bg/link x1 y1)
               (bg/link x1 y2)
               (bg/link y1 z1)
               (bg/link y1 z2)
               (bg/link y2 z3))
           (sequential-composition a b)))))

(deftest topo-depths-test
  (is (= {:a1 0 :a2 0
          :b1 1
          :c1 2 :c2 2}
         (topo-depths (map->dag {:a1 [:b1]
                                 :a2 [:b1]
                                 :b1 [:c1 :c2]})))))
