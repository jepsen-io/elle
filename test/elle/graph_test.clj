(ns elle.graph-test
  (:require [bifurcan-clj [core :as b]
                          [graph :as bg]
                          [set :as bs]]
            [clojure [pprint :refer [pprint]]]
            [elle [core-test :as core-test]
                  [graph :refer :all]
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

(def ops
  "An infinite series of ops with indices 0, 1, 2, ..."
  (map op (range)))

(defn op-graph
  "Takes a graph of integers and lifts them into a graph of Ops where the
  integers are their index fields. We do this because our graph search is
  optimized for Ops, but we don't want to write a zillion ops in testing."
  [g]
  (map-vertices op g))

(def og core-test/op-graph)

(defn indices
  "Takes a collection of Ops and extracts their indexes."
  [ops]
  (mapv :index ops))

(defn prng
  "Prints a graph, just indices."
  [g]
  (println (map-vertices :index g)))

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
  (let [[x1 y1 y2 z1 z2 z3 q r s] ops
        a (og x1 ww y1
              x1 ww y2
              r  ww s)
        b (og y1 ww z1
              y1 ww z2
              y2 ww z3
              r  ww q
              q  ww r)]
    (is (= (og x1 none z1
               x1 none z2
               x1 none z3)
           (sequential-composition a b)))))

(deftest sequential-composition-omit-intermediates-test
  ; A neat little G2 graph that found a bug, I think
  (let [[t1 t2 t3 t4] ops
        g (og t1 ww t3
              t1 wr t4
              t2 rw t1
              t3 rw t2
              t3 rw t4
              t4 rw t3)
        g-ww+wr (project-rels (union ww wr) g)
        g-rw    (project-rels rw g)]
    (is (= (og t1 ww t3
               t1 wr t4)
           g-ww+wr))
    (is (= (og t2 rw t1
               t3 rw t2
               t3 rw t4
               t4 rw t3)
           g-rw))
    ; The sequential composition `ww+wr ; rw`, if we followed the mathematical
    ; definition, would be:
    ;
    ; t1 -> t2 (via t3)
    ; t1 -> t3 (via t4)
    ; t1 -> t4 (via t3)
    ;
    ; Which would make the sequential extension ww+wr U (ww+wr ; rw):
    ;
    ; t1 -> t2
    ; t1 -> t3
    ; t1 -> t4
    ;
    ; Note that both these graphs are acyclic. We thought we'd be clever and
    ; retain the intermediate vertices in the sequential composition. But this
    ; causes us to include extra edges in the graph. In particular, this pair
    ; of double-hops:
    ;
    ; t1 ww t3 rw t4   should collapse to t1 -> t4
    ; t1 wr t4 rw t3   should collapse to t1 -> t3
    ;
    ; ... if we retain the original edges, we include an rw cycle between t3
    ; and t4! This is *not* acyclic!
    ;
    ; This is why we must omit intermediate edges.
    (is (= (og t1 none t2  ; Via t3
               t1 none t3  ; Via t4
               t1 none t4) ; Via t3
           (sequential-composition g-ww+wr g-rw)))
    (is (= (og t1 none t2  ; Via t3
               t1 ww   t3  ; Via t4
               t1 wr   t4) ; Via t3
           (sequential-extension g-ww+wr g-rw)))))

(deftest topo-depths-test
  (is (= {:a1 0 :a2 0
          :b1 1
          :c1 2 :c2 2}
         (topo-depths (map->dag {:a1 [:b1]
                                 :a2 [:b1]
                                 :b1 [:c1 :c2]})))))
