(ns elle.bfs-test
  (:require [bifurcan-clj [core :as b]
                          [list :as bl]
                          [graph :as bg]
                          [set :as bs]]
            [clojure [pprint :refer [pprint]]]
            [clojure.core [protocols :as p]]
            [elle [bfs :refer :all]
                  [graph :as g]
                  [rels :as rels :refer :all]
                  [txn :as t]]
            [jepsen [history :as h]]
            [clojure.test :refer :all]
            [clj-commons.slingshot :refer [try+ throw+]])
  (:import (io.lacuna.bifurcan IMap
                               Map)
           (elle BFSPath)))

; Just for debugging
(extend-protocol p/Datafiable
  elle.BFSPath
  (datafy [p]
    {:ops (mapv :index (.ops p))}))

(defn op
  "Takes a number, returns an Op with that as its index."
  [index]
  (h/op {:index index}))

(defn indices
  "Takes a collection of Ops and extracts their indexes."
  [ops]
  (when ops
    (mapv :index ops)))

(defn op-graph
  "Takes a graph of integers and lifts them into a graph of Ops where the
  integers are their index fields. We do this because our graph search is
  optimized for Ops, but we don't want to write a zillion ops in testing."
  [g]
  (g/map-vertices op g))

(deftest packed-rels-set-test
  (are [rels] (= rels (-> rels bs/from BFSPath/packRelsSet BFSPath/unpackRelsSet set))
       #{}
       #{ww}
       #{rw rwp}
       #{ww realtime}
       #{ww process realtime}
       #{ww wwp wr realtime}))

(deftest realtime-test
  ; Realtime is tricky--it occupies the high bit in our byte representation of
  ; bitrels, and that causes sign extension bugs when Clojure emits
  ; auto-widening code.
  (testing "G0"
    (let [p (spec->path (t/cycle-anomaly-specs :G0-realtime))]
      (is (= (.rels (union ww wwp realtime)) (.legal p)))
      (is (= #{realtime} (set (BFSPath/unpackRelsSet (.want p)))))))
  (testing "G1c"
    (let [p (spec->path (t/cycle-anomaly-specs :G1c-realtime))]
      (is (= (.rels (union ww wwp wr wrp realtime)) (.legal p)))
      (is (= #{realtime (rels/union wr wrp)} (set (BFSPath/unpackRelsSet (.want p))))))))

(defn s
  "Takes an anomaly spec type and a series of [from-idx to-idx rel] triples.
  Builds an op graph, searches it for a cycle, and returns the cycle's
  indices."
  [spec-type & triples]
  (-> (reduce (partial apply g/link) (g/digraph) (partition 3 triples))
      op-graph
      (search (t/cycle-anomaly-specs spec-type))
      indices))

(deftest g0-test
  (testing "empty"
    (is (= nil (s :G0))))

  (testing "simple"
    (is (= [2 1 2] (s :G0
                      1 2 ww
                      2 1 ww))))

  (testing "longer"
       (is (= [3 1 2 3] (s :G0
                           1 2 ww
                           2 3 ww
                           3 1 ww))))

  (testing "not present"
    (is (= nil (s :G0
                  1 2 ww
                  2 1 rw
                  2 1 wr))))

  (testing "indirect"
    (is (= [3 1 2 3] (s :G0
                        1 2 ww
                        2 3 ww
                        3 1 ww
                        2 1 rw
                        3 2 wr)))))

(deftest g1c-test
  (testing "simple"
       (is (= [2 1 2] (s :G1c
                         1 2 ww
                         2 1 wr))))

  (testing "hidden"
    (is (= [3 1 2 3]
           (s :G1c
              1 2 ww
              2 3 wr
              2 1 rw
              3 1 wr
              3 2 rw)))))

(deftest g1c-realtime-test
  ; This is trickier: we have to get a realtime edge and a *separate* wr or wrp
  ; edge. It's not enough for them to be combined!
  (testing "simple"
    (is (= [2 1 2]
           (s :G1c-realtime
              1 2 wrp
              2 1 realtime))))

  (testing "not present"
    (is (= nil
           (s :G1c-realtime
              1 2 ww
              2 1 realtime
              2 1 wrp)))))

(deftest g-single-test
  (testing "simple"
    (is (= [2 1 2] (s :G-single
                      1 2 ww
                      2 1 rw))))

  (testing "hidden"
    (is (= [1 2 3 4 1]
           (s :G-single
              1 2 rw
              2 1 rw
              2 3 ww
              3 1 rw
              3 4 wr
              4 1 wr)))))

(deftest g-nonadjacent-test
  (testing "hidden"
    (is (= [3 4 1 2 3]
           (s :G-nonadjacent
              ; Cycle
              1 2 rw
              2 3 ww
              3 4 rw
              4 1 wr
              ; But also a shorter g-single
              2 1 ww
              ; And a shorter G0
              3 2 ww)))))

(deftest g2-test
  (testing "hidden"
    (is (= [3 4 1 2 3]
           (s :G2
              ; G2 Cycle
              1 2 ww
              2 3 wr
              3 4 rw
              4 1 rw
              ; G0
              2 1 ww
              ; G-single
              4 3 wr)))))

(deftest g0-realtime-test
  (testing "hidden"
    (is (= [2 3 1 2]
           (s :G0-realtime
              ; G0-realtime
              1 2 ww
              2 3 realtime
              3 1 ww
              ; G0
              2 1 ww)))))

(deftest g-nonadjacent-process-test
  (testing "hidden"
    (is (= [3 4 1 2 3]
           (s :G-nonadjacent-process
              ; G-nonadjacent-process
              1 2 rw
              2 3 process
              3 4 rw
              4 1 ww
              ; G-single
              4 3 wr
              ; G-nonadjacent
              2 5 wr
              5 6 rw
              6 1 ww)))))
