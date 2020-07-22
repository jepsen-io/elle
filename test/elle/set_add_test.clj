(ns elle.set-add-test
  (:require [clojure [pprint :refer [pprint]]
                     [test :refer :all]
                     [set  :as set]]
            [clojure.test.check :as tc]
            [clojure.test.check [clojure-test :refer [defspec]]
                                [generators :as gen]
                                [properties :as prop]]
            [elle [graph :as g]
                  [set-add :refer :all]]))

(defn naive-version-graph-for-key
  "A simple implementation which finds the version graph for a key by
  transitively comparing every version to every other version."
  [versions]
  (let [versions (conj versions #{})] ; Always an empty version
    (->> (for [a versions
               b versions]
           (when (and (not= a b) (set/subset? a b))
             [a b]))
         (remove nil?)
         (reduce (fn [g [a b]]
                   (g/link g a b))
                 (g/linear (g/digraph)))
         g/forked)))

(defn transitive-closure?
  "Is graph b the transitive closure of graph a?"
  [a b]
  ; We compute this by doing a trivial bfs for all vertices downstream of a
  ; given vertex in a, and checking that those are exactly the out vertices of
  ; b.
  ; Sometimes equality comparison throws a ClassCastException:
  ; io.lacuna.bifurcan.Map cannot be cast to java.lang.Void, and I'm not sure
  ; why.
  ; (prn :vertex-check (= (g/->clj (g/vertices a)) (g/->clj (g/vertices b))))
  (and (= (g/->clj (g/vertices a)) (g/->clj (g/vertices b)))
       (every? (fn [v]
                 (= (-> (g/bfs (partial g/out a) [v])
                        set
                        (disj v))
                    (g/->clj (g/out b v))))
               (g/vertices a))))

(deftest version-graph-test
  (testing "empty"
    (is (= {} (-> #{} version-graph-for-key g/->clj))))

  (testing "linear chain"
    (is (= {#{}     #{#{1}}
            #{1}    #{#{1 2}}
            #{1 2}  #{#{1 2 3}}
            #{1 2 3} #{}}
           (-> #{#{1} #{1 2} #{1 2 3}}
               version-graph-for-key
               g/->clj))))

  (testing "fork, join, fork, join"
    (is (= {#{}        #{#{1} #{2}}
            #{1}       #{#{1 2}}
            #{2}       #{#{1 2}}
            #{1 2}     #{#{1 2 3} #{1 2 4}}
            #{1 2 3}   #{#{1 2 3 4 5}}
            #{1 2 4}   #{#{1 2 3 4 5}}
            #{1 2 3 4 5} #{}}
           (-> #{#{1} #{2} #{1 2} #{1 2 3} #{1 2 4} #{1 2 3 4 5}}
               version-graph-for-key
               g/->clj)))))

(deftest ^:perf version-graph-perf-test
  ; Simulate a pool of n actors conjing into their local copies, and
  ; periodically gossiping with peers.
  (let [n      1000
        actors 2
        versions (first
                   (reduce (fn [[versions actor-states] x]
                           (let [actor (rand-int (count actor-states))
                                 version (nth actor-states actor)
                                 ; Gossip
                                 version' (into version
                                                (rand-nth actor-states))
                                 ; And update
                                 version' (conj version' x)]
                             [(conj versions version')
                              (assoc actor-states actor version')]))
                         [[] (vec (repeat actors #{}))]
                         (range n)))
        versions-set (set versions)
        t0 (System/nanoTime)
        [vg calls] (binding [*calls* (atom 0)]
                     [(version-graph-for-key versions-set) @*calls*])
        t1 (System/nanoTime)
        dt (/ (- t1 t0) 1e9)
        ;nvg (naive-version-graph-for-key versions-set)
        ]
    ;(pprint :versions)
    ;(pprint versions)
    ;(println "took" dt "seconds" (str "(" calls " subset comparisons)"))
    ;(println (count (seq (.edges vg))) "/" (* (count versions) (count versions) 0.5))
    ;(println (count (seq (.edges vg))) "/" (count (seq (.edges nvg))))
    (is (< 10000 (/ calls dt)))
    (is (< dt 3))
    ))

(defspec version-graph-for-key-spec 100
  ; This spec verifies that our optimized implementation which computes the
  ; version graph for a key computes a graph which is a transitive reduction of
  ; the full subset graph, as computed by naive-version-graph-for-key.
  (prop/for-all [versions (gen/set (gen/set gen/int))]
                (let [vg  (binding [*out* (java.io.StringWriter.)]
                            (version-graph-for-key versions))
                      nvg (naive-version-graph-for-key versions)
                      tc? (transitive-closure? vg nvg)]
                  ;(prn :version-count (count versions)
                  ;     :vg-size (count (seq (.edges vg)))
                  ;     :nvg-size (count (seq (.edges nvg))))
                  (when-not tc?
                    (prn)
                    (prn)
                    (prn :fault!)
                    (prn :versions versions)
                    (prn :vg- (g/->clj vg) vg)
                    (prn :nvg (g/->clj nvg) nvg)
                    (prn)
                    (version-graph-for-key versions)
                    (prn :end-trace)
                    (prn)
                    (prn))
                  tc?)))



