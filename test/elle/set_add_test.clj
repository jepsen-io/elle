(ns elle.set-add-test
  (:require [clojure [pprint :refer [pprint]]
                     [test :refer :all]
                     [set  :as set]]
            [clojure.test.check :as tc]
            [clojure.test.check [clojure-test :refer [defspec]]
                                [generators :as gen]
                                [properties :as prop]]
            [elle [explanation :as expl]
                  [graph :as g]
                  [recovery :as rec]
                  [set-add :refer :all]
                  [txn-graph :as tg]
                  [version-graph :as vg]]
            [knossos.history :as history]))

(defn op
  "Generates an operation from a string language like so:

  ax1       append 1 to x
  ry12      read y = [1 2]
  ax1ax2    append 1 to x, append 2 to x"
  ([string]
  (let [[txn mop] (reduce (fn [[txn [f k v :as mop]] c]
                            (case c
                              \a [(conj txn mop) [:add]]
                              \r [(conj txn mop) [:r]]
                              \x [txn (conj mop :x)]
                              \y [txn (conj mop :y)]
                              \z [txn (conj mop :z)]
                              (let [e (Long/parseLong (str c))]
                                [txn [f k (case f
                                            :add e
                                            :r   (conj (or v #{}) e))]])))
                          [[] nil]
                          string)
        txn (-> txn
                (subvec 1)
                (conj mop))]
    {:type :ok, :value txn}))
  ([process type string]
   (assoc (op string) :process process :type type)))

(defn pair
  "Takes a completed op and returns an [invocation, completion] pair."
  [completion]
  [(-> completion
       (assoc :type :invoke)
       (update :value (partial map (fn [[f k v :as mop]]
                                        (if (= :r f)
                                          [f k nil]
                                          mop)))))
   completion])


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

(deftest empty-test
  (let [r (check {} [])]
    (is (= [] (:history r)))
    (is (= (g/digraph) (tg/graph (:txn-graph r))))))

(deftest single-write-read-test
  (let [[t1 t1'] (pair (op "ax1"))
        [t2 t2'] (pair (op "rx1"))
        h (history/index [t1 t1' t2 t2'])
        [t1 t1' t2 t2'] h
        r (check {} h)
        rec (:recovery r)
        vg (:version-graph r)
        tg (:txn-graph r)]
    (pprint vg)
    ; We can show that ax1 produced the set #{1}
    (is (= #{1} (rec/write->version rec (first (:value t1')))))
    ; And that #{1} was produced by ax1
    (is (= [t1' (first (:value t1'))] (rec/version->write rec :x #{1})))

    ; We know #{1} came after #{}
    (is (= {#{} #{#{1}}
            #{1} #{}}
           (g/->clj (vg/graph vg :x))))

    ; And we can infer a write-read dependency here
    (is (= {t1' #{t2'}
            t2' #{}}
           (g/->clj (tg/graph tg))))))

(deftest ambiguous-writes-both-read-test
  (let [[t1 t1'] (pair (op "ax1"))
        [t2 t2'] (pair (op "ax2"))
        [t3 t3'] (pair (op "rx12"))
        h (history/index [t1 t1' t2 t2' t3 t3'])
        [t1 t1' t2 t2' t3 t3'] h
        r (check {} h)
        rec (:recovery r)]
    ; We can't show what write generated {1 2}, or whether {1} or {2} even
    ; existed.
    (is (nil? (rec/version->write rec :x #{1})))
    (is (nil? (rec/version->write rec :x #{2})))
    (is (nil? (rec/version->write rec :x #{1 2})))
    (is (nil? (rec/write->version rec (first (:value t1')))))
    (is (nil? (rec/write->version rec (first (:value t2')))))

    ; But we CAN infer version relationships here. We know #{} (indirectly)
    ; precedes #{1 2}, because #{} is the initial state.
    (is (= {#{} #{#{1 2}}
            #{1 2} #{}}
           (g/->clj (vg/graph (:version-graph r) :x))))

    ; We can't actually infer any relationships from this graph *directly*,
    ; because we don't have recoverability for the writes. However, our
    ; indirect wr and rw inference CAN identify these edges, which gives us the
    ; following > shaped graph.
    (is (= {t1' #{t3'}
            t2' #{t3'}
            t3' #{}}
           (g/->clj (tg/graph (:txn-graph r)))))

    (is (= {:type :indirect-wr
            :write [:add :x 1]
            :read  [:r :x #{1 2}]}
           (expl/->data (tg/explain (:txn-graph r) t1' t3'))))))
