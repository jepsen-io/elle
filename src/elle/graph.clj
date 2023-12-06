(ns elle.graph
  "Supporting functions for working efficiently with graphs. This is a
  lightweight layer around Bifurcan's graph datatypes and related structures.

  We perform as much of our heavy lifting as possible in Bifurcan structures,
  then coerce them back to Clojure data structures for analysis, serialization,
  pretty-printing, etc."
  (:require [bifurcan-clj [core :as b]
                          [graph :as bg]
                          [set :as bs]]
            [clojure.tools.logging :refer [info error warn]]
            [clojure.core.reducers :as r]
            [dom-top.core :refer [loopr]]
            [elle.util :refer [map-vals maybe-interrupt]]
            [jepsen.history :as h]
            [jepsen.history.fold :refer [loopf]])
  (:import (elle BitRels)
           (io.lacuna.bifurcan DirectedGraph
                               DirectedAcyclicGraph
                               Graphs
                               ICollection
                               IEdge
                               IEntry
                               IList
                               IMap
                               ISet
                               IGraph
                               Set
                               SortedMap)
           (java.util.function BinaryOperator
                               Function)
           (jepsen.history Op)))

; Convert stuff back to Clojure data structures. Mostly used for testing.
(defprotocol ToClj
  (->clj [x]))

(extend-protocol ToClj
  IList
  (->clj [l]
    (iterator-seq (.iterator l)))

  IEdge
  (->clj [e]
    {:from  (.from e)
     :to    (.to e)
     :value (->clj (.value e))})

  IMap
  (->clj [s]
    (let [iter (.iterator s)]
      (loop [m (transient {})]
        (if (.hasNext iter)
          (let [kv ^IEntry (.next iter)]
            (recur (assoc! m (.key kv) (->clj (.value kv)))))
          (persistent! m)))))


  ISet
  (->clj [s]
  (let [iter (.iterator s)]
    (loop [s (transient #{})]
      (if (.hasNext iter)
        (recur (conj! s (->clj (.next iter))))
        (persistent! s)))))

  IGraph
  (->clj [g]
    (->> (.vertices g)
         ->clj
         (map (fn [vertex] [vertex (->clj (.out g vertex))]))
         (into {})))

  clojure.lang.IPersistentMap
  (->clj [m]
    (into {} (map (fn [[k v]] [(->clj k) (->clj v)]) m)))

  jepsen.history.Op
  (->clj [m]
    (into m (map-vals ->clj m)))

  Object
  (->clj [x] x)

  nil
  (->clj [x] x))

(def index-hash
  "Java functional wrapper for hashing ops by index"
  (b/functional h/index-hash))

(def index=
  "Java functional wrapper for comparing ops by index"
  (b/functional h/index=))

(defn ^DirectedGraph digraph
  "Constructs a fresh directed graph."
  []
  (DirectedGraph.))

(defn ^DirectedGraph op-digraph
  "A digraph over operations. Uses the index of operations to massively speed
  up equality."
  []
  (DirectedGraph. index-hash index=))

(defn contains-node?
  "Is this node in the graph?"
  [^IGraph g v]
  (.contains (bg/vertices g) v))

(defn in
  "Inbound edges to v in graph g. Returns nil instead of throwing when given a
  vertex not in the graph."
  [^IGraph g v]
  (try (.in g v)
       (catch IllegalArgumentException e)))

(defn ^Set out
  "Outbound vertices from v in graph g. Returns nil instead of throwing when
  given a vertex not in the graph."
  [^IGraph g v]
  (try (.out g v)
       (catch IllegalArgumentException e)))

(def ^BinaryOperator merge-last-write-wins
  "A binary operator that takes a, b -> b"
  (reify BinaryOperator
    (apply [_ a b] b)))

(def ^BinaryOperator union-bset
  "A binary operator performing bifurcan set union on the values of edges."
  (reify BinaryOperator
    (apply [_ a b]
      (cond (nil? a) b
            (nil? b) a
            true    (.union ^ISet a ^ISet b)))))

(def ^BinaryOperator union-rels
  "A binary operator which unions two BitRels sets."
  (reify BinaryOperator
    (apply [_ a b]
      (cond (nil? a) b
            (nil? b) a
            true     (.union ^BitRels a ^BitRels b)))))

(defn link
  "Helper for linking Bifurcan graphs of ops. Optionally takes a BitRels
  relationship, which is unioned into BitRels of the edge."
  ([^IGraph graph node succ]
   ;(assert (not (nil? node)))
   ;(assert (not (nil? succ)))
   (.link graph node succ))
  ([^IGraph graph node succ relationship]
   (do ;(assert (not (nil? node)))
       ;(assert (not (nil? succ)))
       (.link graph node succ relationship union-rels))))

(defn link-to-all-iter
  "Given a graph g, links x to all ys, using a loop w/iterator instead of
  reduce. Faster for some v hot reduce codepaths."
  [g x ys]
  (loopr [g' g]
         [y ys :via :iterator]
         (recur (link g' x y))))

(defn link-to-all
  "Given a graph g, links x to all ys."
  ([g x ys]
   (loopr [g' g]
          [y ys]
          (recur (link g' x y))))
  ([g x ys rel]
   (loopr [g' g]
          [y ys]
          (recur (link g' x y rel)))))

(defn link-all-to
  "Given a graph g, links all xs to y."
  ([g xs y]
   (loopr [g' g]
          [x xs]
          (recur (link g' x y))))
  ([g xs y relationship]
   (loopr [g' g]
          [x xs]
          (recur (link g' x y relationship)))))

(defn link-all-to-all
  "Given a graph g, links all xs to all ys."
  ([g xs ys]
   (loopr [g' g]
          [x xs, y ys]
          (recur (link g' x y))))
  ([g xs ys rel]
   (loopr [g' g]
          [x xs, y ys]
          (recur (link g' x y rel)))))

(defn unlink
  "Heper for unlinking Bifurcan graphs."
  [^IGraph g a b]
  (.unlink g a b))

(defn unlink-to-all
  "Given a graph g, removes the link from x to all ys."
  [g x ys]
  (if (seq ys)
    (recur (unlink g x (first ys)) x (next ys))
    g))

(defn unlink-all-to
  "Given a graph g, removes the link from all xs to y."
  [g xs y]
  (if (seq xs)
    (recur (unlink g (first xs) y) (next xs) y)
    g))

(defn project-rels
  "Takes a BitRels and a directed graph where edges are BitRels. Returns a
  directed graph with just those relationships in the given BitRels."
  [^BitRels target-rels ^DirectedGraph g]
  (loopr [^DirectedGraph g' (.linear (op-digraph))]
         [^IEdge edge (.edges g) :via :iterator]
         (recur
           (let [rel (.intersection target-rels ^BitRels (.value edge))]
             (if (.isEmpty rel)
               g' ; No rels here
               (.link g' (.from edge) (.to edge) rel))))
         (.forked g')))

(defn ^DirectedGraph remove-self-edges
  "There are times when it's just way simpler to use link-all-to-all between
  sets that might intersect, and instead of writing all-new versions of link-*
  that suppress self-edges, we'll just remove self-edges after."
  [^DirectedGraph g nodes-of-interest]
  (loop [g      (.linear g)
         nodes  nodes-of-interest]
    (if (seq nodes)
      (let [node (first nodes)]
        (recur (unlink g node node) (next nodes)))
      (.forked g))))

(defn bfs
  "Takes a function of a vertex yielding neighbors, and a collection of
  vertices, and yields a lazy sequence of vertices reachable from that initial
  collection."
  [neighbors vertices]
  (Graphs/bfsVertices ^Iterable vertices
                      (reify Function
                        (apply [_ node]
                          (if-let [ns (neighbors node)]
                            ns
                            [])))))

(defn downstream-matches
  "Returns the set of all nodes matching pred including or downstream of
  vertices. Takes a raw graph, and a memoized, which memoizes our previous
  findings. We use memo where possible, and fall back to raw graph searches
  otherwise."
  [pred g ^DirectedGraph memo vertices]
  (->> (reify Function
         (apply [_ node]
           (if (pred node)
             ; We're done!
             []
             (if (.contains (.vertices memo) node)
               ; Ah, good, we can jump right to memoized values
               (out memo node)

               ; Fall back to slow exploration via the raw graph
               (out g node)))))
       (Graphs/bfsVertices ^Iterable vertices)
       (filter pred)))

(defn ^DirectedGraph collapse-graph
  "Given a predicate function pred of a vertex, and a graph g, collapses g to
  just those vertices which satisfy (pred vertex), preserving transitive
  connections through removed vertices. If a -> b -> c, and we remove b, then a
  -> c.

  This method destroys relationship edges. I'm not sure what the semantics of
  preserving them might be, and we won't be using them for the application I'm
  thinking of anyway."
  [pred ^IGraph g]
  ;(info "collapsing graph of " (.size g) "nodes," (count (filter pred (.vertices g))) "of which match pred")
  ; We proceed through the graph linearly, taking every node n which matches
  ; pred. We explore its downstream neighborhood up to and including, but not
  ; past, nodes matching pred. We add an edge from n to each downstream node to
  ; our result graph.
  ;
  ; We're going to take advantage of the fact that our graphs are probably
  ; roughly temporally ordered transactions by :index, and proceed in *reverse*
  ; index order to maximize the chances of hitting memoization.
  (->> (.vertices g)
       (sort-by :index)
       reverse
       (reduce (fn reducer [[g' ^IGraph memo] v]
                 ;(prn :v v :memo-size (.size (.vertices memo)))
                 (let [downstream (downstream-matches pred g memo (out g v))]
                   (if (pred v)
                     ; Good, build associations in our result graph
                     [(link-to-all g' v downstream) memo]
                     ; Well, this *wasn't* a node we were looking for... but we
                     ; can memoize it to speed up future searches.
                     [g' (-> memo
                             (.add v) ; Memoize even negative result!
                             (link-to-all v downstream))])))
               [(.linear (digraph))
                (.linear (digraph))])
       first
       b/forked))

(defn map->bdigraph
  "Turns a sequence of [node, successors] pairs (e.g. a map) into a bifurcan
  directed graph"
  [m]
  (loopr [g (b/linear (bg/digraph))]
         [[node succs]  m
          succ          succs]
         (recur (bg/link g node succ))
         (b/forked g)))

(defn map->dag
  "Turns a sequence of [node, successors] pairs (e.g. a map) into a bifurcan
  directed acyclic graph."
  [m]
  (loopr [g (b/linear (bg/directed-acyclic-graph))]
         [[node succs]  m
          succ          succs]
         (recur (bg/link g node succ))
         (b/forked g)))

(defn ^DirectedGraph digraph-union
  "Takes the union of n graphs, merging BitRels edges with BitRels union."
  ([] (DirectedGraph.))
  ([a] a)
  ([^DirectedGraph a ^DirectedGraph b]
   (.merge a b union-rels))
  ([a b & more]
   (reduce digraph-union a (cons b more))))

(defn strongly-connected-components
  "Finds the strongly connected components of a graph, greater than 1 element."
  [g]
  (map ->clj (Graphs/stronglyConnectedComponents g false)))

(defn tarjan
  "Returns the strongly connected components of a graph specified by its
  nodes (ints) and a successor function (succs node) from node to nodes.
  A iterative verison of Tarjan's Strongly Connected Components."
  [graph]
  (strongly-connected-components (map->bdigraph graph)))

(defn map-vertices
  "Takes a function of vertices, and a graph, and returns graph with all
  vertices mapped via f. Edge values are merged with set union."
  [f g]
  (b/forked
    (reduce (fn [^DirectedGraph g ^IEdge edge]
              (.link g
                     (f (.from edge))
                     (f (.to edge))
                     (.value edge)
                     union-rels))
            (.linear (digraph))
            (bg/edges g))))

(defn ^IGraph sequential-composition
  "The sequential composition (ish; see below) of two graphs A; B. Returns a
  graph C such that iff x -> y in A, and y -> z in B, then x -> y -> z in C.
  This is similar to relational composition, treating each graph as a set of
  [in-vert out-vert] pairs.

  Note that unlike A; B, we actually preserve the intermediate vertex and
  original edges in this graph. This has two advantages: first, Bifurcan's SCC
  search can't distinguish between singleton SCCs with/ or without self edges;
  preserving the intermediate vertex means any SCC has at least 2 ops. Second,
  it means cycles detected here are isomorphic to the real cycles we're looking
  for."
  [a b]
  (let [b-vertices (bg/vertices b)]
    (loopr [c (b/linear (op-digraph))]
           [x->y (bg/edges a) :via :iterator]
           (recur
             (let [y (bg/edge-to x->y)]
               (if (bs/contains? b-vertices y)
                 (loopr [c c]
                        [z (bg/out b y) :via :iterator]
                        (-> c
                            (bg/add-edge x->y)
                            (bg/link y z (bg/edge b y z))
                            recur))
                 ; y not in b
                 c)))
           (b/forked c))))

(defn ^IGraph sequential-extension
  "Takes two graphs A and B. Returns A U (A; B): the union of A with the
  sequential composition of A and B. In other words, takes A and expands it
  with edges that represent a step through A, then a step through B.

  This operation is particularly helpful in finding nonadjacent cycles: it
  produces a graph where cycles are mostly in A, but can take non-adjacent
  jumps through B."
  [a b]
  (let [b-vertices (bg/vertices b)]
    (loopr [c (b/linear a)]
           ; Iterate over vertices in a with some inbound edge
           [y (r/filter (fn has-inbound? [y]
                          (< 0 (b/size (bg/in a y))))
                        (bg/vertices a))]
           (recur
             (if (bs/contains? b-vertices y)
               (loopr [c c]
                      [z (bg/out b y) :via :iterator]
                      (recur (bg/link c y z (bg/edge b y z))))
               ; y not in b
               c))
           (b/forked c))))

;; Very simple graph search. elle.txn doesn't use this. See elle.bfs for the
;; smarter version.

(defn prune-alternate-paths
  "If we have two paths [a b d] and [a c d], we don't need both of them,
  because both get us from a to d. We collapse a set of paths by filtering out
  duplicates. Since all paths *start* at the same place, we can do this
  efficiently by selecting one from the set of all paths that end in the same
  place."
  [paths]
  (->> paths
       (group-by peek)
       vals
       (map first)))

(defn grow-paths
  "Given a graph g, and a set of paths (each a sequence like [a b c]),
  constructs a new set of paths by taking the tip c of each path p, and
  expanding p to all vertices c can reach: [a b c] => #{[a b c d] [a b c e]}."
  [^IGraph g, paths]
  (->> paths
       (mapcat (fn [path]
                 (maybe-interrupt)
                 (let [tip (peek path)]
                   ; Expand the tip to all nodes it can reach
                   (map (partial conj path) (.out g tip)))))))

(defn path-shells
  "Given a graph, and a starting collection of paths, constructs shells
  outwards from those paths: collections of longer and longer paths."
  [^IGraph g starting-paths]
  ; The longest possible cycle is the entire graph, plus one.
  (take (inc (.size g))
        (iterate (comp prune-alternate-paths
                       (partial grow-paths g))
                 starting-paths)))

(defn loop?
  "Does the given vector of Ops begin and end with identical elements, and is
  it longer than 1?"
  [v]
  (and (< 1 (count v))
       (h/index= (first v) (peek v))))

(defn find-cycle
  "Given a strongly connected graph, finds a short cycle in it."
  [^IGraph g]
  (->> (.vertices g)
       (keep (fn [start]
               (->> (path-shells g [[start]])
                    (mapcat identity)
                    (filter loop?)
                    first)))
       first))

(defn fallback-cycle
  "A DFS algorithm which finds ANY cycle in a graph guaranteed to be strongly
  connected. We use this as a fallback when BFS is too slow."
  [^IGraph g]
  (let [start (first (bg/vertices g))]
    (loop [path [start]
           seen {start 0}]
      (let [vs        (->clj (out g (peek path)))
            ; TODO: this is wrong when nodes can be nil, but that shouldn't
            ; matter for us.
            loop-idx  (some seen vs)]
        (if loop-idx
          ; We can jump from this node to something in our own path
          (conj (subvec path loop-idx) (nth path loop-idx))
          ; Keep exploring
          (let [v (first (remove seen vs))]
            (recur (conj path v) (assoc seen v (count path)))))))))

(defn topo-depths
  "Takes a graph. Returns a map of vertices to topological depths. The top
  vertices in the graph--those with no inbound edges--have depth 0. Their
  immediate descendants have depth 1, their descendants have depth 2, and so
  on."
  ([g]
   (topo-depths (b/forked g) 0 (transient {})))
  ([g depth m]
   (let [top (b/forked (bg/top g))]
     (if (= 0 (b/size top))
       ; Done!
       (persistent! m)
       (recur (-> ^DirectedAcyclicGraph (reduce bg/remove g top)
                  ; Work around https://github.com/lacuna/bifurcan/issues/46 by
                  ; recreating the entire DAG.
                  .directedGraph
                  DirectedAcyclicGraph/from)
              (inc depth)
              (reduce #(assoc! %1 %2 depth) m top))))))
