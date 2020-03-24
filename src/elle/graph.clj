(ns elle.graph
  "Supporting functions for working efficiently with graphs. This is a
  lightweight layer around Bifurcan's graph datatypes and related structures.

  We perform as much of our heavy lifting as possible in Bifurcan structures,
  then coerce them back to Clojure data structures for analysis, serialization,
  pretty-printing, etc."
  (:require [clojure.tools.logging :refer [info error warn]]
            [clojure.core.reducers :as r]
            [clojure.set :as set]
            [elle.util :refer [map-vals]])
  (:import (io.lacuna.bifurcan DirectedGraph
                               Graphs
                               Graphs$Edge
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
                               Function)))

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
     :value (.value e)})

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

  Object
  (->clj [x] x)

  nil
  (->clj [x] x))

(defn digraph
  "Constructs a fresh directed graph."
  []
  (DirectedGraph.))

(defn linear
  "Bifurcan's analogue to (transient x)"
  [^ICollection x]
  (.linear x))

(defn forked
  "Bifurcan's analogue to (persistent! x)"
  [^ICollection x]
  (.forked x))

(defn size
  "How big is a thing?"
  [^ICollection c]
  (.size c))

(defn ^ISet vertices
  "The set of all vertices in the node."
  [^IGraph g]
  (.vertices g))

(defn contains-node?
  "Is this node in the graph?"
  [^IGraph g v]
  (.contains (vertices g) v))

(defn in
  "Inbound edges to v in graph g."
  [^IGraph g v]
  (try (.in g v)
       (catch IllegalArgumentException e)))

(defn out
  "Outbound edges from v in graph g."
  [^IGraph g v]
  (try (.out g v)
       (catch IllegalArgumentException e)))

(def ^BinaryOperator union-edge
  "A binary operator performing set union on the values of edges."
  (reify BinaryOperator
    (apply [_ a b]
      (set/union a b))))

(defn ^IEdge edge
  "Returns the edge between two vertices."
  [^IGraph g a b]
  (.edge g a b))

(defn edges
  "A lazy seq of all edges."
  [^IGraph g]
  ; We work around a bug in bifurcan which returns edges backwards!
  (map (fn [^IEdge e]
         (Graphs$Edge. (.value e) (.to e) (.from e)))
       (.edges g)))

(defn add
  "Add a node to a graph."
  [^DirectedGraph graph node]
  (.add graph node))

(defn set-add
  "Add an element to a set."
  [^ISet s x]
  (.add s x))

(defn link
  "Helper for linking Bifurcan graphs. Optionally takes a relationship, which
  is added to the value set of the edge. Nil relationships are treated as if no
  relationship were passed."
  ([^DirectedGraph graph node succ]
   ;(assert (not (nil? node)))
   ;(assert (not (nil? succ)))
   (.link graph node succ))
  ([^DirectedGraph graph node succ relationship]
   (do ;(assert (not (nil? node)))
       ;(assert (not (nil? succ)))
       (.link graph node succ #{relationship} union-edge))))

(defn link-to-all
  "Given a graph g, links x to all ys."
  ([g x ys]
   (if (seq ys)
     (recur (link g x (first ys)) x (next ys))
     g))
  ([g x ys rel]
   (if (seq ys)
     (recur (link g x (first ys) rel) x (next ys) rel)
     g)))

(defn link-all-to
  "Given a graph g, links all xs to y."
  ([g xs y]
   (if (seq xs)
     (recur (link (first xs) y) (next xs) y)
     g))
  ([g xs y relationship]
   (if (seq xs)
     (recur (link g (first xs) y relationship) (next xs) y relationship)
     g)))

(defn link-all-to-all
  "Given a graph g, links all xs to all ys."
  ([g xs ys]
   (if (seq xs)
     (recur (link-to-all g (first xs) ys) (next xs) ys)
     g))
  ([g xs ys rel]
   (if (seq xs)
     (recur (link-to-all g (first xs) ys rel) (next xs) ys rel)
     g)))

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


(defn keep-edge-values
  "Transforms a graph by applying a function (f edge-value) to each edge in the
  graph. Where the function returns `nil`, removes that edge altogether."
  [f ^DirectedGraph g]
  (forked
     (reduce (fn [^IGraph g, ^IEdge edge]
              (let [v' (f (.value edge))]
                (if (nil? v')
                  ; Remove edge
                  (.unlink g (.from edge) (.to edge))
                  ; Update existing edge
                  (.link g (.from edge) (.to edge) v'))))
            (linear g)
            ; Note that we iterate over an immutable copy of g, and mutate a
            ; linear version in-place, to avoid seeing our own mutations during
            ; iteration.
            (edges (forked g)))))

(defn remove-relationship
  "Filters a graph, removing the given relationship from it."
  [g rel]
  (keep-edge-values (fn [rs]
                      (let [rs' (disj rs rel)]
                        (when (seq rs')
                          rs')))
                    g))

(defn project-relationship
  "Filters a graph to just those edges with the given relationship."
  [g rel]
  ; Might as well re-use this, we're gonna build it a lot.
  (let [rs' #{rel}]
    (keep-edge-values (fn [rs] (when (contains? rs rel) rs'))
                      g)))

(defn filter-relationships
  "Filters a graph g to just those edges which intersect with the given set of
  relationships."
  [target-rels g]
  (keep-edge-values (fn [rs]
                      (let [rs' (set/intersection target-rels rs)]
                        (when-not (empty? rs')
                          rs')))
                    g))

(defn ^DirectedGraph remove-self-edges
  "There are times when it's just way simpler to use link-all-to-all between
  sets that might intersect, and instead of writing all-new versions of link-*
  that suppress self-edges, we'll just remove self-edges after."
  [^DirectedGraph g nodes-of-interest]
  (loop [g      (linear g)
         nodes  nodes-of-interest]
    (if (seq nodes)
      (let [node (first nodes)]
        (recur (unlink g node node) (next nodes)))
      (forked g))))

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
  [pred ^DirectedGraph g]
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
               [(linear (digraph))
                (linear (digraph))])
       first
       forked))

(defn map->bdigraph
  "Turns a sequence of [node, successors] pairs (e.g. a map) into a bifurcan
  directed graph"
  [m]
  (reduce (fn [^DirectedGraph g [node succs]]
            (reduce (fn [graph succ]
                      (link graph node succ))
                    g
                    succs))
          (.linear (DirectedGraph.))
          m))

(defn ^Set ->bset
  "Turns any collection into a Bifurcan Set."
  ([coll]
   (->bset coll (.linear (Set.))))
  ([coll ^Set s]
   (if (seq coll)
     (recur (next coll) (.add s (first coll)))
     s)))

(defn ^DirectedGraph digraph-union
  "Takes the union of n graphs, merging edges with union."
  ([] (DirectedGraph.))
  ([a] a)
  ([^DirectedGraph a ^DirectedGraph b]
   (.merge a b union-edge))
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
  (forked
    (reduce (fn [^DirectedGraph g ^IEdge edge]
              (.link g
                     (f (.from edge))
                     (f (.to edge))
                     (.value edge)
                     union-edge))
            (linear (digraph))
            (edges g))))

(defn renumber-graph
  "Takes a Graph and rewrites each vertex to a unique integer, returning the
  rewritten Graph, and a vector of the original vertexes for reconstruction."
  [g]
  (let [mapping (persistent!
                  (reduce (fn [mapping v]
                            (assoc! mapping v (count mapping)))
                          (transient {})
                          (vertices g)))
        g' (reduce (fn [g' v]
                     ; Find the index of this vertex
                     (let [vi (get mapping v)]
                       (reduce (fn [g' n]
                                 ; And the index of this neighbor
                                 (let [ni (get mapping n)]
                                   (link g' vi ni)))
                               g'
                               (out g v))))
                (linear (digraph))
                (vertices g))]
    [(forked g')
     (persistent!
       (reduce (fn [vertices [vertex index]]
                 (assoc! vertices index vertex))
               (transient (vec (repeat (count mapping) nil)))
               mapping))]))

; Advanced graph search
;
; Given a graph and a strongly connected component in it, we're interested in
; finding cycles in that graph which satisfy certain properties. For instance,
; we might want to restrict ourselves to only ww or wr edges (for G1c), or
; find a cycle in which every rw edge is *not* adjacent to another rw edge.
; (for G2-nonadjacent). Enumeration of all paths and filtering them for these
; criteria after the fact may be hugely expensive. Instead, we push the
; filtering process into the enumeration process, making sure that we only
; explore paths which would satisfy the target cycle requirements.
;
; To do this, we define a PathState as a sequence of adjacent vertices in the
; graph, *plus* an arbitrary state. As a part of our search, we take a state
; machine transition function (f state path edge-value vertex), which evaluates
; whether we can append that vertex to the given path. A search for G-single
; could say, for instance "this state tells me we already saw a rw edge, so we
; can't add another to this particular path.
;
; f returns a new state if it is possible to extend the path to that vertex, or
; ::invalid if it is not possible.

(defrecord PathState [path state])

(defn prune-alternate-path-states
  "If we have two paths [a b e] and [a c d e], and they have the same state, we
  don't need to retain both of them during the search. We take a set of paths,
  and collapse it to just those which have distinct start and endpoints, and
  distinct states. Since all paths in our search *start* from the same place,
  we can do this efficiently by just selecting one from the set of all paths
  that end in the same place with the same state."
  [path-states]
  (->> path-states
       (group-by (fn [ps] [(peek (:path ps)) (:state ps)]))
       vals
       (map first)))

;; Graph search helpers

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

(defn prune-longer-paths
  "We can also completely remove paths whose tips are in a prefix of any other
  path, because these paths are simply longer versions of paths we've already
  explored."
  [paths]
  (let [old (->> paths
                 (mapcat butlast)
                 (into #{}))]
    (remove (comp old peek) paths)))

(defn grow-path-states
  "Given a transition function f, graph g, and a set of PathStates, constructs
  a new set of Pathstates by taking the tip t of each PathState p and extending
  it to all vertices t can reach, such that (f state path edge next-vertex)
  returns anything but ::invalid."
  [f g path-states]
  (mapcat (fn grow-path-state [ps]
            (let [path    (:path ps)
                  tip     (peek path)
                  state   (:state ps)]
              (keep (fn to [tip']
                      (let [edge   (edge g tip tip')
                            state' (f state path edge tip')]
                        (when-not (= ::invalid state')
                          (PathState. (conj path tip') state'))))
                    (out g tip))))
          path-states))

(defn grow-paths
  "Given a graph g, and a set of paths (each a sequence like [a b c]),
  constructs a new set of paths by taking the tip c of each path p, and
  expanding p to all vertices c can reach: [a b c] => #{[a b c d] [a b c e]}."
  [^DirectedGraph g, paths]
  (->> paths
       (mapcat (fn [path]
                 (let [tip (peek path)]
                   ; Expand the tip to all nodes it can reach
                   (map (partial conj path) (.out g tip)))))))

(defn path-state-shells
  "Given a graph, and a starting collection of path states, constructs shells
  outwards from those paths: collections of longer and longer path states."
  [f g starting-path-states]
  ; The longest possible cycle is the entire graph, plus one.
  (take (inc (size g))
        (iterate (comp prune-alternate-path-states
                       (partial grow-path-states f g))
                 starting-path-states)))

(defn path-shells
  "Given a graph, and a starting collection of paths, constructs shells
  outwards from those paths: collections of longer and longer paths."
  [^DirectedGraph g starting-paths]
  ; The longest possible cycle is the entire graph, plus one.
  (take (inc (.size g))
        (iterate (comp prune-alternate-paths
                       (partial grow-paths g)
                       prune-longer-paths)
                 starting-paths)))

(defn loop?
  "Does the given vector begin and end with identical elements, and is longer
  than 1?"
  [v]
  (and (< 1 (count v))
       (= (first v) (peek v))))

(defn path-state-loop?
  "Is the given PathState a loop?"
  [path-state]
  (loop? (:path path-state)))

(defn find-cycle-starting-with
  "Some anomalies consist of a cycle with exactly, or at least, one edge of a
  particular type. This fuction works like find-cycle, but allows you to pass
  *two* graphs: an initial graph, which is used for the first step, and a
  remaining graph, which is used for later steps."
  [^IGraph initial-graph ^IGraph remaining-graph scc]
  (let [scc   (->bset scc)
        ig    (.select initial-graph scc)
        rg    (.select remaining-graph scc)
        ; Think about the structure of these two graphs
        ;
        ;  I        R
        ; ┌── d ┆
        ; ↓   ↑ ┆
        ; a ──┤ ┆
        ;     ↓ ┆
        ; b → c ┆ c → a
        ;
        ; In this graph, a cycle starting with I and completing with R can't
        ; include d, since there is no way for d to continue in R--it's not
        ; present in that set. Note that this is true even though [a d a] is a
        ; cycle--it's just a cycle purely in I, rather than a cycle starting in
        ; I and continuing in R, which is what we're looking for.
        ;
        ; Similarly, b can't be in a cycle, because there's no way to *return*
        ; to b from R, and we know that the final step in our cycle must be a
        ; transition from R -> I.
        ;
        ; In general, a cycle which has one edge from I must cross the boundary
        ; from I to R, and from R back to I again--otherwise it would not be a
        ; cycle. We therefore know that the first two vertices must be elements
        ; of both I *and* R. To encode this, we restrict I to only vertices
        ; present in R.
        ig (.select initial-graph (.vertices rg))]
    ; Start with a vertex in the initial graph
    (->> (.vertices ig)
         (keep (fn [start]
                 ; Expand this vertex out one step using the initial graph
                 (->> (grow-paths ig [[start]])
                      ; Then expand those paths into surrounding shells
                      (path-shells rg)
                      ; Flatten those into a list of paths
                      (mapcat identity)
                      (filter loop?)
                      first)))
         first)))

(defn find-cycle-with-
  "Searches for a cycle in a graph, given a set of strongly connected vertices
  `scc`, along which path a state machine holds. The state machine is given as
  a transition function f.

  (f vertex) gives the initial state for a path which consists of just
  [vertex].

  (transition state path relationship vertex) yields the state when we append
  vertex to path; relationship is the value of the edge which we take to get to
  vertex.

  The special state ::invalid indicates that the given path should not be
  followed.

  Any cycle found must pass (pred path-state). This is helpful for enforcing
  criteria that can't be rejected incrementally by `transition`--for instance,
  that a cycle must contain at least two edges of a certain type.

  Returns the resulting PathState."
  [transition pred ^IGraph graph scc]
  ; First, restrict the graph to the SCC.
  (let [g     (.select graph (->bset scc))
        cycle (->> (vertices g)
                   (keep (fn [start]
                           (let [state (transition start)
                                 init-path-state (PathState. [start] state)]
                             (when (not= ::invalid? init-path-state)
                               (->> (path-state-shells transition g
                                                       [init-path-state])
                                    (mapcat identity)
                                    (filter path-state-loop?)
                                    (filter pred)
                                    first)))))
                   first)]
    cycle))

(defn find-cycle-with
  "Like find-cycle-with-, but just returns the cycle, not the full PathState."
  [transition pred g scc]
  (:path (find-cycle-with- transition pred g scc)))

(defn find-cycle
  "Given a graph and a strongly connected component within it, finds a short
  cycle in that component."
  [^IGraph graph scc]
  (let [g             (.select graph (->bset scc))
        ; Just to speed up equality checks here, we'll construct an isomorphic
        ; graph with integers standing for our ops, find a cycle in THAT, then
        ; map back to our own space.
        [gn mapping]  (renumber-graph g)]
    (->> (vertices gn)
         (keep (fn [start]
                 (when-let [cycle (->> (path-shells gn [[start]])
                                       (mapcat identity)
                                       (filter loop?)
                                       first)]
                     (mapv mapping cycle))))
         first)))
