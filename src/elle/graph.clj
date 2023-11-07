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
            [jepsen.history :as h])
  (:import (elle NamedGraph
                 RelGraph)
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

(defn ^DirectedGraph digraph
  "Constructs a fresh directed graph."
  []
  (DirectedGraph.))

(defn ^NamedGraph named-graph
  "Constructs a fresh named directed graph with the given name."
  ([name]
   (NamedGraph. name (digraph)))
  ([name graph]
   (NamedGraph. name graph)))

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

(defn ^Set out
  "Outbound edges from v in graph g."
  [^IGraph g v]
  (try (.out g v)
       (catch IllegalArgumentException e)))

(def ^BinaryOperator merge-last-write-wins
  "A binary operator that takes a, b -> b"
  (reify BinaryOperator
    (apply [_ a b] b)))

(def ^BinaryOperator union-edge
  "A binary operator performing bifurcan set union on the values of edges."
  (reify BinaryOperator
    (apply [_ a b]
      (cond (nil? a) b
            (nil? b) a
            true    (.union ^ISet a ^ISet b)))))

(defn ^IEdge edge
  "Returns the edge between two vertices."
  [^IGraph g a b]
  (.edge g a b))

(defn edges
  "A lazy seq of all edges."
  [^IGraph g]
  (.edges g))

(defn add
  "Add a node to a graph."
  [^DirectedGraph graph node]
  (.add graph node))

(defn ^Set bset
  "Constructs a new Bifurcan Set, either empty or containing the given object."
  ([]
   Set/EMPTY)
  ([x]
   (.. Set/EMPTY linear (add x) forked)))

(defn ^Set ->bset
  "Turns any reducible into a Bifurcan Set."
  [xs]
  (loopr [^ISet s (.linear Set/EMPTY)]
         [x xs]
         (recur (.add s x))
         (.forked s)))

(defn set-add
  "Add an element to a set."
  [^ISet s x]
  (.add s x))

(defn link
  "Helper for linking Bifurcan graphs. Optionally takes a relationship, which
  is added to the value set of the edge. Nil relationships are treated as if no
  relationship were passed."
  ([^IGraph graph node succ]
   ;(assert (not (nil? node)))
   ;(assert (not (nil? succ)))
   (.link graph node succ))
  ([^IGraph graph node succ relationship]
   (do ;(assert (not (nil? node)))
       ;(assert (not (nil? succ)))
       (.link graph node succ (bset relationship) union-edge))))

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

(defn project-relationships
  "Projects a RelGraph to just the given set of relationships."
  [target-rels ^RelGraph g]
  (if (= 1 (count target-rels))
    (.projectRel  ^RelGraph g (first target-rels))
    (.projectRels ^RelGraph g target-rels)))

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
               [(linear (digraph))
                (linear (digraph))])
       first
       forked))

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

(defn ^NamedGraph named-graph-union
  "Unions two named graphs together."
  [^NamedGraph a, ^NamedGraph b]
  (.union a b))

(defn ^RelGraph rel-graph-union
  "Unions something into a RelGraph. Can take either a NamedGraph or another
  RelGraph. With no args, returns an empty RelGraph."
  ([] RelGraph/EMPTY)
  ([a]
   (condp instance? a
     NamedGraph (.union RelGraph/EMPTY ^NamedGraph a)
     RelGraph   (.union RelGraph/EMPTY ^RelGraph a)
     (throw (IllegalArgumentException.
              (str "Don't know how to union a relgraph with " (type a))))))
  ([^RelGraph a b]
   (condp instance? b
     NamedGraph (.union a ^NamedGraph b)
     RelGraph   (.union a ^RelGraph b)
     (throw (IllegalArgumentException.
              (str "Don't know how to union a relgraph with " (type b)))))))

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
                          (vertices g)))]
    [(map-vertices mapping g)
     (persistent!
       (reduce (fn [vertices [vertex index]]
                 (assoc! vertices index vertex))
               (transient (vec (repeat (count mapping) nil)))
               mapping))]))

(defn out+
  "Like graph/out, but returns nil when the vertex does not exist, rather than
  throwing."
  [graph vertex]
  ; TODO: if this is slow, consider trying bg/out directly and catching the
  ; not-found case. My *guess* is that the double lookup is going to be
  ; relatively fast and stay in cache, but the exception handler might be
  ; cheaper.
  (when (bs/contains? (bg/vertices graph) vertex)
    (bg/out graph vertex)))

(defn ^IGraph sequential-composition
  "The sequential composition of two graphs A; B. Returns a graph C such
  that iff x -> y in A, and y -> z in B, then x -> z in C. This is equivalent
  to relational composition, treating each graph as a set of [in-vert out-vert]
  pairs.

  For now, we simply destroy edge values; it's not clear what the right
  representation is."
  [a b]
  (loopr [c (b/linear (bg/digraph))]
         [x->y (bg/edges a)
          z    (out+ b (bg/edge-to x->y))]
         (recur (bg/link c (bg/edge-from x->y) z))
         (b/forked c)))

(defn ^IGraph sequential-expansion
  "Takes two RelGraphs A and B. Returns A U (A; B): the union of A with the
  sequential composition of A and B. In other words, takes A and expands it
  with edges that represent a step through A, then a step through B.

  This operation is particularly helpful in finding nonadjacent cycles: it
  produces a graph where cycles are mostly in A, but can take non-adjacent
  jumps through B."
  [^RelGraph a, ^RelGraph b]
  ; Rather than add to a piecemeal, we union it with a new NamedGraph--that's
  ; constant time.
  (.union a (NamedGraph. ::seq-comp (sequential-composition a b))))

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
; graph, a sequence of the edges between those vertices, and an arbitrary
; state. As a part of our search, we take a state machine transition function
; (f state path edge-value vertex), which evaluates whether we can append that
; vertex to the given path. A search for G-single could say, for instance "this
; state tells me we already saw a rw edge, so we can't add another to this
; particular path.
;
; f returns a new state if it is possible to extend the path to that vertex, or
; ::invalid if it is not possible.

(defrecord PathState [path edges state])

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

(defn grow-path-states
  "Given a transition function f, graph g, and a set of PathStates, constructs
  a new set of Pathstates by taking the tip t of each PathState p and extending
  it to all vertices t can reach, such that (f state path edge next-vertex)
  returns anything but ::invalid."
  [f g path-states]
  (mapcat (fn grow-path-state [^PathState ps]
            (maybe-interrupt)
            (let [path    (:path ps)
                  tip     (peek path)
                  state   (:state ps)]
              (keep (fn to [tip']
                      (let [edge   (edge g tip tip')
                            state' (f state path edge tip')]
                        (when-not (= ::invalid state')
                          (PathState. (conj path tip')
                                      (conj (.edges ps) edge)
                                      state'))))
                    (out g tip))))
          path-states))

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
  [^IGraph g starting-paths]
  ; The longest possible cycle is the entire graph, plus one.
  (take (inc (.size g))
        (iterate (comp prune-alternate-paths
                       (partial grow-paths g))
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
  [^IGraph initial-graph ^IGraph remaining-graph]
  (let [; Think about the structure of these two graphs
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
        ig  (.select initial-graph (.vertices remaining-graph))]
    ;(info :start-search)
    ; Start with a vertex in the initial graph
    (->> (.vertices ig)
         (keep (fn [start]
                 ;(info :vertex start)
                 ; Expand this vertex out one step using the initial graph
                 (->> (grow-paths ig [[start]])
                      ; Then expand those paths into surrounding shells
                      (path-shells remaining-graph)
                      ; Flatten those into a list of paths
                      (mapcat identity)
                      (filter loop?)
                      first)))
         first)))

(defn map-path-state
  "We try to do as much of our search as possible over Longs, rather than ops,
  which are expensive to compare. Given a function mapping integers to ops, and
  a PathState, we remap the path in the PathState from integers back to ops."
  [mapping ^PathState path-state]
  (PathState. (mapv mapping (.path path-state))
              (.edges path-state)
              (.state path-state)))

(defn unchunk
  "Unchunks a possible chunked collection. We do this to avoid finding more
  solutions than necessary during graph search."
  [coll]
  (lazy-seq
    (when-let [[x] (seq coll)]
      (cons x (unchunk (rest coll))))))

(defn find-cycle-with-
  "Searches for a cycle in a graph, along which path a state machine holds. The
  state machine is given as a transition function f.

  (transition vertex) gives the initial state for a path which consists of just
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
  [transition pred ^IGraph g]
  ; First, restrict the graph to the SCC.
  (let [; Renumber the graph to speed up equality comparison
        ; TODO: this means we pass weird numeric vertices to transition, which
        ; is OK right now because our transition fns don't CARE about vertices,
        ; but... later we should maybe ensure the history is indexed and use
        ; that for equality comparison instead? Something else fast?
        [gn mapping] (renumber-graph g)
        cycle (->> (vertices gn)
                   (keep (fn [start]
                           (let [state (transition start)
                                 init-path-state (PathState. [start] [] state)]
                             (when (not= ::invalid? init-path-state)
                               (->> (path-state-shells transition gn
                                                       [init-path-state])
                                    (mapcat identity)
                                    unchunk
                                    (filter path-state-loop?)
                                    (map (partial map-path-state mapping))
                                    (filter pred)
                                    first)))))
                   first)]
    cycle))

(defn find-cycle-with
  "Like find-cycle-with-, but just returns the cycle, not the full PathState."
  [transition pred g]
  (:path (find-cycle-with- transition pred g)))

(defn find-cycle
  "Given a strongly connected graph, finds a short cycle in it."
  [^IGraph g]
  (let [; Just to speed up equality checks here, we'll construct an isomorphic
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
