(ns elle.bfs
  "Provides fast, specialized breadth-first search for cycles in graphs of
  operations. It's been several years: we know exactly what kinds of cycles
  we're looking for, and we can write their state machines in code instead of
  as general predicates."
  (:require [bifurcan-clj [core :as b]
                          [graph :as bg]
                          [map :as bm]
                          [list :as bl]
                          [set :as bs]]
            [clojure [datafy :refer [datafy]]
                     [pprint :refer [pprint]]]
            [clojure.core [protocols :as p]]
            [clojure.tools.logging :refer [info warn]]
            [dom-top.core :refer [loopr]]
            [elle [graph :as g]
                  [util :refer [maybe-interrupt]]]
            [potemkin :refer [definterface+]])
  (:import (jepsen.history Op)))


(def rel-count
  "How many rels are there?"
  5)

(defn rel->bitmask
  "Takes a single rel keyword and returns its bitmask."
  ^long [rel]
  (case rel
    :ww       2r00001
    :wr       2r00010
    :rw       2r00100
    :process  2r01000
    :realtime 2r10000
    (throw (IllegalArgumentException.
             (str "Unknown rel type: " (pr-str rel))))))

(defn edge->bitmask
  "Takes a collection of rels and returns a bitmask."
  ^long [edge]
  (loopr [b (byte 0)]
         [rel edge]
         (recur (bit-or b (rel->bitmask rel)))))

(defn bitmask->edge
  "Takes a bitmask and returns a clojure Set of rels for use as an edge."
  [^long bitmask]
  (persistent!
    (cond-> (transient #{})
      (bit-test bitmask 0) (conj! :ww)
      (bit-test bitmask 1) (conj! :wr)
      (bit-test bitmask 2) (conj! :rw)
      (bit-test bitmask 3) (conj! :process)
      (bit-test bitmask 4) (conj! :realtime))))

(def rw
  "The RW bitmask"
  2r00100)

(defn rw?
  "Does this bitmask contain an RW?"
  [^long bitmask]
  (bit-test bitmask 2))

(defn array-contains?
  "A quick scan of a small array to see if it contains the given long."
  [^longs xs ^long target]
  (loopr []
         [x xs :via :array]
         (if (= x target)
           true
           (recur))
         false))

; A path is complete when it is valid, forms a loop, and has no tail. Then we
; ask for the operations along the path.
(definterface+ IPath
  (valid? [path] "Does the path's validity rules hold?")
  (loop?  [path] "Does this path connect to itself at any point?")
  (tail?  [path] "Is it exactly a loop, or does it have a dangling tail?")
  (ops    [path] "A Clojure vector of operations along the path.")
  (start  [path ^Op op]
          "Starts a path with an initial operation.")
  (step-rel [path ^long rel ^Op op]
            "Advances the given path along a specific bitset rel to op. Returns
            a Path if possible, nil otherwise.")
  (step   [path edge vertex]
        "Advances the given path along edge to vertex. Returns a Bifurcan List
        of possible Paths. This list is empty if no paths are legal.")

  (internal-degen-key ^long [path]
    "An internal value used for degeneracy optimization. This value packs
    want, want-rw, and rw-mode into a single long. Collisions in this value can
    be dropped when stepping."))

(deftype Path
  [^byte    legal      ; Bitmask of edges we can normally take
   ^byte    want       ; Bitmask of edges we're still waiting to take
   ^byte    want-rw    ; Number of RW edges we're waiting for. 0, 1, or 2.
   ; A state machine for RW edges. This can be:
   ;   nil                No special behavior; take RWs if legal
   ;   :single            Waiting for a single RW. Becomes nil if taken.
   ;   :nonadjacent-free  An RW may be taken, at which point the state flips to
   ;   :nonadjacent-taken An RW can not be taken. State then flips back to free
   rw-mode
   ^long last-index   ; The last index we visited
   index-set          ; A Bifurcan set of indices we visited *except* last-index
   ops                ; A Bifurcan list of operations we visited, in order
   ]

  IPath
  (valid? [this]
    ; A path is valid when the wanted edge bitset is 0, we want no more rws,
    ; and our nonadjacent mode is not nonadjacent-taken (since we always start
    ; with an rw edge for nonadjacent paths)
    (and (= 0 want)
         (= 0 want-rw)
         (not (identical? rw-mode :nonadjacent-taken))))

  (loop? [this]
    ; A path forms a loop when its last index has been visited before.
    (bs/contains? index-set last-index))

  (tail? [this]
    ; A path has a tail if the index of the first operation is different than
    ; the last index.
    (not= last-index (.index ^Op (b/nth ops 0))))

  (ops [this]
    ops)

  (internal-degen-key [this]
    (bit-or (case rw-mode
              nil                0
              :single            1
              :nonadjacent-free  2
              :nonadjacent-taken 3)
            (bit-shift-left want 8)
            (bit-shift-left want-rw 16)))

  (start [this op]
    (Path. legal
           want
           want-rw
           rw-mode
           (.index op)
           index-set
           (bl/add-last ops op)))

  (step-rel [this rel op]
    (let [rw? (rw? rel)]
      (cond ; If the edge is legal, we can simply take it.
            (< 0 (bit-and legal rel))
            (Path. legal                  ; Always unchanged
                   (bit-and-not want rel) ; We took this rel
                   (if rw?
                     (if (= 0 want-rw) 0 (- want-rw 1)) ; Took one rw
                     want-rw)
                   (case rw-mode
                     nil                nil
                     ; The only case where RWs are legal is if rw-mode is nil.
                     ; Any of these implies we did *not* take an RW edge.
                     :single            :single
                     :nonadjacent-free  :nonadjacent-free
                     :nonadjacent-taken :nonadjacent-free)
                   (.index op)                   ; New last index
                   (bs/add index-set last-index) ; Old last index falls into set
                   (bl/add-last ops op))         ; Remember op!

            ; OK, the rel wasn't normally legal, but we might have a special RW
            ; mode...
            rw?
            (case rw-mode
              ; No more RWs possible
              nil nil
              ; We can do exactly one rw
              :single (Path. legal
                             (bit-and-not want rel)
                             0   ; No more RWs possible
                             nil ; We took our only RW
                             (.index op)
                             (bs/add index-set last-index)
                             (bl/add-last ops op))
              :nonadjacent-free (Path. legal
                                       (bit-and-not want rel)
                                       ; We took an RW
                                       (if (= 0 want-rw) 0 (- want-rw 1))
                                       :nonadjacent-taken
                                       (.index op)
                                       (bs/add index-set last-index)
                                       (bl/add-last ops op))
              ; Can't take two nonadjacents in a row
              :nonadjacent-taken nil)

            ; Not legal or RW
            true
            nil)))

  (step [this edge op]
    (let [; These are the rels we might be interested in taking
          mask (cond rw-mode        (bit-or rw legal)
                     (< 0 want-rw)  (bit-or rw legal)
                     true           legal)
          ; As a performance optimization, we try to choose our first step to
          ; fulfill a required rel.
          mask (if (= 1 (b/size ops))
                 ; If we need an RW, it must be the first step.
                 (cond (pos? want-rw) (bit-and mask rw)

                       ; Other required edges
                       (pos? want) (bit-and mask want)

                       true mask)
                 ; Subsequent steps
                 mask)
          ; Which of our requirements work here?
          ;_ (prn :edge (into #{} edge) :mask (bitmask->edge mask))
          rels (bit-and mask (edge->bitmask edge))
          ; Mutable array of degenerate keys
          degen (long-array rel-count -1)]
      ; Iterate through path masks
      (loop [i     0
             paths (b/linear bl/empty)]
        (if (= i rel-count)
          ; Done
          paths
          (let [rel (bit-shift-left 1 i)]
            (if (= 0 (bit-and rel rels))
              ; Rel not present
              (recur (inc i) paths)
              ; Rel present; step forward
              (if-let [path' (step-rel this rel op)]
                ; Check if this rel is degenerate with another rel we took
                (let [dk (internal-degen-key path')]
                  (if (array-contains? degen dk)
                    ; We already constructed an equivalent path
                    (recur (inc i) paths)
                    ; This is novel
                    (do (aset-long degen i dk)
                        (recur (inc i) (bl/add-last paths path')))))
                ; No path possible
                (recur (inc i) paths))))))))

  Object
  (toString [this]
    (str "(Path"
         " :legal " (pr-str (bitmask->edge legal))
         " :want " (pr-str (bitmask->edge want))
         " :want-rw " want-rw
         " :rw-mode " (pr-str rw-mode)
         " :ops " (mapv :index ops)
         ")")))

(defn spec->path
  "Constructs an empty path from a cycle-anomaly spec."
  [{:keys [rels required-rels nonadjacent-rels single-rels multiple-rels
           realtime? process?]
    :as spec}]
  ;(info :rels rels :required-rels required-rels)
  (Path. ; Normally allowed rels
         (edge->bitmask rels)
         ; Required. Note that our :required spec breaks these out right now,
         ; for implementation reasons. When we drop the old implementation we
         ; can simplify.
         (edge->bitmask (cond-> (or required-rels #{})
                          process?  (conj :process)
                          realtime? (conj :realtime)))
         ; RW wanted count
         (cond single-rels
               (do (assert (= #{:rw} single-rels)) 1)

               multiple-rels
               (do (assert (= #{:rw} multiple-rels)) 2)

               true 0)

         ; RW mode
         (condp = nonadjacent-rels
           nil    (when (= single-rels #{:rw})
                    :single)
           #{:rw} :nonadjacent-free
           (throw (IllegalArgumentException. (str "Unexpected nonadjacent rels: "
                                                  (pr-str nonadjacent-rels)))))

         -1         ; First index
         bs/empty   ; Visited index set
         bl/empty)) ; Ops

(defn expand-paths
  "Takes a graph and a list of paths. Expands each path out by one hop,
  returning a new linear list of paths."
  [g paths]
  (loopr [paths' (b/linear bl/empty)]
         [path paths :via :iterator]
         ; For each path...
         (let [op (bl/last (ops path))]
           (recur (loopr [paths' paths']
                         [op'  (bg/out g op) :via :iterator]
                         ; And each op reachable from the tip of that path...
                         (let [edge (bg/edge g op op')
                               ;_ (prn :path   (str path)
                               ;       :op'    (:index op')
                               ;       :edge   (into #{} edge))
                               paths'' (step path edge op')]
                           ;(prn :paths'' (datafy paths''))
                           (recur (bl/concat paths' paths''))))))))

(defn search-from-op
  "Searches a graph for a cycle matching the given initial path, starting with
  `op`."
  [g init-path op]
  ; Expand in incremental shells from the starting vertex.
  (loop [paths (bl/add-last bl/empty (start init-path op))]
    (maybe-interrupt)
    (when (< 0 (b/size paths))
      ; (prn :paths (datafy paths))
      ; First, do we have any paths which are loops? Try to find one which is
      ; valid without a tail. If we have one, we're done. If not, we discard
      ; those loops.
      (loopr [paths' (b/linear bl/empty)]
             [path paths :via :iterator]
             (if (loop? path)
               (if (valid? path)
                 (if (not (tail? path))
                   ; Done!
                   (do ; (prn :found (datafy path))
                       (into [] (ops path)))
                   ; Later we should try and prune the tail
                   (do ; (prn :loop-has-tail (datafy path))
                       (recur paths')))
                 ; A loop, but not valid: drop this
                 (do ; (prn :loop-not-valid (datafy path))
                     (recur paths')))
               ; Not a loop; keep going
               (recur (bl/add-last paths' path)))
             ; We now have a set of non-loop paths to expand
             (do ; (prn :remaining-paths (datafy paths'))
                 (recur (expand-paths g paths')))))))

(defn search
  "Searches a graph for a cycle matching `spec`. Returns a cycle, or nil."
  [g spec]
  (let [init-path (spec->path spec)]
    ; (prn :init-path init-path)
    (loopr []
           [op (bg/vertices g) :via :iterator]
           (do ; (prn)
               ; (prn "Starting with" (:index op))
               (or (search-from-op g init-path op)
                   (recur))))))
