(ns elle.bfs
  "Provides fast, specialized breadth-first search for cycles in graphs of
  operations. It's been several years: we know exactly what kinds of cycles
  we're looking for, and we can write their state machines in code instead of
  as general predicates."
  (:require [bifurcan-clj [core :as b]
                          [graph :as bg]
                          [map :as bm]
                          [list :as bl]
                          [linear-list :as bll]
                          [set :as bs]]
            [clojure [datafy :refer [datafy]]
                     [pprint :refer [pprint]]]
            [clojure.core [protocols :as p]]
            [clojure.tools.logging :refer [info warn]]
            [dom-top.core :refer [loopr]]
            [elle [graph :as g]
                  [util :refer [maybe-interrupt]]]
            [potemkin :refer [definterface+]])
  (:import (elle BFSPath
                 BFSPath$RWMode
                 BitRels)
           (jepsen.history Op)))

(defn tail?
  "A path has a tail if the index of the first op is different than the last."
  [^BFSPath path]
  (not= (.lastIndex path) (.index ^Op (b/nth (.ops path) 0))))

(defn ^BFSPath spec->path
  "Constructs an empty path from a cycle-anomaly spec."
  [{:keys [^BitRels rels
           ^BitRels required-rels
           ^BitRels nonadjacent-rels
           ^BitRels single-rels
           ^BitRels multiple-rels
           realtime?
           process?]
    :as spec}]
  ;(info :rels rels :required-rels required-rels)
  (BFSPath. ; Legal, normally allowed rels
            (.rels rels)
            ; Required rels. Note that our :required spec breaks these out
            ; right now, for implementation reasons. When we drop the old
            ; implementation we can simplify.
            (.rels ^BitRels
                   (cond-> (or required-rels BitRels/NONE)
                     process?  (.union BitRels/PROCESS)
                     realtime? (.union BitRels/REALTIME)))
            ; RW wanted count
            (cond single-rels
                  (do (assert (= BitRels/RW single-rels)) 1)

                  multiple-rels
                  (do (assert (= BitRels/RW multiple-rels)) 2)

                  true 0)

            ; RW mode
            (condp = nonadjacent-rels
              nil    (if (and single-rels (.isAnyRW single-rels))
                        BFSPath$RWMode/SINGLE
                        BFSPath$RWMode/NONE)
              BitRels/RW BFSPath$RWMode/NONADJACENT_FREE
              (throw (IllegalArgumentException. (str "Unexpected nonadjacent rels: "
                                                     nonadjacent-rels))))))

(defn expand-paths
  "Takes a graph and a list of paths. Expands each path out by one hop,
  returning a new linear list of paths."
  [g paths]
  (loopr [paths' (bll/linear-list)]
         [^BFSPath path paths :via :iterator]
         ; For each path...
         (let [op (bl/last (.ops path))]
           (recur (loopr [paths' paths']
                         [^Op op'  (bg/out g op) :via :iterator]
                         ; And each op reachable from the tip of that path...
                         (let [edge (bg/edge g op op')
                               ;_ (prn :path   (str path)
                               ;       :op'    (:index op')
                               ;       :edge   (into #{} edge))
                               paths'' (.step path edge (.index op') op')
                               ; Faster concat
                               paths'''  (reduce bl/add-last paths' paths'')]
                           ;(prn :paths''' (datafy paths'''))
                           (recur paths''')))))))

(declare search-from-op)

(defn trim-loop
  "Takes a graph, a loop path with a tail, and tries to cut the tail
  off. Returns either a tail-less loop, or nil."
  [g init-path ^BFSPath path]
  (let [; We just hit a loop. Find the loop, restrict the graph to just those
        ; vertices, and search it for a cycle. We know the last op visited must
        ; be the pin where we link the loop shut.
        ops (.ops path)
        pin (.index ^Op (bl/last ops))
        ; So where does our path begin?
        pin-index (loopr [i 0]
                         [^Op op ops :via :iterator]
                         (if (= pin (.index op))
                           i
                           (recur (inc i))))
        ; Which means our candidate path is
        trimmed (bl/slice ops pin-index (b/size ops))
        n (b/size trimmed)
        ; Restrict graph to just those elements
        g' (bg/select g (bs/from trimmed))]
    ; Now search that graph.
    (loopr []
           [op trimmed :via :iterator]
           (or (search-from-op g' init-path op)
               (recur)))))

(defn search-from-op
  "Searches a graph for a cycle matching the given initial path, starting with
  `op`."
  [g ^BFSPath init-path ^Op op]
  ; Expand in incremental shells from the starting vertex.
  (loop [paths (bl/add-last bl/empty (.start init-path (.index op) op))]
    ;(prn :search-from-op :paths paths)
    (maybe-interrupt)
    (when (< 0 (b/size paths))
      ; (prn :paths (datafy paths))
      ; First, do we have any paths which are loops? Try to find one which is
      ; valid without a tail. If we have one, we're done. If not, we discard
      ; those loops.
      (loopr [paths' (b/linear bl/empty)]
             [^BFSPath path paths :via :iterator]
             (if (.isLoop path)
               (if (.isValid path)
                 (if (not (tail? path))
                   ; Done!
                   (do ;(prn :found (datafy path))
                       (into [] (.ops path)))
                   ; We have a tail--can we prune it?
                   (do ;(prn :loop-has-tail (datafy path))
                       (or (trim-loop g init-path path)
                           (recur paths'))))
                 ; A loop, but not valid: drop this
                 (do ;(prn :loop-not-valid (datafy path))
                     (recur paths')))
               ; Not a loop; keep going
               (recur (bl/add-last paths' path)))
             ; We now have a set of non-loop paths to expand
             (do ;(prn :remaining-paths paths' (datafy paths'))
                 ; Recurs to enclosing loop!
                 (recur (expand-paths g paths')))))))

(defn search
  "Searches a graph for a cycle matching `spec`. Returns a cycle, or nil."
  [g spec]
  (let [init-path (spec->path spec)]
    ;(prn :init-path init-path)
    (loopr []
           [op (bg/vertices g) :via :iterator]
           (do ;(prn)
               ;(prn "Starting with" (:index op))
               (or (search-from-op g init-path op)
                   (recur))))))
