(ns elle.version-order
  "The version order, in an Adya history, is a total order over committed,
  installed versions of each object. For our purposes, it's the *maximal linear
  graph* we can reconstruct which is consistent with that order.

  We derive the version order from the version graph by removing intermediate
  and known-aborted versions, then restricting that graph to linear segments."
  (:require [elle [explanation :as expl]
                  [graph :as g]
                  [recovery :as rec]
                  [version-graph :as vg]]))

(set! *warn-on-reflection* true)

(defprotocol VersionOrder
  (all-keys [_]
            "Returns the set of all keys in this version order.")

  (graph [_ k]
         "Returns the Bifurcan directed graph relating successive versions of
         key k.")

  (explain-version-pair [_ k v v']
                        "Explains why for key k, version v precedes v'"))

(defn version-order
  "Derives a version order from an analysis."
  [analysis]
  (let [aborted       (rec/known-aborted-versions analysis)
        version-graph (:version-graph analysis)
        orders        (->> (vg/all-keys version-graph)
                           (map (fn [k]
                                  (let [vg (vg/graph version-graph k)
                                        vg (reduce g/remove vg (get aborted k))
                                        vg (g/remove-split-edges vg)]
                                    [k vg])))
                           (into {}))]
    (reify VersionOrder
      (all-keys [_]
        (keys orders))

      (graph [_ k]
        (get orders k))

      (explain-version-pair [_ k v v']
        expl/trivial))))

(defn add-version-order
  "Takes an analysis map with a :version-graph and :recovery object, and adds a
  :version-order key."
  [analysis]
  (assoc analysis :version-order (version-order analysis)))
