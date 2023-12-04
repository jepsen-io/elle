(ns elle.rels
  "Relationships between transactions."
  (:import (elle BitRels)))

(def none "A dependency with no relationships" BitRels/NONE)
(def ww "A write-write dependency" BitRels/WW)
(def wr "A write-read dependency" BitRels/WR)
(def rw "A read-write dependency" BitRels/RW)
(def wwp "A predicate write-write dependency" BitRels/WWP)
(def wrp "A predicate write-read dependency" BitRels/WRP)
(def rwp "A predicate read-write dependency" BitRels/RWP)
(def process "A process dependency" BitRels/PROCESS)
(def realtime "A realtime dependency" BitRels/REALTIME)

(defn bit-rels?
  "Is this a BitRels?"
  [x]
  (instance? BitRels x))

(defn ^BitRels union
  "Unions any number of BitRels. Nil is treated as BitRels/NONE"
  ([]
   BitRels/NONE)
  ([a]
   (if a a BitRels/NONE))
  ([^BitRels a, ^BitRels b]
   (cond (nil? a) b
         (nil? b) a
         true     (.union a b)))
  ([^BitRels a ^BitRels b & more]
   (reduce union (union a b) more)))
