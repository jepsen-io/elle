(ns elle.util
  "Kitchen sink"
  (:require [clojure.core.reducers :as r]))

(defn nanos->secs
  "Convert nanoseconds to seconds"
  [nanos]
  (/ nanos 1e9))

(defn map-kv
  "Takes a function (f [k v]) which returns [k v], and builds a new map by
  applying f to every pair."
  [f m]
  (into {} (r/map f m)))

(defn map-vals
  "Maps values in a map."
  [f m]
  (map-kv (fn [[k v]] [k (f v)]) m))
