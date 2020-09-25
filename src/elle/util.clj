(ns elle.util
  "Kitchen sink"
  (:require [clojure.core.reducers :as r]
            [clojure.tools.logging :refer [info warn]])
  (:import (java.util.concurrent ExecutionException)))

(set! *warn-on-reflection* true)

(defn nanos->secs [nanos] (/ nanos 1e9))

(defn maybe-interrupt
  "Throws an InterruptedException if our interrupt flag is set."
  []
  (when (Thread/interrupted)
    (throw (InterruptedException.))))

(defmacro timeout
  "Times out body after n millis, returning timeout-val if that occurs."
  [millis timeout-val & body]
  `(let [worker# (future ~@body)
         retval# (try
                   (deref worker# ~millis ::timeout)
                   (catch ExecutionException ee#
                     (throw (.getCause ee#))))]
     (if (= retval# ::timeout)
       (do (future-cancel worker#)
           ~timeout-val)
       retval#)))

(defn map-kv
  "Takes a function (f [k v]) which returns [k v], and builds a new map by
  applying f to every pair."
  [f m]
  (into {} (r/map f m)))

(defn map-vals
  "Maps values in a map."
  [f m]
  (map-kv (fn [[k v]] [k (f v)]) m))

(defn map-compose
  "Given a map of a->b and b->c, returns a map of a->c."
  [ab bc]
  (map-vals bc ab))

(defn keyed-map-compose
  "Sort of a weird function. You've got two maps: a->b, and b->c. You want the
  composition of these maps: a->c. Now, lift that to maps of *keys* to maps of
  as to bs: k->a->b and k->b->c, returning a map of k->a->c."
  [kab kbc]
  (reduce (fn [kac [k ab]]
            (assoc kac k
                   (when-let [bc (get kbc k)]
                     (map-compose ab bc))))
          {}
          kab))
