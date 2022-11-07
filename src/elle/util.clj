(ns elle.util
  "Kitchen sink"
  (:require [clojure.core.reducers :as r]
            [clojure.tools.logging :refer [info warn]]
            [dom-top.core :refer [loopr]])
  (:import (java.util.concurrent ExecutionException)
           (java.util.function BinaryOperator)
           (io.lacuna.bifurcan IMap Map)))

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

(defn index-of
  "Type-hinted .indexOf"
  [^java.util.List coll element]
  (.indexOf coll element))

(defn fast-frequencies
  "Like frequencies, but faster. Returns an IMap."
  [coll]
  (let [add (reify BinaryOperator
              (apply [_ x y] (+ ^Long x ^Long y)))]
    (loopr [^IMap m (.linear (Map.))]
           [x coll]
           (recur (.put m x 1 add))
           (.forked m))))
