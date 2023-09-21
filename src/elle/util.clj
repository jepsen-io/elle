(ns elle.util
  "Kitchen sink"
  (:require [clojure.core.reducers :as r]
            [clojure.tools.logging :refer [info warn]]
            [dom-top.core :refer [loopr]]
            [jepsen.history :as h])
  (:import (java.util.concurrent ExecutionException)
           (java.util.function BinaryOperator)
           (io.lacuna.bifurcan IMap
                               IntMap
                               Map)
           (jepsen.history Op)))

(defn empty->nil
  "Takes a collection coll and returns coll iff it is non-empty; otherwise nil."
  [coll]
  (when (seq coll)
    coll))

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

(defn op-memoize
  "Memoizes a pure function of an operation. Uses the op's index as a key to
  speed up access. Thread-safe."
  [f]
  (let [cache        (atom (IntMap.))
        add-cache (fn [^IntMap m, ^long k, v]
                    (.put m k v))]
    (fn memoized [^Op op]
      (let [index (.index op)
            res   (.get ^IntMap @cache index ::not-found)]
        (if (identical? res ::not-found)
          (let [res (f op)]
            (swap! cache add-cache index res)
            res)
          res)))))
