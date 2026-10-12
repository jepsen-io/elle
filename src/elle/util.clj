(ns elle.util
  "Kitchen sink"
  (:require [clojure.core.reducers :as r]
            [clojure.tools.logging :refer [info warn]]
            [dom-top.core :refer [loopr]]
            [jepsen.history :as h])
  (:import (java.util Arrays)
           (java.util.concurrent ExecutionException)
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

(deftype OpMemoize [f, ^:volatile-mutable ^objects cache]
  clojure.lang.IFn
  (invoke [this op]
    (let [^Op op      op
          i           (.index op)
          local-cache cache
          size        (alength local-cache)]
      (if (<= size i)
        ; This op index is beyond the local cache; enlarge it
        (do (locking this
              (when (identical? local-cache cache)
                (let [cache' (Arrays/copyOf
                               local-cache (int (max (inc i) (* 1.4 size))))]
                  (Arrays/fill cache' size (alength cache') ::not-found)
                  ; See https://clojure.atlassian.net/browse/CLJ-2743
                  (set! (.cache this) cache'))))
        (recur op))
        ; The cache is big enough; we can use an unsynchronized path here
        (let [res (aget local-cache i)]
          (if-not (identical? res ::not-found)
            ; Cache hit
            res
            ; Cache miss
            (let [res (f op)]
              ; This may miss because the cache gets replaced, but that's fine;
              ; we'll just recompute it later. My intuition here is that
              ; lock-free is simpler and might be faster.
              (aset local-cache i res)
              res)))))))

(defn op-memoize
  "Memoizes a pure function of an operation. Uses the op's index as a key to
  speed up access. Thread-safe."
  [f]
  (OpMemoize. f, (object-array (repeat 1024 ::not-found))))

(defn fand
  "Functional and. Takes a collection of unary functions and returns a single
  function which calls each f and returns the first non-truthy return value, or
  the last return value."
  [fs]
  (condp = (count fs)
    0 (constantly true)
    1 (first fs)
    2 (let [[f2 f1] fs]
        (fn binary [x]
          (and (f1 x) (f2 x))))
    (fn nary [x]
      (reduce (fn [_ f]
                (let [r (f x)]
                  (if r r (reduced r))))
              nil
              fs))))
