(ns elle.history
  "This namespace provides basic functions for working with histories,
  including identifying keys, known-committed, and known-aborted operations."
  (:require [knossos [op :as op]]))

(set! *warn-on-reflection* true)

(defn known-committed
  "Returns a sequence of operations which are known to be
  committed."
  [history]
  (filter op/ok? history))

(defn known-aborted
  "Returns a sequence of operations which are known to be aborted."
  [history]
  (filter op/fail? history))
