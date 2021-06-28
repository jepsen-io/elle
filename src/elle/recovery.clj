(ns elle.recovery
  "Recoverability is the property that lets us map back and forth between
  *operations* (e.g. a write or read) and *versions*. Reads are trivially
  recoverable: they return the version they read! Writes, however, are
  trickier: it depends on the datatype.

  - For registers, a write encodes its whole version: w(5) produces 5.

  - For counter increment, a write produces any value higher than the write.
    w(3) could produce 3, 4, 5, ....

  - For set add, a write identifies *some* element in the list. w(5) could
    produce {5}, {1, 5}, {1, 5, 6}, etc.

  - For list append, a write identifies the *final* element in the list. w(5)
    could produce [5], [1 2 5], [6 5], and so on.

  The goal, of course, is to take these relations, and produce a *bijection*
  between (some, if not all) ops and versions. We do this by using reads and
  traceability to constrain the version space; wherever versions in that space
  unambioguously correspond to a particular write, that write is recoverable.

  The actual mechanism for recoverability is datatype dependent. Here, we
  provide a polymorphic *Recovery* type, which allows Elle to map between
  operations and versions, and to explain those mappings."
  (:require [elle [history :as history]]
            [jepsen [txn :as txn]]
            [knossos [op :as op]]))

(set! *warn-on-reflection* true)

(defprotocol WriteRecovery
  "Maps between writes and versions."
  (write->version [r mop]
                  "Takes a write micro-op (e.g. [f k v]) and returns the
                  version which that micro-op produced, if known.")

  (explain-write->version [r mop version]
                          "Returns an Explanation justifying the
                          write-to-version relationship.")

  (version->write [r k version]
                   "Takes a key and a version, and returns the the [op mop]
                   which produced that version.")

  (explain-version->write [r k version [op mop]]
                          "Takes a key, version, and an op-mop pair, and
                          returns an Explanation justifying why that particular
                          version had to have been written by that mop in that
                          op."))

(defprotocol ReadRecovery
  "Maps between versions and reads."
  (version->reads [r k version]
                  "Takes a key and a version, and returns a collection of [op
                  mop]s which read that version."))

(defrecord WriteReadRecovery [writes reads]
  WriteRecovery
  (write->version [_ mop]
    (write->version writes mop))

  (explain-write->version [_ mop version]
    (explain-write->version writes mop version))

  (version->write [_ k version]
    (version->write writes k version))

  (explain-version->write [_ k version op+mop]
    (explain-version->write writes k version op+mop))

  ReadRecovery
  (version->reads [_ k version]
    (version->reads reads k version)))

(defn write-read-recovery
  "A unified Recovery object which glues together a write recovery and a read
  recovery."
  [writes reads]
  (WriteReadRecovery. writes reads))

(defn known-aborted-versions
  "Given an analysis with a :history and a :recovery, returns a map of keys to
  sets of versions which are known to have been written by aborted
  transactions."
  [analysis]
  (let [r (:recovery analysis)]
    (->> (history/known-aborted (:history analysis))
         (txn/reduce-mops (fn [aborted op [k :as mop]]
                            (if-let [v (write->version r mop)]
                              (let [vs (get aborted k #{})]
                                (assoc aborted k (conj vs v)))
                              aborted))))))

(defn known-intermediate-versions
  "Given an analysis with a :history and a :recovery, returns a map of keys to
  sets of versions which are known to have been written by intermediate
  transactions."
  [analysis]
  (let [r (:recovery analysis)]
    ; Take all intermediate versions across all operations...
    (->> (:history analysis)
         (filter op/invoke?)
         (map txn/int-write-mops)
         ; We don't care about grouping by keys; just give us a
         ; big bag of mops.
         (mapcat vals)
         ; And map those, via recovery, back to versions.
         (reduce (fn [m [f k :as mop]]
                   (if-let [version (write->version r mop)]
                     (let [vs (get m k #{})]
                       (assoc m k (conj vs version)))))))))
