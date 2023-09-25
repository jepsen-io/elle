(ns elle.closed-predicate
  "A test for predicate safety. Uses a closed-universe assumption to
  infer the version set selected for transactions based not only on what the
  predicate matches, but based on what it *doesn't* match.

  In Adya's formalism, predicate dependencies cover the versions a transaction
  reads/writes which match the predicate. However, any read or write of these
  versions also appears as a non-predicate read or write in the history: these
  are *item* dependencies. But predicate dependencies *also* cover versions a
  transaction does *not* read or write. Indeed, any predicate operation a
  transaction performs captures a 'Version Set' (vset) including some version
  of(basically) every object in the database. Even unborn and dead ones. How
  are we going to infer these additional predicate dependencies, given they
  cover records which do not match the predicate?

  How do you take a photograph of something invisible?

  Let us assume that we know every version of some object x. Let us then assume
  there are at most *two* versions of x: x0, x1. Now assume we have a predicate
  transaction which performs a predicate read covering x, and it reads nothing:

    T1: r(VSet(P))

  Now evaluate P(x0) and P(x1) to see whether those versions match the
  predicate. Note that unborn and dead versions do not match predicates. There
  are four possible cases:

  1. Both x0 and x1 match. *Any* choice of VSet(P) should have returned
  something. This is illegal; something is terribly wrong in the DB.

  2. x0 matches, x1 doesn't. VSet(P) must have selected x1.

  3. x1 matches, x0 doesn't. VSet(P) must have selected x0.

  4. Neither match. We cannot tell which VSet(P) chose.

  This allows us to infer a subset of VSet(P) *even when values are unread*.
  From this we can infer the additional dependency edges in the Adya formalism!

  ## Predicates

  We need a structure to describe a predicate. These are:

  :true. The trivial predicate, which matches everything. This is still
  useful--predicates never match unborn or dead versions.

  [:= 2]. Matches every object whose value which is equal to 2.

  [:mod 2 0] Matches every object whose value, modulo two, is zero.

  ## Operations

  We perform an initial *universe-constructing* operation which establishes the
  state of the universe. We're trusting the database positively, definitely has
  this state--perhaps by writing it to a healthy cluster, waiting, and reading
  the state back on every replica to ensure it's definitively present. We
  choose to believe that the database will not return prior (e.g. unborn)
  states. The value for this operation is a map of keys (e.g. :x) to initial
  versions (e.g. 1).

    {:f :init, :value {:x 1, :y 2, ...}}

  Then we perform transactions whose values are (as usual) sequences of
  micro-operations:

    {:f :txn, :value [mop1, mop2, ...]}

  These micro-operations are of the following forms:

    [:insert :x 1]

  Inserts key x with value 1.

    [:delete :x]

  Deletes key x.

    [:w :x 2]

  Sets x's value to 2.

    [:r :x 2]

  A normal object read of key :x, observing version 2.

    [:rp :true {:x 1, :y 2}]

  A predicate read. The predicate :true matches everything. This read observed
  key x's value as 1 and key y's value as 2.

  ## Representations

  We represent the unborn version as :elle/unborn, and the dead version as
  :elle/dead."
  (:require [clojure [pprint :refer [pprint]]
                     [set :as set]]
            [clojure.tools.logging :refer [info warn]]
            [dom-top.core :as dt :refer [loopr]]
            [elle [core :as elle]
                  [graph :as g]
                  [rw-register :as rw-register]
                  [txn :as ct]
                  [util :as util :refer [index-of]]]
            [slingshot.slingshot :refer [try+ throw+]]
            [jepsen [history :as h]
                    [txn :as txn]]))

(defn xor
  "Exclusive or. A and not B, or B and not A."
  [a b]
  (if a
    (not b)
    (boolean b)))

(defn ext-writes-txn
  "Given a transaction, returns a map of keys to values for its external
  writes."
  [txn]
  (loopr [ext (transient {})]
         [[f k v :as mop] txn]
         (recur
           (case f
             :w       (assoc! ext k v)
             :insert  (assoc! ext k v)
             :delete  (assoc! ext k :elle/dead)
             ext))
         (persistent! ext)))

(defn ext-writes-op
  "Given an init or txn operation, returns a map of keys to values for its
  external writes."
  [op]
  (case (:f op)
    :init (:value op)
    :txn  (ext-writes-txn (:value op))))

(defn ext-writes
  "Given a history, computes a map of keys to values to the op which wrote
  that value."
  [history]
  (loopr [writes {}]
         [op    (h/possible history)
          [k v] (ext-writes-op op)]
         (recur (let [k-writes (get writes k {})
                      v-write  (get k-writes v)]
                  (if v-write
                    (throw+ {:type ::multiple-writes-of-same-value
                             :key   k
                             :value v
                             :op    op})
                    (assoc writes k
                           (assoc k-writes v op)))))))

(defn write-mop-index
  "Takes an operation, a key, and a value. Returns the index of the mop in that
  transaction which set the key to that value, or -1 if not found. For init
  ops, the index is always 0 iff the init op wrote that value."
  [op k v]
  (case (:f op)
    :init (if (= v (get (:value op) k ::not-found))
            0
            -1)
    :txn (let [txn (:value op)]
           (loop [i 0]
             (if (= i (count txn))
               -1
               (let [[f k' v'] (nth txn i)]
                 (if (not= k k')
                   ; Wrong key
                   (recur (inc i))
                   ; Right key
                   (case f
                     :w      (if (= v v')                  i (recur (inc i)))
                     :insert (if (= v v')                  i (recur (inc i)))
                     :delete (if (identical? v :elle/dead) i (recur (inc i)))
                     (recur (inc i))))))))))

(defn conj-version
  "Takes an all-versions map of keys to vectors of versions those keys took on,
  and a version we know existed, in order. Adds that version. If the key is not
  in the map, also adds a preceding unborn version."
  [versions k v]
  (let [vs (get versions k [:elle/unborn])]
    (assoc versions k (conj vs v))))

(defn all-versions
  "Returns a map of keys to vectors of all versions of that key in the history,
  in version order."
  [history]
  (loopr [versions {}]
         [op (h/possible history)]
         (recur
           (case (:f op)
             ; Init is always the first thing, and there should only ever be
             ; one. TODO: validate this.
             :init (update-vals (:value op) vector)
             :txn (loopr [versions versions]
                         [[f & args] (:value op)]
                         (recur
                           (case f
                             :insert (let [[k v] args]
                                       (conj-version versions k v))
                             :delete (let [[k] args]
                                       (conj-version versions k :elle/dead))
                             :w (let [[k v] args]
                                  (conj-version versions k v))
                             ;:r (let [[k v] args]
                             ;     (update versions k conj v))
                             ;:rp (let [[pred reads] args]
                             ;      (loopr [versions versions]
                             ;             [[k v] reads]
                             ;             (recur (update versions k conj v)))))))))))
                             ; Ignore reads. We're going to assume our writes
                             ; tell us every version.
                             versions)))))))

(defn version-before
  "Takes an all-versions map of keys to vectors of versions, a key, and a
  version. Returns the version immediately before the given version, or nil if
  none is known."
  ([all-versions k v]
   (version-before (get all-versions k) v))
  ([versions target-version]
   (loopr [preceding nil]
          [v versions]
          (if (= v target-version)
            preceding
            (recur v)))))

(defn version-after
  "Takes an all-versions map of keys to vectors of versions, a key, and a
  version. Returns the version immediately after the given version, or nil if
  none is known.

  We may be asked for the version after the unborn version, even when the
  unborn version is *not* in the version order--for instance, because we
  assumed its existence due to init. When this happens, we return the first
  version in the order."
  ([all-versions k v]
   (version-after (get all-versions k) v))
  ([versions target-version]
   (if (identical? :elle/unborn target-version)
     ; Unborn must be one of the first two versions
     (let [[v0 v1] versions]
       (if (identical? :elle/unborn v0)
         v1
         v0))
     ; Some non-unborn version
     (loopr [preceding nil]
            [v versions]
            (if (= preceding target-version)
              v
              (recur v))
            ; Work around a bug in dom-top--fixed now; we can remove this in
            ; the next release.
            (do nil)))))

(defn versions-after
  "Takes an all-versions map of keys to vectors of versions, a key, and a
  version. Returns all versions of that key which follow the given version.
  Every version follows :elle/unborn."
  ([all-versions k v]
   (versions-after (get all-versions k) v))
  ([versions target-version]
   ; Special handling for unborn
   (if (identical? :elle/unborn target-version)
     (if (identical? :elle/unborn (first versions))
       (subvec versions 1)
       versions))
   ; Some non-unborn version
   (loop [i 0]
     ; Stop when there are no versions that could follow
     (when (< i (dec (count versions)))
       (if (= (nth versions i) target-version)
         ; Found it
         (subvec versions (inc i))
         ; Keep looking
         (recur (inc i)))))))

(defn version<
  "Takes an all-versions map of keys to vectors of versions, a key, and two
  versions a and b. Returns true iff a precedes b in the version order."
  ([all-versions k a b]
   (version< (get all-versions k) a b))
  ([versions a b]
   (loopr [found-a? false]
          [v versions]
          (if found-a?
            (if (= v b)
              true
              (recur found-a?))
            (if (= v a)
              (recur true)
              (recur found-a?))))))

(defn resolve-version
  "Both unborn and dead versions are returned by the database as `nil`.
  However, if we know that a key never had a dead version, a nil read *must* be
  unborn, and vice-versa. Takes an all-versions map, a key, and a value.
  Returns the value if non-nil. If nil, tries to return :elle/unborn or
  :elle/dead if we can prove it must have been one or the other. Otherwise,
  returns nil."
  [all-versions k v]
  (if (nil? v)
    (let [versions (get all-versions k [])
          unborn?  (identical? :elle/unborn (first versions))
          dead?    (identical? :elle/dead   (peek versions))]
      (cond (and unborn? dead?) nil ; Can't tell
            unborn?             :elle/unborn
            dead?               :elle/dead
            ; Weird. Let's assume unborn; this must be a case where we read
            ; prior to the initial write.
            true                :elle/unborn))
    v))

(defn eval-pred
  "Evaluates a predicate on a single version, returning true iff it matches."
  [pred version]
  (condp identical? version
    :elle/unborn false
    :elle/dead   false
    (case pred
      :true true
      ; Assume our predicate is of the form [pred-type ...]
      (case (first pred)
        := (let [goal (second pred)]
             (= goal version))

        :mod (let [[_ modulus target] pred]
               (= target (mod version modulus)))))))

(defn pred-mop?
  "Is this micro-operation a predicate operation?"
  [[f]]
  (or (identical? :rp f)))

(defn pred-read-miss-cases
  "Takes an all-versions map and a history. Runs through all predicate reads in
  a history, and yields a seq (or nil) of error maps where a predicate read
  *must* have observed something (e.g. because every known version of a key
  matched the predicate), but that key didn't appear in the read set."
  [all-versions history]
  (->> history
       h/oks
       (mapcat
         (fn per-op [op]
           ; For every predicate read, and every key in the universe...
           (loopr [errs (transient [])]
                  [[f pred v :as mop] (filter pred-mop? (:value op))
                   [k versions] all-versions]
                  (if (contains? v k)
                    ; We read this key; it's fine
                    (recur errs)
                    (if (every? (partial eval-pred pred) versions)
                      ; This predicate matched *every* version of this key;
                      ; it should have appeared.
                      (recur
                        (conj! errs {:op        op
                                     :mop       mop
                                     :key       k
                                     :versions  versions}))
                      (recur errs)))
                  (persistent! errs))))
       util/empty->nil))

(defn version-set
  "Takes all versions and a micro-operation (right now, just :rp) and returns a
  map of keys to versions we can show must have been in VSet(P)."
  [all-versions [f pred v]]
  (case f
    :rp (let [; If we read something, it must have been in VSet(P).
              positive v
              ; What keys did we not read?
              unseen-keys (remove (set (keys positive)) (keys all-versions))
              match? (partial eval-pred pred)]
          (loopr [vset positive]
                 [[k versions] all-versions]
                 (recur
                   (if (contains? vset k)
                     ; Already known
                     vset
                     ; Didn't observe this one. Can we use process of
                     ; elimination?
                     (let [candidates (remove match? versions)]
                       ;(info :versions versions :candidates candidates)
                       (condp = (count candidates)
                         ; Something's terribly wrong. If every version
                         ; matched, one should have appeared in the predicate
                         ; read. We catch this explicitly in
                         ; predicate-read-miss-cases. If it does happen, the
                         ; most charitable interpretation is that we somehow
                         ; chose the unborn version (even though the unborn
                         ; version was never supposed to exist). It could also
                         ; be outright data loss--a :dead version that was
                         ; never generated, but :unborn feels more
                         ; conservative, and will manifest as explicable
                         ; cycles.
                         0 (assoc vset k :elle/unborn)
                         ; Any other version would have appeared in the
                         ; predicate read, so we can prove this non-matching
                         ; version must have been in VSet(P).
                         1 (assoc vset k (first candidates))
                         ; Ambiguous.
                         vset))))))))

(defn version-sets
  "We need to use the version sets of predicate reads repeatedly. To speed
  this up, we construct a cache which maps micro-operations to version sets."
  [all-versions history]
  (loopr [vsets (transient {})]
         [op  (->> history h/oks (h/filter-f :txn))
          mop (filter pred-mop? (:value op))]
         (recur (if (contains? vsets mop)
                  vsets
                  (assoc! vsets mop (version-set all-versions mop))))
         (persistent! vsets)))

(defrecord RWExplainer [all-versions vsets]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (let [b-writes (ext-writes-op b)]
      ; First, try to find a kv link. Loop over kv reads in a, looking
      ; for cases where b overwrote a's read.
      (or (loopr []
                 [[f k v :as mop] (filter (comp #{:r} first) (:value a))]
                 (let [v (resolve-version all-versions k v)]
                   ; Was there a value following this read?
                   (if-let [v' (version-after all-versions k v)]
                     ; And did b write it?
                     (if (= v' (get b-writes k ::not-found))
                       {:type :rw
                        :key   k
                        :value v
                        :value' v'
                        :a-mop-index (index-of (:value a) mop)
                        :b-mop-index (write-mop-index b k v')}
                       ; b wrote something else
                       (recur))
                     ; No next version
                     (recur))))

          ; Failing that, try a predicate relation. Loop over predicate reads
          ; in a, looking for cases where b overwrote a's read.
          (loopr []
                 [mop (filter pred-mop? (:value a))]
                 (let [[_ pred] mop
                       vset     (vsets mop)]
                   ; Loop over b's external writes
                   (or (loopr []
                              [[k v'] b-writes]
                              (let [v (get vset k ::not-found)]
                                ; Did b overwrite k and change the match of
                                ; pred?
                                (if (and (not= ::not-found v)
                                         (version< all-versions k v v')
                                         (xor (eval-pred pred v)
                                              (eval-pred pred v')))
                                  {:type           :rw
                                   :key            k
                                   :value          v
                                   :value'         v'
                                   :predicate?     true
                                   :predicate-read mop
                                   :a-mop-index    (index-of (:value a) mop)
                                   :b-mop-index    (write-mop-index b k v')}
                                  (recur))))
                       ; Next predicate read
                       (recur)))))))

  (render-explanation [_ {:keys [key value value' predicate-read]} a-name b-name]
    (if predicate-read
      (str a-name " performed a predicate read " (pr-str predicate-read)
           " of key " (pr-str key) " and selected version " (pr-str value)
           ", which was overwritten by " b-name "'s write of " value'
           ", which also changed whether the predicate would have matched. "
           "Note that key " (pr-str key) "'s version order was "
           (pr-str (get all-versions key)))
      (str a-name " read key " (pr-str key) " = " (pr-str value)
           ", which was overwritten by " b-name "'s write of " value'))))

(defn rw-graph
  "Takes an analysis map and a history. Returns a graph of both item and
  predicate read-write dependencies.

  For items: T1 -rw-> T2 if T1 performs a read of x1 and T2 installs some x2,
  and x1 directly precedes x2 in the version order.

  For predicates: T1 -rw-> T2 if T1 performs a predicate read P where VSet(P)
  included version x1, and T2 installs some x2, and x1 << x2 in the version
  order, and T2 changed whether P matched: that is, P matches x1 but not x2, or
  P matches x2 but not x1."
  [{:keys [all-versions vsets ext-writes]} history]
  {:graph
   (loopr [g (g/linear (g/digraph))]
          [op          (h/oks history)
           [f :as mop] (:value op)]
          (recur
            (condp identical? f
              ; KV read
              :r (let [[f k v] mop
                       v       (resolve-version all-versions k v)]
                   (if-let [v' (version-after all-versions k v)]
                     (if-let [write (get-in ext-writes [k v'])]
                       (if (= op write)
                         ; Don't generate self-edges
                         g
                         ; write overwrote this op.
                         (g/link g op write))
                       ; Don't know who wrote the next version
                       g)
                     ; No known next version
                     g))

              ; Predicate read
              :rp (let [[f pred] mop]
                    (loopr [g g]
                           ; For each version in the version set
                           [[k v] (vsets mop)
                            ; And every version following it in the version
                            ; order
                            v'    (versions-after all-versions k v)]
                           ; Did v' change the predicate match?
                           (recur (if (xor (eval-pred pred v)
                                           (eval-pred pred v'))
                                    ; Find txns that wrote it
                                    (if-let [write (get-in ext-writes [k v'])]
                                      ; Don't generate self-edges
                                      (if (= op write)
                                        g
                                        (g/link g op write))
                                      ; No writer known
                                      g)
                                    ; Didn't change the predicate
                                    g))))
                    ; Some other kind of mop
                    g))
          ; Later we should break out predicate vs non-predicate deps so we can
          ; distinguish G2 from G2-item?
          (g/named-graph :rw (g/forked g)))
   :explainer (RWExplainer. all-versions vsets)})

(defrecord WRExplainer [all-versions vsets]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    ; Try for an item dependency
    (let [writes (ext-writes-op a)]
      (or (loopr []
                 [[f k v :as mop] (:value b)]
                 (if-not (identical? f :r)
                   (recur)
                   (let [v (resolve-version all-versions k v)]
                     (if-not (= v (get writes k))
                       (recur)
                       {:type        :wr
                        :key         k
                        :value       v
                        :a-mop-index (write-mop-index a k v)
                        :b-mop-index (index-of (:value b) mop)}))))
          ; Barring that, a predicate dependency
          (loopr []
                 [mop   (filter pred-mop? (:value b))
                  [k v] (vsets mop)]
                 (if (= v (get writes k))
                   {:type  :wr
                    :key   k
                    :value v
                    :predicate-read mop
                    :a-mop-index (write-mop-index a k v)
                    :b-mop-index (index-of (:value b) mop)}
                   (recur))))))

  (render-explanation [_ {:keys [key value predicate-read]} a-name b-name]
    (if predicate-read
      (str a-name " set key " (pr-str key) " to " (pr-str value)
           ", which was in the version set of predicate read "
           (pr-str predicate-read) ". Note that the version order of key "
           (pr-str key) " was " (pr-str (get all-versions key)))
      (str a-name " wrote " (pr-str key) " = " (pr-str value)
           ", which was read by " b-name))))

(defn wr-graph
  "Takes an analysis map and a history. Returns a graph of both item and
  predicate write-read edges. T1 -wr-> T2 if T1 installs some x that T2
  performs a standard (e.g. non-predicate) read of. T1 -wrp-> T2 if T1 installs
  some version x1 and T2 performs a predicate read [:rp pred ...] and x1 is in
  VSet(pred)."
  [{:keys [all-versions vsets ext-writes]} history]
  {:graph
   (loopr [g (g/linear (g/digraph))]
          [op               (h/oks history)
           [f k v :as mop]  (:value op)]
          (recur
            (condp identical? f
              ; Item read
              :r (let [v (resolve-version all-versions k v)]
                   (if-let [write (get-in ext-writes [k v])]
                     ; Don't generate self-edges
                     (if (= op write)
                       g
                       (g/link g write op))
                     ; No writer known
                     g))
              ; Predicate read
              :rp (loopr [g g]
                         [[k v] (vsets mop)]
                         (recur
                           (if (identical? v :elle/unborn)
                             ; Don't bother generating an edge; we don't
                             ; explicitly represent the Adya init txn.
                             g
                             ; What transaction wrote that version?
                             (if-let [write (get-in ext-writes [k v])]
                               (if (= write op)
                                 g ; No self-edges
                                 (g/link g write op))
                               ; No writer known
                               g))))
              ; Some other mop
              g))
          (g/named-graph :wr (g/forked g)))
   :explainer (WRExplainer. all-versions vsets)})

(defrecord WWExplainer [all-versions]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (let [a-writes (ext-writes-op a)
          b-writes (ext-writes-op b)]
      (loopr []
             [[k v'] b-writes]
             (if-let [v (version-before all-versions k v')]
               ; We have a prior version
               (if (= v (get a-writes k))
                 ; Found it
                 {:type  :ww
                  :key    k
                  :value  v
                  :value' v'
                  :a-mop-index (write-mop-index a k v)
                  :b-mop-index (write-mop-index b k v')}
                 ; Not the previous write
                 (recur))
               ; No prior version
               (recur)))))

  (render-explanation [_ {:keys [key value value']} a-name b-name]
    (str a-name " set key " (pr-str key) " to " (pr-str value)
         ", which " b-name " overwrote with " (pr-str value'))))

(defn ww-graph
  "Takes an analysis map and a history. Returns a graph of write-write edges.
  T1 -ww-> T2 if T1 installs some x and T2 installs some x' such that x
  directly precedes x' in the version order."
  [{:keys [all-versions ext-writes]} history]
  {:graph
   (loopr [g (g/linear (g/digraph))]
          [op (h/possible history)
           [f k v :as mop] (:value op)]
          (recur
            (case f
              (:insert :write :delete)
              (let [v' (if (identical? f :delete) :elle/dead v)]
                (if-let [v (version-before all-versions k v')]
                  (if-let [write (get-in ext-writes [k v])]
                    (if (= op write)
                      g
                      (g/link g write op))
                    ; No writer known
                    g)
                  ; No prior version
                  g))

              ; Some other mop
              g))
          (g/named-graph :ww (g/forked g)))
   :explainer (WWExplainer. all-versions)})

(defn graph
  "Given an analysis map (e.g. :all-versions, etc) and a history, computes a
  transaction dependency graph."
  [analysis history]
  ((elle/combine (partial ww-graph analysis)
                 (partial wr-graph analysis)
                 (partial rw-graph analysis))
   history))

(defn check
  "Checker for closed predicate histories. Options are: TODO

  "
  ([history]
   (check {} history))
  ([opts history]
   (let [history        (h/client-ops history)
         all-versions   (all-versions history)
         ;_              (info :all-versions (with-out-str (pprint all-versions)))
         vsets          (version-sets all-versions history)
         ext-writes     (ext-writes history)
         pred-read-miss (pred-read-miss-cases all-versions history)
         analysis     {:all-versions all-versions
                       :vsets        vsets
                       :ext-writes   ext-writes}
         analyzers    (into [(partial graph analysis)]
                            (ct/additional-graphs opts))
         analyzer     (apply elle/combine analyzers)
         cycles       (:anomalies (ct/cycles! opts analyzer history))
         anomalies    (cond-> cycles
                        pred-read-miss (assoc :predicate-read-miss pred-read-miss))]
     ;(println "versions")
     ;(pprint all-versions)
     ;(println "cycles")
     ;(pprint cycles)
     (ct/result-map opts anomalies))))

(defn gen-key-type
  "Is this key eligible for an :insert, :w, or :delete? Options:

    :insert-only? If true, all keys are of type :insert."
  [opts k]
  (if (:insert-only? opts)
    :insert
    (case (long (mod k 3))
      0 :insert
      1 :w
      2 :delete)))

(defn gen-pred
  "Generates a random predicate."
  []
  (case (long (rand-int 3))
    ; Equality: either 0 or 1, our initial values.
    0 [:= (rand-int 2)]
    ; Modulo: mod 2 should be either 0 or 1.
    1 [:mod 2 (rand-int 2)]
    ; Trivial
    2 :true))

(defn gen
  "Constructs a lazy sequence of operations for a closed predicate test. Begins
  with an init operation, and then a series of transactions affecting various
  keys. Stops when no more mutations are possible. Options:

    :insert-only?         If true, init creates nothing; the only writes
                          possible are inserts. This might be helpful when you
                          suspect anomalies are a consequence of reading state
                          prior to the init txn. Default: false.

    :key-count            Number of total keys in the test. Default: 50.

    :min-txn-length       Minimum number of operations per txn. Default: 1.

    :max-txn-length       Maximum number of operations per txn. Default: 4."
  ([opts]
   (let [key-count      (:key-count opts 50)
         min-txn-length (:min-txn-length opts 1)
         max-txn-length (:max-txn-length opts 4)
         ; Start with an init txn. We want to mix inserts, writes, and deletes,
         ; but we only get to do one mutation per key. Ask gen-key-type what
         ; kind of operation we'll do on each key, and create an init txn for
         ; keys with writes and deletes.
         ks  (shuffle (range key-count))
         init-ks (filter (comp #{:w :delete} (partial gen-key-type opts)) ks)]
     (cons {:type  :invoke
            :f     :init
            :value (into (sorted-map)
                         (zipmap init-ks
                                 ; Assign them random values, all 0 or 1.
                                 (repeatedly (partial rand-int 2))))}
           (gen {:key-count      key-count
                 :min-txn-length min-txn-length
                 :max-txn-length max-txn-length
                 :insert-only?   (:insert-only? opts)}
                {; Keys we can mutate
                 :ks         ks
                 ; Next value to write
                 :next-write 2}))))
  ([opts state]
   (lazy-seq
     (let [{:keys [key-count min-txn-length max-txn-length]} opts
           {:keys [ks next-write]} state]
       (when (seq ks)
         (loop [i          (+ min-txn-length (rand-int max-txn-length))
                ks         ks
                next-write next-write
                txn        (transient [])]
           (if (or (zero? i) (empty? ks))
             ; Done!
             (cons {:type :invoke, :f :txn, :value (persistent! txn)}
                   (gen opts {:ks ks, :next-write next-write}))
             ; Read, predicate reads, or mutation?
             (let [i' (dec i)]
               (case (long (rand-int 3))
                 ; Read
                 0 (recur i' ks next-write
                          (conj! txn [:r (rand-int key-count) nil]))
                 ; Predicate read
                 1 (recur i' ks next-write (conj! txn [:rp (gen-pred) nil]))
                 ; Mutation
                 2 (let [[k & ks'] ks]
                     (case (gen-key-type opts k)
                       :insert (recur i' ks' (inc next-write)
                                      (conj! txn [:insert k next-write]))
                       :w (recur i' ks' (inc next-write)
                                 (conj! txn [:w k next-write]))
                       :delete (recur i' ks' next-write
                                      (conj! txn [:delete k])))))))))))))
