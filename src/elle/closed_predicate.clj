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

  For this very silly proof of concept, we define our predicate as simply
  `true`: every version except unborn and dead should be returned.

  # Operations

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

  # Representations

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

(defn ext-writes
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
                             ; tel us every version.
                             versions)))))))
(defn versions-after
  "Takes an all-versions map of keys to vectors of versions, a key, and a
  version. Returns all versions of that key which follow the given version."
  ([all-versions k v]
   (versions-after (get all-versions k) v))
  ([versions target-version]
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

(defn eval-pred
  "Evaluates a predicate on a single version, returning true iff it matches."
  [pred version]
  (condp identical? version
    :elle/unborn false
    :elle/dead   false
    (case pred
      :true true)))

(defn pred-mop?
  "Is this micro-operation a predicate operation?"
  [[f]]
  (or (identical? :rp f)))

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
                         ; read.
                         0 (throw+ {:type ::predicate-read-should-have-seen-something
                                    :mop        [f pred v]
                                    :key        k
                                    :versions   versions})
                         ; Any other version would have appeared in the
                         ; predicate read, so we can prove this non-matching
                         ; version must have been in VSet(P).
                         1 (assoc vset k (first candidates))
                         ; Ambiguous.
                         vset))))))))

(defrecord WRPExplainer [all-versions]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    ; Slow, but just for a prototype...
    (let [a-writes (ext-writes (:value a))]
      (loopr []
             [mop   (filter pred-mop? (:value b))
              [k v] (version-set all-versions mop)]
             (do (if (= v (get a-writes k))
                   {:type  :wr
                    :key   k
                    :value v
                    :predicate-read mop
                    :a-mop-index (index-of (:value a) [:w k v])
                    :b-mop-index (index-of (:value b) mop)}
                   (recur))))))

  (render-explanation [_ {:keys [key value predicate-read]} a-name b-name]
    (str a-name " set key " (pr-str key) " to " (pr-str value) ", which was in the version set of predicate read " (pr-str predicate-read))))

(defn wrp-graph
  "Takes an analysis map and a history. Returns a graph of predicate write-read
  dependencies. T1 -wrp-> T2 if T1 installs some version x1 and T2 performs a
  predicate read [:rp pred ...] and x1 is in VSet(pred)."
  [{:keys [all-versions ext-writes]} history]
  {:graph (loopr [g (g/linear (g/digraph))]
                 [op (h/oks history)
                  [f :as mop] (:value op)]
                 (recur
                   (condp identical? f
                     ; Predicate read
                     :rp (loopr [g g]
                                [[k v] (version-set all-versions mop)]
                                (recur
                                  (if (identical? v :elle/unborn)
                                    ; Don't bother generating an edge; we don't
                                    ; explicitly represent the Adya init txn.
                                    g
                                    ; What transaction wrote that version?
                                    (let [writes (get-in ext-writes [k v])]
                                      (assert (= 1 (count writes)))
                                      (g/link g (first writes) op)))))
                     ; Not a predicate read
                     g))
                 ; Later we should have our graph break out predicate vs
                 ; non-predicate deps?
                 (g/named-graph :wr (g/forked g)))
   :explainer (WRPExplainer. all-versions)})

(defrecord RWPExplainer [all-versions]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (let [b-writes (ext-writes (:value b))]
      ; Loop over predicate reads
      (loopr []
             [mop (filter pred-mop? (:value a))]
             (let [[_ pred] mop
                   vset     (version-set all-versions mop)]
               ; Loop over b's external writes
               (or (loopr []
                          [[k v'] b-writes]
                          (let [v (get vset k ::not-found)]
                            ; Did b overwrite k and change the match of pred?
                            (if (and (not= ::not-found v)
                                     (version< all-versions k v v')
                                     (xor (eval-pred pred v)
                                          (eval-pred pred v')))
                              {:type   :rw
                               :key    k
                               :value  v
                               :value' v'
                               :predicate-read mop
                               :a-mop-index (index-of (:value a) mop)
                               ; TODO: extend this to insert/delete
                               :b-mop-index (index-of (:value b) [:w k v'])}
                              (recur))))
                   ; Next predicate read
                   (recur))))))

  (render-explanation [_ {:keys [key value value' predicate-read]} a-name b-name]
    (str a-name " performed a predicate read " (pr-str predicate-read) " of key " (pr-str key) " and selected version " (pr-str value) ", which was overwritten by " b-name "'s write of " value' ", which changed whether the predicate would have matched.")))

(defn rwp-graph
  "Takes an analysis map and a history. Returns a graph of predicate read-write
  dependencies. T1 -rwp-> T2 if T1 performs a predicate read P where VSet(P)
  included version x1, and T2 installs some x2, and x1 << x2 in the version
  order, and T2 changed whether P matched: that is, P matches x1 but not x2, or
  P matches x2 but not x1."
  [{:keys [all-versions ext-writes]} history]
  {:graph
   (loopr [g (g/linear (g/digraph))]
          [op (h/oks history)
           [f pred :as mop] (:value op)]
          (recur
            (condp identical? f
              ; Predicate read
              :rp (loopr [g g]
                         ; For each version in the version set
                         [[k v] (version-set all-versions mop)
                          ; And every version following it in the version order
                          v'    (versions-after all-versions k v)]
                         ; Did v' change the predicate match?
                         (recur (if (xor (eval-pred pred v)
                                         (eval-pred pred v'))
                                  ; Find txns that wrote it
                                  (let [writes (get-in ext-writes [k v'])]
                                    (assert (= 1 (count writes)))
                                    ; Don't generate self-edges
                                    (if (= op (first writes))
                                      g
                                      (g/link g op (first writes))))
                                  ; Didn't change the predicate
                                  g)))
              ; Something else
              g))
          ; Later we should break out predicate vs non-predicate deps so we can
          ; distinguish G2 from G2-item?
          (g/named-graph :rw (g/forked g)))
   :explainer (RWPExplainer. all-versions)})

(defn graph
  "Given an analysis map (e.g. :all-versions, etc) and a history, computes a
  transaction dependency graph."
  [analysis history]
  ((elle/combine (partial wrp-graph analysis)
                 (partial rwp-graph analysis)
                 )
   history))

(defn check
  "Checker for closed predicate histories. Options are: TODO

  "
  ([history]
   (check {} history))
  ([opts history]
   (let [history      (h/client-ops history)
         all-versions (all-versions history)
         ext-writes   (rw-register/ext-index ext-writes
                                             (h/possible history))
         analysis     {:all-versions all-versions
                       :ext-writes   ext-writes}
         analyzers    (into [(partial graph analysis)]
                            (ct/additional-graphs opts))
         analyzer     (apply elle/combine analyzers)
         cycles       (:anomalies (ct/cycles! opts analyzer history))]
     ;(println "versions")
     ;(pprint all-versions)
     ;(println "cycles")
     ;(pprint cycles)
     (ct/result-map opts cycles))))