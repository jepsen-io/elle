(ns elle.list-append
  "Detects cycles in histories where operations are transactions over named
  lists lists, and operations are either appends or reads."
  (:refer-clojure :exclude [test])
  (:require [clojure [pprint :refer [pprint]]
                     [set :as set]
                     [string :as str]]
            [clojure.core.reducers :as r]
            [clojure.java.io :as io]
            [clojure.tools.logging :refer [info error warn]]
            [dom-top.core :as dt :refer [loopr]]
            [elle [core :as elle]
                  [graph :as g]
                  [txn :as ct]
                  [util :as util :refer [index-of
                                         nanos->secs]]]
            [hiccup.core :as hiccup]
            [jepsen [history :as h]
                    [txn :as txn :refer [reduce-mops]]]
            [jepsen.txn.micro-op :as mop]
            [slingshot.slingshot :refer [try+ throw+]]
            [tesser.core :as t])
  (:import (io.lacuna.bifurcan DirectedGraph
                               Graphs
                               ICollection
                               IList
                               ISet
                               IGraph
                               Set
                               SortedMap)))

(defn verify-mop-types
  "Takes a history where operation values are transactions. Verifies that the
  history contains only reads [:r k v] and appends [:append k v]. Returns nil
  if the history conforms, or throws an error object otherwise."
  [history]
  (when-let [bad (->> (t/filter (fn bad? [op]
                                  (loopr [res nil]
                                         [[f] (:value op)]
                                         (if (or (identical? f :r)
                                                 (identical? f :append))
                                           (recur nil)
                                           op))))
                      (t/take 8)
                      (t/into [])
                      (h/tesser history))]
    (when (seq bad)
      (throw+ {:valid?    :unknown
               :type      :unexpected-txn-micro-op-types
               :message   "history contained operations other than appends or reads"
               :examples  bad}))))

(defn verify-unique-appends
  "Takes a history of txns made up of appends and reads, and checks to make
  sure that every invoke appending a value to a key chose a unique value."
  [history]
  (loopr [written (transient {})]
         [op      history :via :reduce
          [f k v] (:value op)]
         (if (and (h/invoke? op)
                  (identical? f :append))
           (let [writes-of-k (written k #{})]
             (if (contains? writes-of-k v)
               (throw+ {:valid?   :unknown
                        :type     :duplicate-appends
                        :op       op
                        :key      k
                        :value    v
                        :message  (str "value " v " appended to key " k
                                       " multiple times!")})
               (recur (assoc! written k (conj writes-of-k v)))))
           ; Something other than an invoke append, whatever
           (recur written))))

(defn g1a-cases
  "G1a, or aborted read, is an anomaly where a transaction reads data from an
  aborted transaction. For us, an aborted transaction is one that we know
  failed. Info transactions may abort, but if they do, the only way for us to
  TELL they aborted is by observing their writes, and if we observe their
  writes, we can't conclude they aborted, sooooo...

  This function takes a history (which should include :fail events!), and
  produces a sequence of error objects, each representing an operation which
  read state written by a failed transaction."
  [history]
  ; Build a map of keys to maps of failed elements to the ops that appended
  ; them.
  (let [failed (ct/failed-writes #{:append} history)]
    ; Look for ok ops with a read mop of a failed append
    (->> history
         h/oks
         ct/op-mops
         (mapcat (fn [[op [f k v :as mop]]]
                   (when (= :r f)
                     (keep (fn [e]
                             (when-let [writer (get-in failed [k e])]
                               {:op        op
                                :mop       mop
                                :writer    writer
                                :element   e}))
                           v)))))))

(defn g1b-cases
  "G1b, or intermediate read, is an anomaly where a transaction T2 reads a
  state for key k that was written by another transaction, T1, that was not
  T1's final update to k.

  This function takes a history (which should include :fail events!), and
  produces a sequence of error objects, each representing a read of an
  intermediate state."
  [history]
  ; Build a map of keys to maps of intermediate elements to the ops that wrote
  ; them
  (let [im (ct/intermediate-writes #{:append} history)]
    ; Look for ok ops with a read mop of an intermediate append
    (->> history
         h/oks
         ct/op-mops
         (keep (fn [[op [f k v :as mop]]]
                 (when (= :r f)
                   ; We've got an illegal read if our last element came from an
                   ; intermediate append.
                   (when-let [writer (get-in im [k (peek v)])]
                     ; Internal reads are OK!
                     (when (not= op writer)
                       {:op       op
                        :mop      mop
                        :writer   writer
                        :element  (peek v)}))))))))


(def unknown-prefix
  "A marker we use in a list to identify an unknown prefix."
  '...)

(defn op-internal-case
  "Given an op, returns a map describing internal consistency violations, or
  nil otherwise. Our maps are:

      {:op        The operation which went wrong
       :mop       The micro-operation which went wrong
       :expected  The state we expected to observe. Either a definite list
                  like [1 2 3] or a postfix like ['... 3]}"
  [op]
  ; We maintain a map of keys to expected states.
  (->> (:value op)
       (reduce (fn [[state error] [f k v :as mop]]
                 (case f
                   :append [(assoc! state k
                                    (conj (or (get state k [unknown-prefix]) []) v))
                            error]
                   :r      (let [s (get state k)]
                             (if (and s ; We have an expected state
                                      (if (= unknown-prefix (first s))
                                        ; We don't know the prefix.
                                        (let [i (- (inc (count v)) (count s))]
                                          (or (neg? i) ; Bounds check
                                              (not= (subvec s 1) ; Postfix =
                                                    (subvec v i))))
                                        ; We do know the full state for k
                                        (not= s v)))
                               ; Not equal!
                               (reduced [state
                                         {:op       op
                                          :mop      mop
                                          :expected s}])
                               ; OK, or we just don't know
                               [(assoc! state k v) error]))))
               [(transient {}) nil])
       second))

(defn internal-cases
  "Given a history, finds operations which exhibit internal consistency
  violations: e.g. some read [:r k v] in the transaction fails to observe a v
  consistent with that transaction's previous append operations, including
  whatever (initially unknown) state k began with."
  [history]
  (ct/ok-keep op-internal-case history))

(defn prefix?
  "Given two sequences, returns true iff A is a prefix of B."
  [a b]
  (and (<= (count a) (count b))
       (loop [a a
              b b]
         (cond (nil? (seq a))           true
               (= (first a) (first b))  (recur (next a) (next b))
               true                     false))))

(defn values-from-single-appends
  "As a special case of sorted-values, if we have a key which only has a single
  append, we don't need a read: we can infer the sorted values it took on were
  simply [], [x]."
  [history]
  ; Build a map of keys to appended elements.
  (->> history
       (reduce-mops (fn [appends op [f k v]]
                      (cond ; If it's not an append, we don't care
                            (not= :append f) appends

                            ; There's already an append!
                            (contains? appends k)
                            (assoc appends k ::too-many)

                            ; No known appends; record
                            true
                            (assoc appends k v)))
                    {})
       (keep (fn [[k v]]
               (when (not= ::too-many v)
                 [k #{[v]}])))
       (into {})))

(defn sorted-values
  "Takes a history where operation values are transactions, and every micro-op
  in a transaction is an append or a read. Computes a map of keys to all
  distinct observed values for that key, ordered by length.

  As a special case, if we have a key which only has a single append, we don't
  need a read: we can infer the sorted values it took on were simply [], [x]."
  [history]
  (->> history
       ; Build up a map of keys to sets of observed values for those keys
       (reduce (fn [states op]
                 (reduce (fn [states [f k v]]
                           (if (and (= :r f) (seq v))
                             ; Good, this is a read of something other than the
                             ; initial state
                             (-> states
                                 (get k #{})
                                 (conj v)
                                 (->> (assoc states k)))
                             ; Something else!
                             states))
                         states
                         (:value op)))
               {})
       ; If we can't infer anything from reads, see if we can use a single
       ; append operation to infer a value.
       (merge (values-from-single-appends history))
       ; And sort
         (util/map-vals (partial sort-by count))))

(defn incompatible-orders
  "Takes a map of keys to sorted observed values and verifies that for each key
  the values read are consistent with a total order of appends. For instance,
  these values are consistent:

     {:x [[1] [1 2 3]]}

  But these two are not:

     {:x [[1 2] [1 3 2]]}

  ... because the first is not a prefix of the second. Returns a sequence of
  anomaly maps, nil if none are present."
  [sorted-values]
  (let [; For each key, verify the total order.
        errors (keep (fn ok? [[k values]]
                       (->> values
                            ; If a total order exists, we should be able
                            ; to sort their values by size and each one
                            ; will be a prefix of the next.
                            (partition 2 1)
                            (reduce (fn mop [error [a b]]
                                      (when-not (prefix? a b)
                                        (reduced
                                          {:key    k
                                           :values [a b]})))
                                    nil)))
                     sorted-values)]
    (seq errors)))

(defn verify-total-order
  "Takes a map of keys to observed values (e.g. from
  `sorted-values`, and verifies that for each key, the values
  read are consistent with a total order of appends. For instance, these values
  are consistent:

     {:x [[1] [1 2 3]]}

  But these two are not:

     {:x [[1 2] [1 3 2]]}

  ... because the first is not a prefix of the second.

  Returns nil if the history is OK, or throws otherwise."
  [sorted-values]
  (when-let [errors (incompatible-orders sorted-values)]
    (throw+ {:valid?  false
             :type    :no-total-state-order
             :message "observed mutually incompatible orders of appends"
             :errors  errors})))

(defn duplicates
  "Given a history, finds operations which have duplicate copies of the same
  appended element. Since we only append values once, we should never see them
  more than that--and if we do, it could mess up our whole \"total order\"
  thing!"
  [history]
  (->> history
       ct/op-mops
       (keep (fn check-op [[op [f k v :as mop]]]
                 (when (= f :r)
                   (let [dups (->> (frequencies v)
                                   (filter (comp (partial < 1) val))
                                   (into (sorted-map)))]
                     (when (seq dups)
                       {:op         op
                        :mop        mop
                        :duplicates dups})))))
       seq))

(defn merge-orders
  "Takes two potentially incompatible read orders (sequences of elements), and
  computes a total order which is consistent with both of them: where there are
  conflicts, we drop those elements.

  First, we remove duplicates; an order shouldn't have them at all. Yes, this
  means we fail to compute some dependencies.

  In general, the differences between orders fall into some cases:

  1. One empty

      _
      1 2 3 4 5

     We simply pick the non-empty order.

  2. Same first element

     2 x y
     2 z

     Our order is [2] followed by the merged result of [x y] and [z].

  3. Different first elements followed by a common element

     3 y
     2 3

    We drop the smaller element and recur with [3 y] [3]. This isn't... exactly
  symmetric; we prefer longer and higher elements for tail-end conflicts, but I
  think that's still a justifiable choice. After all, we DID read both values,
  and it's sensible to compute a dependency based on any read. Might as well
  pick longer ones.

  Later, we should change the whole structure of append indexes to admit
  multiple prior txns rather than just one, and get rid of this."
  ([as bs]
   (merge-orders [] (distinct as) (distinct bs)))
  ([merged as bs]
   (cond (empty? as) (into merged bs)
         (empty? bs) (into merged as)

         (= (first as) (first bs))
         (recur (conj merged (first as)) (next as) (next bs))

         (< (first as) (first bs)) (recur merged (next as) bs)
         true                      (recur merged as (next bs)))))

(defn append-index
  "Takes a map of keys to observed values (e.g. from sorted-values), and builds
  a bidirectional index: a map of keys to indexes on those keys, where each
  index is a map relating appended values on that key to the order in which
  they were effectively appended by the database.

    {:x {:indices {v0 0, v1 1, v2 2}
         :values  [v0 v1 v2]}}

  We merge all observed orders on a key using merge-orders."
  [sorted-values]
  (util/map-vals (fn [values]
                   ; The last value will be the longest, and since every other
                   ; is a prefix, it includes all the information we need.
                   (let [vs (reduce merge-orders [] values)]
                     {:values  vs
                      :indices (into {} (map vector vs (range)))}))
                 sorted-values))

(defn write-index
  "Takes a history and constructs a map of keys to append values to the
  operations that appended those values."
  [history]
  (reduce (fn [index op]
            (reduce (fn [index [f k v]]
                      (if (= :append f)
                        (assoc-in index [k v] op)
                        index))
                    index
                    (:value op)))
          {}
          history))

(defn dirty-update-cases
  "Takes an append index and a history and searches for instances of dirty
  update. For each key, we use the version order from the append index,
  construct an index mapping appended elements to the transaction which wrote
  them, and look for cases where an aborted transaction is followed by a
  committed one."
  [append-index history]
  (let [write-index (write-index history)]
    (seq
      (mapcat (fn [[k idx]]
                (->> (:values idx)
                     (reduce (fn [[t1 vs cases] v]
                               (assert t1)
                               ; Keep track of the version range
                               (let [vs (conj vs v)
                                     t2 (get (get write-index k) v)]
                                 (assert t2 (str "No transaction wrote "
                                                 (pr-str k) " " (pr-str v)))
                                 (case [(:type t1) (:type t2)]
                                   ; Moving along happily
                                   [:ok    :ok] [t2 [v] cases]
                                   ; We can't say; moving along...
                                   [:info  :ok] [t2 [v] cases]
                                   ; Aha, a dirty write!
                                   [:fail  :ok] [t2 [v]
                                                 (conj cases
                                                       {:key     k
                                                        :values  vs
                                                        :txns    [t1 '... t2]})]

                                   ; We can't say for sure; keep using vs
                                   [:ok    :info] [t1 vs cases]
                                   [:info  :info] [t1 vs cases]
                                   [:fail  :info] [t1 vs cases]

                                   ; Okay, we've got an aborted state now.
                                   [:ok    :fail] [t2 [v] cases]
                                   [:info  :fail] [t2 [v] cases]

                                   ; Huh, in this case we've got a couple
                                   ; options. We could show the tightest bound
                                   ; temporally, or try to cover the range.
                                   ; Tight bounds is how we actually *define*
                                   ; the anomaly, but I think covering is
                                   ; probably more interesting from a "How bad
                                   ; was this" perspective.
                                   [:fail  :fail] [t1 vs cases])))
                             ; The initial state is committed
                             [{:type :ok} [] []])
                     peek))
              append-index))))

(defn read-index
  "Takes a history restricted to oks and infos, and constructs a map of keys to
  append values to the operations which observed the state generated by the
  append of k. The special append value ::init generates the initial (nil)
  state.

  Note that reads of `nil` by :info ops don't result in an entry in this index,
  because those `nil`s denote the default read value, NOT that we actually
  observed `nil`."
  [history]
  (reduce-mops (fn [index op [f k v]]
                 (if (and (= :r f)
                          (not (and (= :info (:type op))
                                    (= :r f)
                                    (= nil v))))
                   (update-in index [k (or (peek v) ::init)] conj op)
                   index))
               {}
               history))

(defn wr-mop-dep
  "What (other) operation wrote the value just before this read mop?"
  [write-index op [f k v]]
  (when (seq v)
    ; It may be the case that a failed operation appended this--that'd be
    ; picked up by the G1a checker.
    (when-let [append-op (-> write-index (get k) (get (peek v)))]
      ; If we wrote this value, there's no external dep here.
      (when-not (= op append-op)
        append-op))))

(defn previously-appended-element
  "Given an append mop, finds the element that was appended immediately prior
  to this append. If we don't know precisely which element was appended
  immediately prior (e.g. we never read this append), we still know it came
  after the highest observed element, so we return that instead.

  Returns ::init if this was, or can only be shown to come after, the first
  append."
  [append-index write-index op [f k v]]
  (if-let [index (get-in append-index [k :indices v])]
    ; What value was appended immediately before us in version order?
    (if (pos? index)
      (get-in append-index [k :values (dec index)])
      ::init)
    ; We don't know what version this append was exactly, because we never
    ; observed it. That still tells us that it came *after* the highest
    ; observed element. If we never observed any appends, it must have come
    ; after the initial state.
    (-> append-index (get k) :values peek (or ::init))))

(defn ww-mop-dep
  "What (other) operation wrote the value just before this write mop?"
  [append-index write-index op [f k v :as mop]]
  (when-let [prev-e (previously-appended-element
                      append-index write-index op mop)]
      ; If we read the initial state, no writer precedes us
      (when (not= ::init prev-e)
        ; What op wrote that value?
        (let [writer (get-in write-index [k prev-e])]
          ; If we wrote it, there's no dependency here
          (when (not= op writer)
            writer)))))

(defn rw-mop-deps
  "The set of (other) operations which read the value just before this write
  mop."
  [append-index write-index read-index op [f k v :as mop]]
  (if-let [prev-e (previously-appended-element
                      append-index write-index op mop)]
    ; Find all ops that read the previous value, except us
    (-> (get-in read-index [k prev-e])
        set
        (disj op))
    ; Dunno what was appended before us
    #{}))

(defn mop-deps
  "A set of dependencies for a mop in an op."
  [append-index write-index read-index op [f :as mop]]
  (case f
    :append (let [deps (rw-mop-deps append-index write-index read-index op mop)
                  deps (if-let [d (ww-mop-dep append-index write-index op mop)]
                         (conj deps d)
                         deps)]
              deps)
    :r      (when-let [d (wr-mop-dep write-index op mop)]
              #{d})))

(defn op-deps
  "All dependencies for an op."
  [append-index write-index read-index op]
  (->> (:value op)
       (map (partial mop-deps append-index write-index read-index op))
       (reduce set/union #{})))

(defn preprocess
  "Before we do any graph computation, we need to preprocess the history,
  making sure it's well-formed. We return a map of:

  {:history       The history restricted to :ok and :info ops
   :append-index  An append index
   :write-index   A write index
   :read-index    A read index}"
  [history]
  (let [; Make sure there are only appends and reads
        vmt (h/task history verify-mop-types-task []
                    (verify-mop-types history))
        ; And that every append is unique
        vua (h/task history verify-unique-appends-task []
                    (verify-unique-appends history))]
    ; These will throw if either finds a problem
    @vmt @vua)

   ; We only care about ok and info ops; invocations don't matter, and failed
   ; ops can't contribute to the state. TODO: do we... want to start inferring
   ; deps for failed ops too? Might simplify the dirty-update codepath.
   (let [history       (h/possible history)
         sorted-values (sorted-values history)]
     ; Compute indices
     (let [append-index (h/task history append-index []
                                (append-index sorted-values))
           write-index  (h/task history write-index []
                                (write-index history))
           read-index   (h/task history read-index []
                                (read-index history))]
       {:history      history
        :append-index @append-index
        :write-index  @write-index
        :read-index   @read-index})))

(defrecord WWExplainer [append-index write-index read-index]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (->> (:value b)
         (keep (fn [[f k v :as b-mop]]
                 (when (= f :append)
                   ; We only care about write-write cycles
                   (when-let [prev-v (previously-appended-element
                                       append-index write-index b b-mop)]
                     ; What op wrote that value?
                     (when-let [dep (ww-mop-dep append-index write-index b b-mop)]
                       (when (= a dep)
                         {:type     :ww
                          :key      k
                          :value    prev-v
                          :value'   v
                          :a-mop-index (index-of (:value a) [:append k prev-v])
                          :b-mop-index (index-of (:value b) b-mop)}))))))
         first))

  (render-explanation [_ {:keys [key value value'] :as m} a-name b-name]
    (str b-name " appended " (pr-str value') " after "
         a-name " appended " (pr-str value)
         " to " (pr-str key))))

(defn ww-graph
  "Analyzes write-write dependencies."
  ([history]
   (ww-graph (preprocess history) nil))
  ([{:keys [history append-index write-index read-index]} _]
   {:graph (g/forked
             (reduce-mops (fn [g op [f :as mop]]
                            ; Only appends have dependencies, cuz we're
                            ; interested in ww cycles.
                            (if (not= f :append)
                              g
                              (if-let [dep (ww-mop-dep
                                             append-index write-index op mop)]
                                (g/link g dep op)
                                g)))
                          (g/linear (g/named-graph :ww))
                          history))
    :explainer (WWExplainer. append-index write-index read-index)}))

(defrecord WRExplainer [append-index write-index read-index]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (->> (:value b)
         (keep (fn [[f k v :as mop]]
                 (when (= f :r)
                   (when-let [writer (wr-mop-dep write-index b mop)]
                     (when (= writer a)
                       {:type  :wr
                        :key   k
                        :value (peek v)
                        :a-mop-index (index-of (:value a) [:append k (peek v)])
                        :b-mop-index (index-of (:value b) mop)})))))
         first))

  (render-explanation [_ {:keys [key value]} a-name b-name]
    (str b-name " observed " a-name
         "'s append of " (pr-str value)
         " to key " (pr-str key))))

(defn wr-graph
  "Analyzes write-read dependencies."
  ([history]
   (wr-graph (preprocess history) nil))
  ([{:keys [history append-index write-index read-index]} _]
   {:graph (g/forked
             (reduce-mops (fn [g op [f :as mop]]
                            (if (not= f :r)
                              g
                              ; Figure out what write we overwrote
                              (if-let [dep (wr-mop-dep write-index op mop)]
                                (g/link g dep op)
                                ; No dep
                                g)))
                          (g/linear (g/named-graph :wr))
                          history))
    :explainer (WRExplainer. append-index write-index read-index)}))

(defrecord RWExplainer [append-index write-index read-index]
  elle/DataExplainer
  (explain-pair-data [_ a b]
    (->> (:value b)
         (keep-indexed (fn [i [f k v :as mop]]
                 (when (= f :append)
                   (when-let [readers (rw-mop-deps append-index write-index
                                                   read-index b mop)]
                     (when (some #{a} readers)
                       (let [prev-v (previously-appended-element
                                      append-index write-index b mop)]
                         {:type   :rw
                          :key    k
                          :value  prev-v
                          :value' v
                          :a-mop-index
                          (->> (:value a)
                               (keep-indexed
                                 (fn [i [f mk vs]]
                                   (when (and (= f :r)
                                              (= mk k)
                                              (if (= ::init prev-v)
                                                (= 0 (count vs))
                                                (= (peek vs) prev-v)))
                                     i)))
                                            first)
                          :b-mop-index i}))))))
         first))

  (render-explanation [_ {:keys [key value value']} a-name b-name]
    (if (= ::init value)
      (str a-name
           " observed the initial (nil) state of "
           (pr-str key) ", which " b-name
           " created by appending " (pr-str value'))
      (str a-name " did not observe "
           b-name "'s append of " (pr-str value')
           " to " (pr-str key)))))

(defn rw-graph
  "Analyzes read-write anti-dependencies."
  ([history]
   (rw-graph (preprocess history) nil))
  ([{:keys [history append-index write-index read-index]} _]
   {:graph (loopr [; Yourkit claims we were burning time in NamedGraph/link, so
                   ; we'll fall back to the concrete digraph then wrap.
                   ; Maybe inliner got confused.
                   g (g/linear (g/digraph))]
                  [op           history
                   [f :as mop]  op]
                  (if (identical? f :append)
                    ; Who read the state just before we wrote?
                    (if-let [deps (rw-mop-deps append-index
                                               write-index
                                               read-index op mop)]
                      (recur (g/link-all-to g deps op))
                      (recur g))
                    (recur g))
                  (g/named-graph :rw (g/forked g)))
    :explainer (RWExplainer. append-index write-index read-index)}))

(defn graph
  "Some parts of a transaction's dependency graph--for instance,
  anti-dependency cycles--involve the *version order* of states for a key.
  Given two transactions: [[:w :x 1]] and [[:w :x 2]], we can't tell whether T1
  or T2 happened first. This makes it hard to identify read-write and
  write-write edges, because we can't tell what particular transaction should
  have overwritten the state observed by a previous transaction.

  However, if we constrain ourselves to transactions whose only mutation is to
  *append* a value to a key's current state...

    {:f :txn, :value [[:r :x [1 2]] [:append :x 3] [:r :x [1 2 3]]]} ...

  ... we can derive the version order for (almost) any pair of operations on
  the same key because the order of appends is encoded in every read: if we
  observe [:r :x [3 1 2]], we know the previous states must have been [3] [3 1]
  [3 1 2].

  That is, assuming appends actually work correctly. If the database loses
  appends or reorders them, it's *likely* (but not necessarily the case), that
  we'll observe states like:

    [1 2 3]
    [1 3 4]  ; 2 has been lost!

  We can verify these in a single O(appends^2) pass by sorting all observed
  states for a key by size, and verifying that each is a prefix of the next.
  Assuming we *do* observe a total order, we can use the longest read value for
  each key as an order over appends for that key. This order is *almost*
  complete in that appends which are never read can't be related, but so long
  as the DB lets us see most of our appends at least once, this should work.

  So then, our strategy here is to compute those orders for each key, then use
  them to relate successive [w w], [r w], and [w r] pair on that key. [w,w]
  pairs are a direct write dependency, [w,r] pairs are a direct
  read-dependency, and [r,w] pairs are direct anti-dependencies.

  For more context, see Adya, Liskov, and O'Neil's 'Generalized Isolation Level
  Definitions', page 8."
  [history]
  ; We need these auxiliary structures for each subgraph; might as well do the
  ; work just once.
  (let [preprocessed (preprocess history)]
    ((elle/combine (partial ww-graph preprocessed)
                   (partial wr-graph preprocessed)
                   (partial rw-graph preprocessed))
     history)))

(defn rand-bg-color
  "Hashes anything and assigns a lightish hex color to it--helpful for
  highlighting different values differently."
  [x]
  (let [h (hash x)
        ; Break up hash into 3 8-bit chunks
        r (bit-and 255 h)
        g (-> h (bit-and 65280)    (bit-shift-right 8))
        b (-> h (bit-and 16711680) (bit-shift-right 16))
        ; Squeeze these values into the range 130-250, so they're not too dark
        ; to read, but not pure white (which would disappear).
        ceil     250
        floor    130
        range    (- ceil floor)
        compress (fn compress [x]
                   (-> x (/ 255) (* range) (+ floor) short))
        r (compress r)
        g (compress g)
        b (compress b)]
    (str "#"
         (format "%02x" r)
         (format "%02x" g)
         (format "%02x" b))))

(defn incompatible-order-viz
  "Takes a key, a vector of the longest value of that key, and a seq of ok
  operations which interacted with that key. Constructs a Hiccup structure with
  a visualization for that key."
  [key longest ops]
  [:html
   [:head
    [:style "th { text-align: left; }"]]
   [:body
    [:h1 (str "All Reads of " key)]
    [:table
     [:thead
      [:tr
       [:th "Index"]
       [:th "Time (s)"]
       [:th "Process"]
       [:th "Fun"]
       [:th {:colspan 32} "Value"]]]
     [:tbody
      (for [{:keys [index time process f value]} ops
            [mop-f k v] value
            :when (and (= k key) (= mop-f :r))]
        [:tr
         (concat [[:td index]
                  [:td (when time
                         (format "%.2f" (nanos->secs time)))]
                  [:td process]
                  [:td (when f (name f))]]
                 (->> v
                      ; Stitch together values with indexes so we can compare
                      ; for compatibility
                      (map-indexed vector)
                      (keep (fn [[i elem]]
                              (let [compat? (= elem (nth longest i))
                                    attrs (if compat?
                                            {}
                                            {:style (str "background: "
                                                         (rand-bg-color elem))})]
                                [:td attrs elem])))))])]]]])

(defn render-incompatible-orders!
  "Takes a directory, history, a sorted-values map, and a map of keys to
  incompatible orders. For each incompatible-order anomaly, renders an HTML
  file in elle/incompatible-orders/ showing all the reads of that key, and
  where they were incompatible with the longest value."
  [directory history sorted-values incompatible-orders]
  (let [; What keys are we interested in?
        ks (->> incompatible-orders
                (map :key)
                set)
        ; Find ops that might be relevant, and group them by key.
        ops (reduce (fn [by-k {:keys [type value] :as op}]
                      (if (= type :ok)
                        ; Find what keys we intersected with
                        (->> value
                             (filter (comp #{:r} first))
                             (map second)
                             set
                             (set/intersection ks)
                             ; And add this op to the list of ops for each
                             ; relevant key
                             (reduce (fn add-to-ks [by-k k]
                                       (let [ops (get by-k k [])]
                                         (assoc by-k k (conj ops op))))
                                     by-k))
                        ; Not an OK op
                        by-k))
                    {}
                    history)]
    (doseq [k ks]
      (let [; What's our longest version of k?
            longest (->> (get sorted-values k)
                         last)
            ; Where are we writing?
            path (io/file directory "incompatible-order" (str (pr-str k)
                                                              ".html"))
            _ (io/make-parents path)]
        (spit path
              (hiccup/html (incompatible-order-viz k longest (get ops k))))))))

(defn check
  "Full checker for append and read histories. Options are:

    :consistency-models     A collection of consistency models we expect this
                            history to obey. Defaults to [:strict-serializable].
                            See elle.consistency-model for available models.

    :anomalies              You can also specify a collection of specific
                            anomalies you'd like to look for. Performs limited
                            expansion as per
                            elle.consistency-model/implied-anomalies.

    :additional-graphs      A collection of graph analyzers (e.g. realtime)
                            which should be merged with our own dependencies.

    :cycle-search-timeout   How many milliseconds are we willing to search a
                            single SCC for a cycle?

    :directory              Where to output files, if desired. (default nil)

    :plot-format            Either :png or :svg (default :svg)

    :plot-timeout           How many milliseconds will we wait to render a SCC
                            plot?

    :max-plot-bytes         Maximum size of a cycle graph (in bytes of DOT)
                            which we're willing to try and render.
  "
  ([history]
   (check {} history))
  ([opts history]
   (let [history      (h/client-ops history)
         g1a          (h/task history g1a [] (g1a-cases history))
         g1b          (h/task history g1b [] (g1b-cases history))
         internal     (h/task history internal [] (internal-cases history))
         dirty-update (h/task history dirty-update []
                              (dirty-update-cases
                                (append-index (sorted-values history))
                                history))

         ; We don't want to detect duplicates or incompatible orders for
         ; aborted txns.
         history+      (h/possible history)
         dups          (h/task history dups [] (duplicates history+))
         sorted-values (h/task history sorted-values+ []
                               (sorted-values history+))
         incmp-order   (h/task history incmp-order [sv sorted-values]
                               (incompatible-orders sv))
         _             (h/task history render-incmp-order [sv    sorted-values
                                                           incmp incmp-order]
                               (render-incompatible-orders!
                                 (:directory opts) history+ sv incmp))
         lost-update   (h/task history lost-update []
                               (ct/lost-update-cases #{:append} history+))

         ; Great, now construct a graph analyzer...
         analyzers     (into [graph] (ct/additional-graphs opts))
         analyzer      (apply elle/combine analyzers)
         cycles        (:anomalies (ct/cycles! opts analyzer history))

         ; And merge in our own anomalies
         anomalies (cond-> cycles
                     @dups          (assoc :duplicate-elements @dups)
                     @incmp-order   (assoc :incompatible-order @incmp-order)
                     @internal      (assoc :internal @internal)
                     @dirty-update  (assoc :dirty-update @dirty-update)
                     (seq @g1a)     (assoc :G1a @g1a)
                     (seq @g1b)     (assoc :G1b @g1b)
                     @lost-update   (assoc :lost-update @lost-update))]
     (ct/result-map opts anomalies))))

(defn append-txns
  "Like wr-txns, we just rewrite writes to be appends."
  [opts]
  (->> (ct/wr-txns opts)
       (map (partial mapv (fn [[f k v]] [(case f :w :append f) k v])))))

(defn gen
	"A generator for operations where values are transactions made up of reads
  and appends to various integer keys. Takes options:

    :key-count            Number of distinct keys at any point
    :min-txn-length       Minimum number of operations per txn
    :max-txn-length       Maximum number of operations per txn
    :max-writes-per-key   Maximum number of operations per key

 For defaults, see wr-txns."
  ([]
   (gen {}))
  ([opts]
   (ct/gen (append-txns opts))))
