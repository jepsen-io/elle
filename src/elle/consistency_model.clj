(ns elle.consistency-model
  "Elle finds anomalies in histories. This namespace helps turn those
  anomalies into claims about what kind of consistency models are supported
  by, or ruled out by, a given history. For sources, see

  - Adya, 'Weak Consistency'

  - Adya, Liskov, O'Neil, 'Generalized Isolation Level Definitions'

  - Adya, Liskov, O'Neil, 'Towards an Isolation Level Standard' (https://pdfs.semanticscholar.org/1bbf/5189299b71502b500ef9717dc47d930d080a.pdf)

  - Bailis, Davidson, Fekete, et al, 'Highly Available Transactions'

  - Cerone, Bernardi, Gotsman, 'A Framework for Transactional Consistency Models with Atomic Visibility'

  - Fekete, Liarokapis, O'Neil, O'Neil, 'Making Snapshot Isolation Serializable'

  - Cerone-SI: Cerone, Gotsman, 'Analysing Snapshot Isolation' (http://software.imdea.org/~gotsman/papers/si-podc16.pdf)

  - Daudjee, Salem, 'Lazy Database Replication with Ordering Guarantees' (https://cs.uwaterloo.ca/~kmsalem/pubs/DaudjeeICDE04.pdf)

  - Daudjee-SI: Daudjee, Salem, 'Lazy Database Replication with Snapshot Isolation' (http://www.vldb.org/conf/2006/p715-daudjee.pdf)

  - Bernstein, Hazilacos, Goodman, 'Concurrency Control and Recovery in Database Systems' (https://www.microsoft.com/en-us/research/people/philbe/)

  - Hermitage: Kleppmann, 'Hermitage' (https://github.com/ept/hermitage)

  - Zuikeviciute, Pedone, 'Correctness Criteria for Database Replication' (https://www.researchgate.net/profile/Fernando_Pedone/publication/225706071_Correctness_Criteria_for_Database_Replication_Theoretical_and_Practical_Aspects/links/00b7d53274a4c89278000000/Correctness-Criteria-for-Database-Replication-Theoretical-and-Practical-Aspects.pdf)

  - Liu, Ölveczky, et al, 'ROLA: A New Distributed Transaction Protocol and Its Formal Analysis'

  - Cahill, 'Serializable Isolation for Snapshot Databases' (http://hdl.handle.net/2123/5353)

  - Elnikety, Pedone, Zwaenepoel, 'Generalized Snapshot Isolation and a Prefix-Consistent Implementation' (https://www.inf.usi.ch/faculty/pedone/Paper/2004/IC_TECH_REPORT_200421.pdf)

  ## Choices

  -  When we say 'serializability', we follow Bernstein et al in meaning
  'conflict serializability'.

  - Our snapshot isolation mixes (perhaps incorrectly) a variety of
  formalizations."
  (:require [bifurcan-clj [graph :as bg]]
            [elle [graph :as g]
                  [util :as util :refer [map-vals]]]
            [clojure [set :as set]
                     [pprint :refer [pprint]]]
            [clojure.tools.logging :refer [info warn]]
            [dom-top.core :refer [assert+]]
            [rhizome [dot :refer [graph->dot]]
                      [viz :as rv]])
  (:import (java.util.function Function)
           (io.lacuna.bifurcan Graphs)))

(def implied-anomalies
  "We have lots of different types of anomalies. Some of them imply others--for
  example, when we detect an :internal anomaly, that's *also* a sign of G1a:
  aborted reads. If G1a is present, so is G1, because G1 is defined as the
  union of G1a, G1b, and G1c."
  (g/map->dag
    {:G0          [:G1c ; Adya
                   :G0-process] ; G0 is a trivial G0-process
     ; Since processes are singlethreaded
     :G0-process  [:G1c-process :G0-realtime]
     :G0-realtime [:G1c-realtime]

     ; G1 is defined in terms of these three anomalies.
     :G1a [:G1]
     :G1b [:G1]
     :G1c [:G1           ; Adya
           :G1c-process] ; G1c is a trivial G1c-process]

     ; Since processes are singlethreaded
     :G1c-process  [:G1c-realtime :G1-process]
     :G1c-realtime [:G1-realtime]
     :G1           [:G1-process] ; Trivial
     :G1-process   [:G1-realtime]

     ; G-single-item is a special case of G-single, G-nonadjacent-item
     :G-single-item          [:G-single
                              :G-single-item-process
                              :G-nonadjacent-item]
     :G-single-item-process  [:G-single-process
                              :G-single-item-realtime
                              :G-nonadjacent-item-process]
     :G-single-item-realtime [:G-single-realtime
                              :G-nonadjacent-item-realtime]

     ; G-single is a special case of G-nonadjacent
     :G-single          [:G-nonadjacent
                         ; Adya; if there's a cycle with one rw edge in DSG,
                         ; must be one in SSG as well. Not sure about
                         ; process/RT variants of this.
                         :GSIb
                         :G-single-process] ; Trivial
     :G-single-process  [:G-nonadjacent-process :G-single-realtime]
     :G-single-realtime [:G-nonadjacent-realtime]

     ; G-nonadjacent-item is a special case of G-nonadjacent restricted to item
     ; rw edges, which means it's also G2-item.
     :G-nonadjacent-item          [:G-nonadjacent
                                   :G2-item
                                   :G-nonadjacent-item-process]
     :G-nonadjacent-item-process  [:G-nonadjacent-process
                                   :G2-item-process
                                   :G-nonadjacent-item-realtime]
     :G-nonadjacent-item-realtime [:G2-item-realtime
                                   :G-nonadjacent-realtime]

     ; G-nonadjacent is a special kind of G2 where rw edges alternate
     :G-nonadjacent           [:G2                     ; Adya
                               :G-nonadjacent-process] ; Trivial
     :G-nonadjacent-process   [:G2-process :G-nonadjacent-realtime]
     :G-nonadjacent-realtime  [:G2-realtime]

     :G2                [:G2-process]      ; Trivial
     :G2-item           [:G2               ; Adya
                         :G2-item-process] ; Trivially
     :G2-item-process   [:G2-process :G2-item-realtime]
     :G2-item-realtime  [:G2-realtime]

     ; TODO: we don't distinguish between G-single which applies to items, vs
     ; G-single on predicates. Right now, our G-singles ARE G2-item, but that's
     ; not necessarily always going to be the case. This means checkers which
     ; look for repeatable read are going to miss G-single, because they want
     ; to see G2-item, but we filter out G-singles from G2 results. What a
     ; mess. Fix this... in elle.txn, not here.

     ; If we see a process violation, we also have a realtime violation,
     ; because processes are single-threaded.
     :G2-process        [:G2-realtime]

     ; SI properties, per Adya
     :GSIa [:GSI]
     :GSIb [:GSI]

     ; The list-append test can find an anomaly which we call
     ; incompatible-order, where two committed read versions couldn't have come
     ; from the same timeline. This implies a dirty read.
     :incompatible-order [:G1a]

     ; Our dependency graphs never contain self-edges. However, a future read
     ; is essentially a trivial cycle in which T1 -wr-> T1. The degenerate case
     ; is that it externally reads one of its own external effects. It's also
     ; possible to perform an internal read which observes internal writes from
     ; later in the transaction. Both of these are essentially G1c.
     :future-read [:G1c]

     ; Because we work in a richer data model than Adya, we have an extra class
     ; of anomaly that Adya doesn't: a dirty update. Dirty update is basically
     ; like a dirty read, except it affects writes as well. We say it implies a
     ; G1a anomaly, because it's likely that any model which prohibits G1a
     ; would want to prohibit dirty updates as well.
     :dirty-update [:G1a]

     ; Lost update is a special case of write skew, per Bailis, and since it
     ; involves a single record by primary key, rather than a predicate, it is
     ; also G2-item.
     :lost-update [:write-skew :G2-item]
     ; And write skew is a special case of G2, per Hermitage
     :write-skew  [:G2]}))

(def anomaly-severity-graph
  "G0 doesn't imply G-Single, but G0 is usually \"worse\" than G-Single. This
  graph encodes that extra severity information. We use this to order anomalies
  by severity, which aids us in searching for the worst anomalies first."
  (g/map->dag
    {:G0           [:G1c]
     :G0-process   [:G1c-process]
     :G0-realtime  [:G1c-realtime]
     :G1c          [:G-single :G2-item]
     :G1c-process  [:G-single-process :G2-item-process]
     :G1c-realtime [:G-single-realtime :G2-item-realtime]
     ; Process anomalies are not as bad as pure data violations
     :G2           [:G0-process]
     ; And we only start caring about realtime once we've exhausted the most
     ; subtle process anomaly
     :G2-process   [:G0-realtime]}))

(defn all-anomalies-implying
  "Takes a collection of anomalies, and yields a set of anomalies which would
  imply any of those anomalies."
  [anomalies]
  (when (seq anomalies)
    (set (g/bfs (partial g/in implied-anomalies) anomalies))))

(defn all-implied-anomalies
  "Takes a collection of anomalies, and yields a set of anomalies implied by
  those."
  [anomalies]
  (when (seq anomalies)
    (set (g/bfs (partial g/out implied-anomalies) anomalies))))

(def canonical-model-names
  "Lots of models have different names, and I can't keep them all straight.
  This structure maps friendly names to canonical ones."
  {
   :consistent-view          :PL-2+    ; Adya
   :conflict-serializable    :PL-3     ; Adya
   :cursor-stability         :PL-CS    ; Adya
   :forward-consistent-view  :PL-FCV   ; Adya
   :monotonic-snapshot-read  :PL-MSR   ; Adya
   :monotonic-view           :PL-2L    ; Adya
   :read-committed           :PL-2     ; I thiiiink Adya means this, but I'm not
                                       ; sure
   :read-uncommitted         :PL-1     ; Ditto, I'm guessing here. This might
                                       ; be a matter of interpretation.
   :repeatable-read          :PL-2.99  ; Adya
   ; We use "serializable" to mean "conflict serializable"
   :serializable             :PL-3
   :snapshot-isolation       :PL-SI    ; Adya
   ; TODO: What do we want to do about "1SR" and "strong serializable"? Are they
   ; equivalent to strict serializable?
   ;
   ; Bernstein introduces the concept of strict-1SR, but the entire point is
   ; that it's indistinguishible (for users) from (conflict) serializability.
   ; OTOH, they also say "As we have seen, another explanation why a
   ; serializable execution may not be 1SR is that different transactions
   ; observe failures and recoveries in different orders", which implies SR is
   ; weaker than 1SR. Is there an implication here? Is it visible to users?
   ; :strict-1SR               :serializable
   :strict-serializable      :PL-SS    ; Adya
   ; Right, I'm calling this: strong and strict serializable are the same thing.
   :strong-serializable      :PL-SS
   :update-serializable      :PL-3U    ; Adya
   :strong-session-read-uncommitted :strong-session-PL-1
   :strong-session-read-committed   :strong-session-PL-2
   :strong-read-uncommitted         :strong-PL-1
   :strong-read-committed           :strong-PL-2
   })

(def friendly-model-names
  "Maps canonical model names to friendly ones."
  (assoc (->> canonical-model-names
              (map (juxt val key))
              (into {}))
         ; There are multiple options here, and serializable seems
         ; simplest.
         :PL-3 :serializable))

(defn canonical-model-name
  "Returns the canonical name of a consistency model."
  [model]
  (get canonical-model-names model model))

(defn friendly-model-name
  "Returns the friendly name of a consistency model."
  [model]
  (get friendly-model-names model model))

(def models
  "This graph relates consistency models in a hierarchy, such that if a->b in
  the graph, a history which satisfies model a also satisfies model b. See
  https://jepsen.io/consistency for sources."
  (->> ; Transactional models
       {
        ; Might merge this into normal causal later? I'm not sure
        ; how to unify them exactly.
        :causal-cerone          [:read-atomic]                ; Cerone
        :consistent-view        [:cursor-stability            ; Adya
                                 :monotonic-view]             ; Adya
        :conflict-serializable  [:view-serializable]
        :cursor-stability       [:read-committed              ; Bailis
                                 :PL-2]                       ; Adya
        :forward-consistent-view [:consistent-view]           ; Adya
        :PL-2                    [:PL-1]                      ; Adya
        :PL-3                   [:repeatable-read             ; Adya
                                 :update-serializable         ; Adya
                                 ; We define PL-3 *as* conflict serializable
                                 ;:conflict-serializable]      ; Adya
                                 ]
        :update-serializable    [:forward-consistent-view]    ; Adya
        :monotonic-atomic-view  [:read-committed]             ; Bailis
        :monotonic-view         [:PL-2]                       ; Adya
        :monotonic-snapshot-read [:PL-2]                      ; Adya
        :parallel-snapshot-isolation [:causal-cerone          ; Cerone
                                      :update-atomic]         ; ROLA (which actually provides UA)
        :prefix                 [:causal-cerone]              ; Cerone
        :read-atomic            [; EXT guarantees atomic visibility, and
                                 ; monotonicity within the txn is trivially
                                 ; satisfied by INT
                                 :monotonic-atomic-view]      ; Cerone
        :read-committed         [:read-uncommitted]           ; SQL
        :repeatable-read        [:cursor-stability            ; Adya
                                 :monotonic-atomic-view]      ; Bailis
        :update-atomic          [:read-atomic]                ; Cerone
        :serializable           [:repeatable-read             ; SQL
                                 :snapshot-isolation          ; Bailis, Cerone
                                 :view-serializable]          ; Bernstein
        :session-serializable   [:1SR]                        ; Zuikeviciute
        :snapshot-isolation     [:forward-consistent-view     ; Adya
                                 :monotonic-atomic-view       ; Bailis
                                 :monotonic-snapshot-read     ; Adya
                                 :parallel-snapshot-isolation ; Cerone
                                 :prefix]                     ; Cerone
        :strict-serializable    [:PL-3                        ; Adya
                                 :serializable                ; Bailis
                                 :linearizable                ; Bailis
                                 :snapshot-isolation          ; Adya
                                 ; It's hard to imagine how this could *not* be
                                 ; the case, but I don't have a citation here
                                 ; either.
                                 :strong-snapshot-isolation
                                 :strong-session-serializable]; Daudjee???

        ; These models aren't in the literature to my knowledge, but they're
        ; intuitive generalizations of the SI/serializable models, and they
        ; help us rule out quite a few cycle searches.
        :strong-session-PL-1 [:PL-1]
        :strong-session-PL-2 [:PL-2 :strong-session-PL-1]
        :strong-PL-1 [:strong-session-PL-1]
        :strong-PL-2 [:strong-session-PL-2 :strong-PL-1]

        :strong-session-serializable
        [:serializable                        ; Daudjee
         :strong-session-snapshot-isolation]  ; Obviously!

        ; TODO: Fekete et al suggests there's a concurrency restriction for
        ; SI-but-nonserializable anomalies here: https://www.cse.iitb.ac.in/infolab/Data/Courses/CS632/2009/Papers/p492-fekete.pdf, but I don't fully understand
        ; their formalism.

        ; Daudjee-SI, Cerone-SI
        :strong-session-snapshot-isolation [:snapshot-isolation
                                            :strong-session-PL-2]

        ; TODO: does strong mean PL-SS?
        ; TODO: What about strict-1SR? Zuikeviciute's informal definitions
        ; make it sound like these are all PL-SS, but I'm not SURE
        :strong-serializable    [:session-serializable]       ; Zuikeviciute
        ; Daudjee-SI
        :strong-snapshot-isolation [:strong-session-snapshot-isolation
                                    :strong-PL-2]

        ; Single-object (ish) models
        :linearizable          [:sequential]                 ; Bailis
        :sequential            [:causal]                     ; Bailis
        :causal                [:writes-follow-reads         ; Bailis
                                :PRAM]                       ; Bailis

        :PRAM                  [:monotonic-reads             ; Bailis
                                :monotonic-writes            ; Bailis
                                :read-your-writes]}          ; Bailis
       g/map->dag
       (g/map-vertices canonical-model-name)))

(def all-models
  "A set of all models."
  (into (sorted-set)
        (concat (bg/vertices models)
                (keys canonical-model-names)
                (vals canonical-model-names))))

(defn validate-models
  "Takes a collection of models and returns it, unless some of those models
  aren't known, in which case, throws an IllegalArgumentException."
  [ms]
  (let [unknown (remove all-models ms)]
    (assert+ (empty? unknown)
             (str "Unknown consistency model " (pr-str unknown)
                  "; known models are:\n" all-models))
    ms))

(defn all-implied-models
  "Takes a set of models, and expands it, using `models`, to a set of all
  models which are implied by any of those models."
  [ms]
  (g/bfs (partial g/out models)
         (map canonical-model-name (validate-models ms))))

(defn all-impossible-models
  "Takes a set of models which are impossible, and expands it, using `models`,
  to a set of all models which are also impossible."
  [impossible]
  (g/bfs (partial g/in models)
         (map canonical-model-name (validate-models impossible))))

(defn most-models
  "Given a set of models, and a direction function (g/in or g/out), gives a
  subset of models which imply/are implied by the other models in the set.
  Canonicalizes model names."
  [dir ms]
  ; The graph's not that big. We just brute-force this by searching the full
  ; downstream set. It's not minimal, but it should be good enough.
  (let [ms (map canonical-model-name ms)]
    (reduce (fn [ms model]
              (let [ms' (disj ms model)]
                (if (some ms' (g/bfs (partial dir models) [model]))
                  ; Some other model covers this one.
                  ms'
                  ms)))
            (set ms)
            ms)))

(defn strongest-models
  "Given a set of models, returns a (hopefully smaller) subset of those models
  which implies all the rest. For instance, (strongest-models
  #{:strict-serializable :serializable}) => #{:strict-serializable}."
  [ms]
  (most-models g/in ms))

(defn weakest-models
  "Given a set of models, returns a (hopefully smaller) subset of those models
  which are implied by all the rest. For instance, (weakest-models
  #{:strict-serializable :serializable}) => #{:serializable}."
  [ms]
  (most-models g/out ms))

(def direct-proscribed-anomalies
  "A graph which relates (canonical) consistency models to the anomalies they
  directly proscribe.

  We don't always specify the *full* set of prohibited anomalies for each
  model, just the ones they add over weaker, implied models. This data
  structure is intended to be used in conjunction with `models` and
  `anomaly-graph`."
  (->> {
        :causal-cerone             [:internal :G1a]    ; Cerone (incomplete)
        :cursor-stability          [:G1 :G-cursor      ; Adya
                                    :lost-update]      ; Adya, Bailis
        :monotonic-view            [:G1 :G-monotonic]  ; Adya
        :monotonic-snapshot-read   [:G1 :G-MSR]        ; Adya
        :consistent-view           [:G1 :G-single]     ; Adya
        :forward-consistent-view   [:G1 :G-SIb]        ; Adya
        :parallel-snapshot-isolation [:internal :G1a]  ; Cerone (incomplete)
        :PL-3                      [:G1 :G2            ; Adya
                                    ; We say a "predicate read miss" occurs
                                    ; when a predicate read fails to observe a
                                    ; version when *every* version in the
                                    ; history matches the predicate.
                                    :predicate-read-miss
                                    :PL-3-cycle-exists]
        :PL-2                      [:G1                ; Adya
                                    :PL-2-cycle-exists]
        :PL-1                      [:G0                ; Adya
                                    ; I don't think an Adya history can exist
                                    ; with either of these. We might want to
                                    ; include these in other, non-Adya models
                                    ; too, but I don't understand their
                                    ; formalisms well enough to say for sure.
                                    :duplicate-elements
                                    ; Version orders are supposed to be total
                                    :cyclic-versions
                                    :PL-1-cycle-exists]
        :prefix                    [:internal :G1a     ; Cerone (incomplete)
                                    ; :prefix-cycle-exists ; Not yet ready
                                    ]
        :serializable              [:internal]         ; Cerone (incomplete)
        :snapshot-isolation        [:internal          ; Cerone (incomplete)
                                    :G1                ; Adya
                                    :G-SI              ; Adya
                                    ; Daudjee-SI: "If a distinct label is
                                    ; assigned to every transaction, strong
                                    ; session SI is equivalent to weak SI".
                                    ; Weak SI, in this context, means
                                    ; generalized SI, which is what we use for
                                    ; SI. I feel like this is *very* close to
                                    ; sugesting G-nonadjacent is forbidden by
                                    ; SI, but I'm not quite sure.
                                    ;
                                    ; Cerone-SI also states *strong session* SI
                                    ; forbids nonadjacent rw edges.
                                    ;
                                    ; Chatting with Alexey Gotsman about this
                                    ; confirms my suspicion: generalized SI
                                    ; forbids *any* history where all rw edges
                                    ; are nonadjacent, not just G-single.
                                    :G-nonadjacent
                                    :PL-SI-cycle-exists
                                    ]
        :read-atomic               [:internal          ; Cerone (incomplete)
                                    :G1a               ; Cerone (incomplete)
                                    ; Future read implies a violation of EXT,
                                    ; because a read observed a value that was
                                    ; written by the same transaction later,
                                    ; which means it did *not* observe the
                                    ; value from the previous txn in the
                                    ; visibility order.
                                    :future-read]       ; Cerone (incomplete)
        :repeatable-read           [:G1 :G2-item       ; Adya
                                    :PL-2.99-cycle-exists
                                    :lost-update]      ; Bailis
        :update-atomic             [:lost-update]      ; Cerone
        :strict-serializable       [:G1                ; Adya
                                    :G1c-realtime      ; Adya
                                    :G2-realtime       ; Adya
                                    :PL-SS-cycle-exists]
        :strong-session-PL-1       [:strong-session-PL-1-cycle-exists
                                    :G0-process]
        :strong-session-PL-2       [:strong-session-PL-2-cycle-exists
                                    :G1c-process]
        :strong-PL-1               [:strong-PL-1-cycle-exists
                                    :G0-realtime]
        :strong-PL-2               [:strong-PL-2-cycle-exists
                                    :G1c-realtime]
        ; I *don't* have a source for these officially, because the use of
        ; G-nonadjacent isn't well canonicalized in the literature, but it
        ; seems obvious that strong session SI should prevent you from failing
        ; to read your own *previous* writes (G-single-process), and strong SI
        ; should prevent you from failing to read *any* completed writes
        ; (G-single-realtime), and since we actually formalize this in SI as
        ; G-nonadjacent rather than just G-single, I'm going to include
        ; G-nonadjacent's realtime and process variants here too.
        :strong-session-snapshot-isolation
        [:internal
         :G1-process
         :G-nonadjacent-process
         :strong-session-snapshot-isolation-cycle-exists]
        :strong-snapshot-isolation
        [:internal
         :G1-realtime
         :G-nonadjacent-realtime
         :strong-snapshot-isolation-cycle-exists]
        :strong-session-serializable
        [:G1-process      ; Daudjee
         :G2-process      ; Daudjee
         :strong-session-serializable-cycle-exists] ; Alvaro (unpub)
        :update-serializable       [:G1 :G-update]     ; Adya
        }
       (map (fn [[k v]] [(canonical-model-name k) v]))
       g/map->dag))

(def anomaly-depths
  "A map of anomaly names to their depth in the anomaly dependency tree. Depth
  0 are anomalies which aren't implied by any other. You can sort by this depth
  to perform a topological traversal of anomalies."
  (merge-with max
              (g/topo-depths (bg/merge implied-anomalies
                                       anomaly-severity-graph
                                       (constantly nil)))
              ; Basically treating the graph as a map and getting
              ; vals out
              (zipmap (->> direct-proscribed-anomalies
                           bg/top
                           (mapcat (partial g/out
                                            direct-proscribed-anomalies)))
                      (repeat 0))))

(defn anomaly-depth-compare
  "Takes two anomalies and compares them by depth, fewer deps first."
  [a b]
  (let [d (compare (get anomaly-depths a)
                   (get anomaly-depths b))]
    (if (= 0 d)
      (if (= a b)
        0
        (compare a b))
      d)))

(def all-anomalies
  "A set of all known anomalies. Sorted by depth."
  (into (sorted-set-by anomaly-depth-compare)
        (keys anomaly-depths)))

(defn anomalies-prohibited-by
  "Takes a collection of consistency models, and returns a set of anomalies
  which can't be present if all of those models are to hold."
  [models]
  (->> ; Canonicalize models
       (map canonical-model-name models)
       ; Take every model implied by those
       all-implied-models
       ; And expand those to proscribed anomalies...
       (mapcat (comp g/->clj (partial g/out direct-proscribed-anomalies)))
       ; And any anomalies which would imply those anomalies.
       all-anomalies-implying
       (into (sorted-set))))

(defn anomalies->impossible-models
  "Takes a collection of anomalies, and returns a set of models which can't
  hold, given those anomalies are present."
  [anomalies]
  (->> ; Consider not just these direct anomalies, but also the anomalies these
       ; ones imply.
       (all-implied-anomalies anomalies)
       ; Map those to consistency models which directly forbid them
       (mapcat (comp g/->clj (partial g/in direct-proscribed-anomalies)))
       ; And expand to implied impossible models
       all-impossible-models
       (into (sorted-set))))

(defn possible-models
  "Given a set of ruled-out models, returns all models that *are* possible."
  [impossible]
  (->> (bg/vertices models)
       g/->clj
       (remove (set impossible))))

(defn boundary
  "Takes a set of anomalies, and yields a map like

    {:not       #{:serializable}
     :also-not  #{:strict-serializable}]}

  ... where :not is the weakest set of consistency models invalidated by the
  given anomaly, and also-not is the remaining set of stronger models."
  [anomalies]
  (let [impossible (anomalies->impossible-models anomalies)
        is-not     (weakest-models impossible)]
    {:not       is-not
     :also-not  (into (sorted-set) (remove is-not impossible))}))

(defn friendly-boundary
  "Like boundary, but uses friendly names."
  [anomalies]
  (map-vals #(into (sorted-set) (map friendly-model-name %))
            (boundary anomalies)))

; Visualizations


(defn plot-graph!
  [g filename]
  (let [dot (graph->dot (bg/vertices g)
                        (partial g/out g)
                        :node->descriptor (fn [x] {:label (name x)}))
        img (rv/dot->image dot)]
    ;(rv/view-image img)
    (rv/save-image img filename)))

(defn plot-severity!
  []
  (plot-graph! (bg/merge implied-anomalies anomaly-severity-graph
                         (constantly nil))
               "images/severity.png"))

(defn plot-models!
  []
  (plot-graph! models "images/models.png"))

(defn plot-anomalies!
  []
  (plot-graph! implied-anomalies "images/anomalies.png"))
