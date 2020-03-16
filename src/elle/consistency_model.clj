(ns elle.consistency-model
  "Elle finds anomalies in histories. This namespace helps turn those
  anomalies into claims about what kind of consistency models are supported
  by, or ruled out by, a given history. For sources, see

  - Adya, 'Weak Consistency'
  - Adya, Liskov, O'Neil, 'Generalized Isolation Level Definitions'
  - Bailis, Davidson, Fekete, et al, 'Highly Available Transactions'
  - Cerone, Bernardi, Gotsman, 'A Framework for Transactional Consistency Models with Atomic Visibility'"
  (:require [elle [graph :as g]
                  [util :as util :refer [map-vals]]]
            [clojure [set :as set]])
  (:import (java.util.function Function)
           (io.lacuna.bifurcan Graphs)))

(def implied-anomalies
  "We have lots of different types of anomalies. Some of them imply others--for
  example, when we detect an :internal anomaly, that's *also* a sign of G1a:
  aborted reads. If G1a is present, so is G1, because G1 is defined as the
  union of G1a, G1b, and G1c."
  (g/map->bdigraph
    {; Formally, G0 is also G1.
     :G0 [:G1]
     ; G1 is defined in terms of these three anomalies.
     :G1a [:G1]
     :G1b [:G1]
     :G1c [:G1]
     ; Every G2-item is also a G2, by definition.
     :G2-item [:G2]
     ; The list-append test can find an anomaly which we call
     ; incompatible-order, where two committed read versions couldn't have come
     ; from the same timeline. This implies a dirty read.
     :incompatible-order [:G1a]
     ; Because we work in a richer data model than Adya, we have an extra class
     ; of anomaly that Adya doesn't: a dirty update. Dirty update is basically
     ; like a dirty read, except it affects writes as well. We say it implies a
     ; G1a anomaly, because it's likely that any model which prohibits G1a
     ; would want to prohibit dirty updates as well.
     :dirty-update [:G1a]}))

(defn all-implied-anomalies
  "Takes a collection of anomalies, and yields a set of anomalies implied by
  those."
  [anomalies]
  (g/bfs (partial g/out implied-anomalies) anomalies))

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
   :strict-serializable      :PL-SS    ; Adya
   :update-serializable      :PL-3U    ; Adya
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
                                 :conflict-serializable]      ; Adya
        :update-serializable    [:forward-consistent-view]    ; Adya
        :monotonic-atomic-view  [:read-committed]             ; Bailis
        :monotonic-view         [:PL-2]                       ; Adya
        :monotonic-snapshot-read [:PL-2]                      ; Adya
        :parallel-snapshot-isolation [:causal-cerone]         ; Cerone
        :prefix                 [:causal-cerone]              ; Cerone
        :read-atomic            [:causal-cerone]              ; Cerone
        :read-committed         [:read-uncommitted]           ; SQL
        :repeatable-read        [:cursor-stability            ; Adya
                                 :monotonic-atomic-view]      ; Bailis
        :strict-serializable    [:PL-3                        ; Adya
                                 :serializable                ; Bailis
                                 :linearizable                ; Bailis
                                 :snapshot-isolation]         ; Adya
        :serializable           [:repeatable-read             ; SQL
                                 :snapshot-isolation]         ; Bailis, Cerone
        :snapshot-isolation     [:forward-consistent-view     ; Adya
                                 :monotonic-atomic-view       ; Bailis
                                 :monotonic-snapshot-read     ; Adya
                                 :parallel-snapshot-isolation ; Cerone
                                 :prefix]                     ; Cerone

        ; Single-object (ish) models
        :linearizable          [:sequential]                 ; Bailis
        :sequential            [:causal]                     ; Bailis
        :causal                [:writes-follow-reads         ; Bailis
                                :PRAM]                       ; Bailis

        :PRAM                  [:monotonic-reads             ; Bailis
                                :monotonic-writes            ; Bailis
                                :read-your-writes]}          ; Bailis
       (g/map->bdigraph)
       (g/map-vertices canonical-model-name)))

(defn all-impossible-models
  "Takes a set of models which are impossible, and expands it, using `models`,
  to a set of all models which are also impossible."
  [impossible]
  (g/bfs (partial g/in models)
         impossible))

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

(def proscribed-anomalies-1
  "This is a map of anomalies to the (canonical) consistency models which the
  presence of that anomaly rules out.

  We don't always specify the *full* set of prohibited anomalies for each
  model, just the ones they add over weaker, implied models. This data
  structure is intended to be used in conjunction with `models` and
  `anomaly-graph`.

  For example, repeatable read proscribes G2-item--but we don't have to say
  that it also proscribes G0, because the consistency-model graph says that
  repeatable-read implies read-committed, and read-committed proscribes G0."
  ; It's easier to express this backwards, because models are defined in terms
  ; of proscribed anomalies. We start with a map of models to proscribed
  ; anomalies, then canonicalize and invert that map.
  (let [proscribed
        {:causal-cerone             [:internal :G1a]    ; Cerone (incomplete)
         :cursor-stability          [:G1 :G-cursor]     ; Adya
         :monotonic-view            [:G1 :G-monotonic]  ; Adya
         :monotonic-snapshot-read   [:G1 :G-MSR]        ; Adya
         :consistent-view           [:G1 :G-single]     ; Adya
         :forward-consistent-view   [:G1 :G-SIb]        ; Adya
         :read-atomic               [:internal          ; Cerone (incomplete)
                                     :G1a]              ; Cerone (incomplete)
         :repeatable-read           [:G1 :G2-item]      ; Adya
         :update-serializable       [:G1 :G-update]     ; Adya
         :parallel-snapshot-isolation [:internal :G1a]  ; Cerone (incomplete)
         :PL-3                      [:G1 :G2]           ; Adya
         :PL-2                      [:G1]               ; Adya
         :PL-1                      [:G0                ; Adya
                                     ; I don't think an Adya history can exist
                                     ; with either of these.
                                     :duplicate-elements
                                     ; Version orders are supposed to be total
                                     :cyclic-versions]
         :prefix                    [:internal :G1a]    ; Cerone (incomplete)
         :serializable              [:internal]         ; Cerone (incomplete)
         :snapshot-isolation        [:internal          ; Cerone (incomplete)
                                     :G1 :G-SI]         ; Adya
        ; Should we consider PL-3 and serializable equivalent? I don't know
        ; yet; it probably depends on view/conflict/full serializability.
        ; Better to be conservative now.
        }]
    ; Now we invert those relationships to get a mapping of anomalies to models
    ; that can't be true if those anomalies hold.
    (->> (for [[model anomalies] proscribed
               anomaly           anomalies]
           {anomaly #{(canonical-model-name model)}})
         (apply merge-with set/union))))

(defn anomalies->impossible-models
  "Takes a collection of anomalies, and returns a set of models which can't
  hold, given those anomalies are present."
  [anomalies]
  (->> ; Consider not just these direct anomalies, but also the anomalies these
       ; ones imply.
       (all-implied-anomalies anomalies)
       ; Get a collection of sets of models we know can't hold
       (keep proscribed-anomalies-1)
       ; Squash that
       (reduce set/union)
       ; And expand to implied impossible models
       all-impossible-models
       ; Forming a set
       (into (sorted-set))))

(defn possible-models
  "Given a set of ruled-out models, returns all models that *are* possible."
  [impossible]
  (->> (g/vertices models)
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
