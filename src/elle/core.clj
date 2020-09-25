(ns elle.core
  "Tests based on detecting cycles between operations in a history.

  First, we define a bunch of ways you can compute a dependency graph over a
  history. Our graphs use completions (e.g. ok, info) for the canonical
  representation of an operation. For instance:

  `realtime-graph` relates a->b if operation b begins after operation a
  completes successfully.

  `process-graph` relates a->b if a and b are performed by the same process,
  and that process executes a before b.

  `monotonic-key-graph` assumes op :values are maps of keys to observed values,
  like {:x 1 :y 2}. It relates a->b if b observed a higher value of some key
  than a did. For instance, {:x 1 :y 2} -> {:x 2 :y 2}, because :x is higher in
  the second op.

  You can also *combine* graphs using `combine`, which takes the union of
  multiple graphs. `(combine realtime monotonic-key)`, for instance, verifies
  that not only must the values of each key monotonically increase, but that
  those increases must be observed in real time: stale reads are not allowed.

  Given a function which takes a history and produces a dependency graph, the
  checker runs that function, identifies strongly-connected components in the
  resulting graph, and decides whether the history is valid based on whether
  the graph has any strongly connected components--e.g. cycles."
  (:require [elle [graph :as g]
                  [util :as util]]
            [clojure.tools.logging :refer [info error warn]]
            [clojure.core.reducers :as r]
            [clojure [pprint :refer [pprint]]
                     [set :as set]
                     [string :as str]]
            [clojure.java.io :as io]
            [jepsen.txn :as txn]
            [jepsen.txn.micro-op :as mop]
            [knossos [op :as op]
                     [history :refer [pair-index+]]]
            [slingshot.slingshot :refer [try+ throw+]]))

; This is going to look a bit odd. Please bear with me.
;
; Our analysis generally goes like this:
;
;   1. Take a history, and analyze it to build a dependency graph.
;   2. Find cycles in that graph
;   3. Explain why those are cycles
;
; Computing the graphs is fairly straightforward, but explaining cycles is a
; bit less so, because the explanation may require data that's expensive to
; calculate. For instance, realtime orders would like to be able to tell you
; when precisely a given ok operation was invoked, and that needs an expensive
; index to be constructed over the full history. We want to be able to *re-use*
; that expensive state.
;
; At the top level, we want to have a single object that defines how to analyze
; a history *and* how to explain why the results of that analysis form cycles.
; We also want to be able to *compose* those objects together. That means that
; both graph construction and cycle explanation must compose.
;
; To do this, we decouple analysis into three objects:
;
; - An Analyzer, which which examines a history and produces a pair of:
; - A Graph of dependencies over completion ops, and
; - An Explainer, which can explain cycles between those ops.

; We write our Analyzers as a function (f history) => [graph explainer]. Graphs
; are Bifurcan DirectedGraphs. Explainers have a protocol, because we're going
; to pack some cached state into them.

(set! *warn-on-reflection* true)

(defprotocol Anomalies
  "There are several points in an analysis where we want to construct some
  intermediate data, like a version graph, for later. However, it might be that
  *during* the construction of that version graph, we discover the graph itself
  contains anomalies. This doesn't *invalidate* the graph--perhaps we can still
  use it to discover anomalies later, but it *is* information we need to pass
  upstream to the user. The Anomalies protocol lets the version graph signal
  that additional anomalies were encountered, so whatever uses the version
  graph can merge those into its upstream anomaly set.

  This is kind of like an error monad, but it felt weird and less composable to
  use exceptions for this."
  (anomalies [this] "Returns a map of anomaly types to anomalies."))

(extend-protocol Anomalies
  ; nil means no anomalies
  nil (anomalies [_] nil)

  ; This lets us return plain old objects transparently when there's no
  ; anomalies.
  Object (anomalies [_] nil)

  ; It's convenient to just pass around a map when you do have anomalies, and
  ; don't need to encode extra information.
  clojure.lang.IPersistentMap
  (anomalies [m] m))

(defn merge-anomalies
  "Merges n Anomaly objects together."
  [coll-of-anomalies]
  (reify Anomalies
    (anomalies [_] (merge-with concat (map anomalies coll-of-anomalies)))))

(defprotocol TransactionGrapher
  "The TransactionGrapher takes a history and produces a TransactionGraph,
  optionally augmented with Anomalies discovered during the graph inference
  process."
  (build-transaction-graph [this history]
                           "Analyzes the history and returns a TransactionGraph,
                           optionally with Anomalies."))

(defprotocol TransactionGraph
  "A TransactionGraph represents a graph of dependencies between transactions
  (really, operations), where edges are sets of tagged relationships, like :ww
  or :realtime."
  (transaction-graph [this]
                     "Returns a Bifurcan IDirectedGraph of dependencies between
                     transactions (represented as completion operations)"))

(defprotocol DataExplainer
  (explain-pair-data
    [_ a b]
    "Given a pair of operations a and b, explains why b depends on a, in the
    form of a data structure. Returns `nil` if b does not depend on a.")

  (render-explanation
    [_ explanation a-name b-name]
    "Given an explanation from explain-pair-data, and short names for a and b,
    renders a string explaining why a depends on b."))

(defn explain-pair
  "Given a pair of operations, and short names for them, explain why b
  depends on a, as a string. `nil` indicates that b does not depend on a."
  [explainer a-name a b-name b]
  (when-let [ex (explain-pair-data explainer a b)]
    (render-explanation explainer ex a-name b-name)))

(defrecord CombinedExplainer [explainers]
  DataExplainer
  (explain-pair-data [this a b]
    ; This is SUCH an evil hack, but, uh, bear with me.
    ; When we render an explanation, we have no way to tell what explainer
    ; knows how to render it, and we don't want to make every explainer have to
    ; double-check whether they're rendering their own explanations, or if
    ; they're being passed someone else's. We could have a *wrapper type* here,
    ; but then we're introducing non-semantic data into the explanation which
    ; isn't necessary for users, makes it harder to read output, and makes it
    ; more difficult to test. Routing explanations to the explainers that
    ; generated them is just *plumbing*, and has no semantic place in our
    ; data model.
    ;
    ; Lord help me, I think this is the first time I've actually wanted to
    ; think about metadata outside of a macro or compiler context.
    (when-let [[i ex] (->> explainers
                           (map-indexed (fn [i e]
                                          [i (explain-pair-data e a b)]))
                           ; Find the first [i explanation] pair where ex is
                           ; present
                           (filter second)
                           first)]
      (vary-meta ex assoc this i)))

  (render-explanation [this ex a-name b-name]
    (let [i (get (meta ex) this)]
      (assert i (str "Not sure where explanation " (pr-str ex) " with meta " (pr-str (meta ex)) " came from!"))
      (render-explanation (nth explainers i) ex a-name b-name))))

(defn combine
  "Helpful in composing an analysis function for a checker out of multiple
  other analysis fns. For example, you might want a checker that looks for
  per-key monotonicity *and* real-time precedence---you could use:

  (checker (combine monotonic-keys real-time))"
  [& analyzers]
  (fn analyze [history]
    (loop [analyzers  analyzers
           anomalies  nil
           graph      (g/linear (g/digraph))
           explainers []]
      (if (seq analyzers)
        ; Use this analyzer on the history and merge its result map into our
        ; state.
        (let [analyzer (first analyzers)
              analysis (analyzer history)]
          (assert (and (:graph analysis) (:explainer analysis))
                  (str "Analyzer " (pr-str analyzer)
                       " did not return a map with a :graph and :analysis."
                       " Instead, we got " (pr-str analysis)))
          (recur (next analyzers)
                 (merge anomalies (:anomalies analysis))
                 (g/digraph-union graph (:graph analysis))
                 (conj explainers (:explainer analysis))))
        ; Done!
      {:anomalies anomalies
       :graph     (g/forked graph)
       :explainer (CombinedExplainer. explainers)}))))

;; Monotonic keys!

(defrecord MonotonicKeyExplainer []
  DataExplainer
  (explain-pair-data [_ a b]
    (let [a (:value a)
          b (:value b)]
      ; Find keys in common
      (->> (keys a)
           (filter b)
           (reduce (fn [_ k]
                     (let [a (get a k)
                           b (get b k)]
                       (when (and a b (< a b))
                         (reduced {:type   :monotonic
                                   :key    k
                                   :value  a
                                   :value' b}))))
                   nil))))

  (render-explanation [_ {:keys [key value value']} a-name b-name]
    (str a-name " observed " (pr-str key) " = "
         (pr-str value) ", and " b-name
         " observed a higher value "
         (pr-str value'))))

(defn monotonic-key-order
  "Given a key, and a history where ops are maps of keys to values, constructs
  a partial order graph over ops reading successive values of key k."
  [k history]
  ; Construct an index of values for k to all ops with that value.
  (let [index (as-> history x
                (group-by (fn [op] (get (:value op) k ::not-found)) x)
                (dissoc x ::not-found))]
    (->> index
         ; Take successive pairs of keys
         (sort-by key)
         (partition 2 1)
         ; And build a graph out of them
         (reduce (fn [g [[v1 ops1] [v2 ops2]]]
                   (g/link-all-to-all g ops1 ops2 :monotonic-key))
                 (g/linear (g/digraph)))
         g/forked)))

(defn monotonic-key-graph
  "Analyzes ops where the :value of each op is a map of keys to values. Assumes
  keys are monotonically increasing, and derives relationships between ops
  based on those values."
  [history]
  (let [history (filter op/ok? history)
        graph (->> history
                   (mapcat (comp keys :value))
                   distinct
                   (map (fn [k] (monotonic-key-order k history)))
                   (reduce g/digraph-union))]
    {:graph     graph
     :explainer (MonotonicKeyExplainer.)}))

;; Processes

(defn process-order
  "Given a history and a process ID, constructs a partial order graph based on
  all operations that process performed."
  [history process]
  (->> history
       (filter (comp #{process} :process))
       (partition 2 1)
       (reduce (fn [g [op1 op2]] (g/link g op1 op2 :process))
               (g/linear (g/digraph)))
       g/forked))

(defrecord ProcessExplainer []
  DataExplainer
  (explain-pair-data [_ a b]
    (when (and (= (:process a) (:process b))
               (< (:index a) (:index b)))
      {:type      :process
       :process   (:process a)}))

  (render-explanation [_ {:keys [process]} a-name b-name]
    (str "process " process " executed " a-name " before " b-name)))

(defn process-graph
  "Analyses histories and relates operations performed sequentially by each
  process, such that every operation a process performs is ordered (but
  operations across different processes are not related)."
  [history]
  (let [oks (filter op/ok? history) ; TODO: order infos?
        graph (->> oks
                   (map :process)
                   distinct
                   (map (fn [p] (process-order oks p)))
                   (reduce g/digraph-union))]
    {:graph     graph
     :explainer (ProcessExplainer.)}))

; Realtime order

(defrecord RealtimeExplainer [pairs]
  DataExplainer
  (explain-pair-data [_ a' b']
    (let [b (get pairs b')]
      (when (< (:index a') (:index b))
        {:type :realtime
         :a'   a'
         :b    b})))

  (render-explanation [_ {:keys [a' b]} a'-name b'-name]
    (str a'-name " completed at index " (:index a') ","
         (when (and (:time a') (:time b))
           (let [dt (- (:time b) (:time a'))]
             ; Times are approximate--what matters is the serialization
             ; order. If we observe a zero or negative delta, just fudge it.
             (if (pos? dt)
               (str (format " %.3f" (util/nanos->secs (- (:time b) (:time a'))))
                    " seconds")
               ; Times are inaccurate
               " just")))
         " before the invocation of " b'-name
         ", at index " (:index b))))

(defn realtime-graph
  "Given a history, produces {:graph g :explainer e}, which encodes the
  real-time dependencies of transactions: a < b if a ends before b begins.

  In general, txn a precedes EVERY txn which begins later in the history, but
  that's n^2 territory, and for purposes of cycle detection, we only need a
  transitive reduction of that graph. We compute edges from txn a to subsequent
  invocations until a new operation b completes."
  [history]
  ; Our basic approach here is to iterate through the history, and for any
  ; given :ok op, create an edge from that :ok to the :ok or :info
  ; corresponding to subsequent :invokes--because our graph relates
  ; *completion* operations, not invocations.
  ;
  ; What about this history?
  ;
  ;   ==a==       ==c== ==e==
  ;         ==b==
  ;           ==d===
  ;
  ; Do we need an edge from a->c? No, because b->c has it covered.
  ;
  ; What about e? a, b, c, and d precede e, but since a->b and b->c, we only
  ; need c->e and d->e.
  ;
  ; So... our strategy is to keep a buffer of all previous completions that
  ; need to be linked forward to new invocations. When we see an invoke x, we
  ; link every buffered completion (a, b, c...) to x. When we see a new
  ; completion d, we look backwards in the graph to see whether any buffered
  ; completions point to d, and remove those from the buffer.
  ;
  ; OK, first up: we need this index to look forward from invokes to completes.
  (let [pairs (pair-index+ history)]
    (loop [history history
           oks     #{}               ; Our buffer of completed ops
           g       (g/digraph)] ; Our order graph
      (if-let [op (first history)]
        (case (:type op)
          ; A new operation begins! Link every completed op to this one's
          ; completion. Note that we generate edges here regardless of whether
          ; this op will fail or crash--we might not actually NEED edges to
          ; failures, but I don't think they'll hurt. We *do* need edges to
          ; crashed ops, because they may complete later on.
          :invoke (let [op' (get pairs op)
                        g   (reduce (fn [g ok]
                                      (g/link g ok op' :realtime))
                                    g
                                    oks)]
                    (recur (next history) oks g))
          ; An operation has completed. Add it to the oks buffer, and remove
          ; oks that this ok implies must have completed.
          :ok     (let [implied (g/->clj (g/in g op))
                        oks     (-> oks
                                    (set/difference implied)
                                    (conj op))]
                    (recur (next history) oks g))
          ; An operation that failed doesn't affect anything--we don't generate
          ; dependencies on failed transactions because they didn't happen. I
          ; mean we COULD, but it doesn't seem useful.
          :fail (recur (next history) oks g)
          ; Crashed operations, likewise: nothing can follow a crashed op, so
          ; we don't need to add them to the ok set.
          :info (recur (next history) oks g))
        ; All done!
        {:graph     g
         :explainer (RealtimeExplainer. pairs)}))))

(defn explain-binding
  "Takes a seq of [name op] pairs, and constructs a string naming each op."
  [bindings]
  (str "Let:\n"
       (->> bindings
            (map (fn [[name txn]]
                   (str "  " name " = " (pr-str txn))))
            (str/join "\n"))))

(defn explain-cycle-pair-data
  "Takes a pair explainer and a pair of ops, and constructs a data structure
  explaining why a precedes b."
  [pair-explainer [a b]]
  (or (explain-pair-data pair-explainer a b)
      (throw (IllegalStateException.
               (str "Explainer\n"
                    (with-out-str (pprint pair-explainer))
                    "\nwas unable to explain the relationship"
                    " between " (pr-str a)
                    " and " (pr-str b))))))

(defn explain-cycle-ops
  "Takes an pair explainer, a binding, and a sequence of steps: each an
  explanation data structure of one pair. Produces a string explaining why they
  follow in that order."
  [pair-explainer binding steps]
  (let [explanations (map (fn [[a-name b-name] step]
                            (str a-name " < " b-name ", because "
                                 (render-explanation
                                   pair-explainer step a-name b-name)))
                          ; Take pairs of names from the binding
                          (partition 2 1 (cycle (map first binding)))
                          steps)
        prefix       "  - "]
    (->> explanations
         (map-indexed (fn [i ex]
                        (if (= i (dec (count explanations)))
                          (str prefix "However, " ex ": a contradiction!")
                          (str prefix ex ".\n"))))
         str/join)))

; This protocol gives us the ability to take a cycle of operations and produce
; a data structure describing that cycle, and to render that cycle explanation
; as a string.
(defprotocol CycleExplainer
  (explain-cycle
    [_ pair-explainer cycle]
    "Takes a cycle and constructs a data structure describing it.")

  (render-cycle-explanation
    [_ pair-explainer explanation]
    "Takes an explanation of a cycle and renders it to a string."))

(def cycle-explainer
  "This explainer just provides the step-by-step explanation of the
  relationships between pairs of operations."
  (reify CycleExplainer
    (explain-cycle [_ pair-explainer cycle]
      ; Take pairs of ops from the cycle, and construct an explanation for each.
      {:cycle cycle
       :steps (->> cycle
                   (partition 2 1)
                   (map (partial explain-cycle-pair-data pair-explainer)))})

    (render-cycle-explanation [_ pair-explainer {:keys [cycle steps]}]
      ; Number the transactions in the cycle
      (let [binding (->> (butlast cycle)
                         (map-indexed (fn [i op] [(str "T" (inc i)) op])))]
        ; Explain the binding, then each step.
        (str (explain-binding binding)
             "\n\nThen:\n"
             (explain-cycle-ops pair-explainer binding steps))))))

(defn explain-scc
  "Takes a graph, a cycle explainer, a pair explainer, and a strongly connected
  component (a collection of ops) in that graph. Using those graphs, constructs
  a string explaining the cycle."
  [graph cycle-explainer pair-explainer scc]
  (->> (g/find-cycle graph scc)
       (explain-cycle cycle-explainer pair-explainer)
       (render-cycle-explanation cycle-explainer pair-explainer)))

(defn check-
  "Meat of the checker. Takes an analysis function and a history; returns an map
  of:

      {:graph     The computed graph
       :explainer The explainer for that graph
       :cycles    A list of cycles we found
       :sccs      A set of strongly connected components
       :anomalies Any anomalies we found during this analysis.}"
  [analyze-fn history]
  (let [history           (remove (comp #{:nemesis} :process) history)
        {:keys [anomalies explainer graph]} (analyze-fn history)
        sccs              (g/strongly-connected-components graph)
        cycles            (->> sccs
                               (sort-by (comp :index first))
                               (mapv (partial explain-scc graph
                                              cycle-explainer
                                              explainer)))
        ; It's almost certainly the case that something went wrong if we didn't
        ; infer *any* dependencies.
        anomalies (if (= 0 (g/size graph))
                    (assoc anomalies :empty-transaction-graph true)
                    anomalies)]
    {:graph     graph
     :explainer explainer
     :sccs      sccs
     :cycles    cycles
     :anomalies anomalies}))

(defn write-cycles!
  "Writes cycles to a file. Opts:

  :cycle-explainer  How to explain a cycle
  :pair-explainer   How to explain a pair
  :directory   What directory to write to. Defaults to nil, which means no
               files are written.
  :filename    What to call the file. Defaults to \"cycles.txt\"."
  [opts cycles]
  (when (seq cycles)
    ; Only write if a directory is given.
    (when-let [d (:directory opts)]
      (io/make-parents (io/file d "."))
      (->> cycles
           ; Turn each cycle into a string
           (map-indexed (fn [i cx]
                          (str (name (:type cx "Cycle")) " #" i "\n"
                               (render-cycle-explanation
                                 (:cycle-explainer opts cycle-explainer)
                                 (:pair-explainer opts)
                                 cx))))
           ; And put em in a file
           (str/join "\n\n\n")
           (spit (io/file d (:filename opts "cycles.txt")))))))

(defn check
  "Checks a history for cycles. Takes a function which takes a history and
  returns a [graph, explainer] pair, and returns a checker which uses those
  graphs to identify cyclic dependencies. Options are:

  {:analyzer    A function which takes a history and returns a {:graph,
  :explainer, :anomalies} map; e.g. realtime-graph.
  :directory   Where to write results}"
  [opts history]
  (try+
    (let [analyze-fn (:analyzer opts)
          {:keys [graph explainer sccs cycles]} (check- analyze-fn history)]
      (write-cycles! opts cycles)
      {:valid?     (empty? sccs)
       :scc-count  (count sccs)
       :cycles     cycles})
    ; The graph analysis might decide that a certain history isn't
    ; analyzable (perhaps because it violates expectations the analyzer
    ; needed to hold in order to infer dependencies), or it might discover
    ; violations that *can't* be encoded as a part of the dependency graph.
    ; If that happens, the analyzer can throw an exception with a :valid?
    ; key, and we'll simply return the ex-info map.
    (catch [:valid? false] e e)
    (catch [:valid? :unknown] e e)))
