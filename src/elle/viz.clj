(ns elle.viz
  (:require [clojure.string :as str]
            [clojure.java.io :as io]
            [clojure.tools.logging :refer [info warn]]
            [elle [core :as elle]
                  [graph :as g]]
            [rhizome [dot :as dot]
                     [viz :as rv]]))

(set! *warn-on-reflection* true)

(def ^:private escapable-characters "\\|{}\"")

(defn escape-string
  "Escape characters that are significant for the dot format."
  [s]
  (reduce
    #(str/replace %1 (str %2) (str "\\" %2))
    s
    escapable-characters))

(defn dot
  "We're gonna be doing some weird stuff with html and referencing record ports
  that none of the existing clojure graphviz libraries are really built for.
  Just gonna roll our own ast and generator for dot here."
  [node]
  ; (prn node)
  (cond (sequential? node)
        (let [[node-type a b c] node]
          (case node-type
            :lit          a
            :lines        (str/join "\n" (map dot a))
            :digraph      (str "digraph a_graph {\n" (dot [:lines a]) "\n}")
            :record-label (->> (map-indexed
                                 (fn [i x] (str "<f" i "> "
                                                (escape-string x) ""))
                                 a)
                               (str/join "|")
                               dot)
            :node    (str a " [" (dot b) "]")
            :edge    (str a " -> " b " [" (dot c) "]")
            :html    (str "<" a ">")))

        (map? node)
        (str/join "," (map (fn [[k v]] (str (name k) "=" (dot v))) node))

        (string? node)
        (str "\"" node "\"")

        (keyword? node)
        (name node)

        true
        (pr-str node)))

(def type->color
  "Takes a type of operation (e.g. :ok) and returns a hex color."
  {:ok   "#0058AD"
   :info "#AC6E00"
   :fail "#A50053"})

(defn short-f
  "Short names for common operations"
  [f]
  (case f
    :append :a
    f))

(defn mop->str
  "Converts a micro-op to a short string"
  [[f k v]]
  (str (name (short-f f)) " " k " " (pr-str v)))

(defn short-rel
  "Short names for relations"
  [rel]
  (case rel
    :realtime :rt
    :process  :p
    rel))

(defn rel->color
  "Colors for each type of relationship in a graph."
  [rel]
  (case rel
   :ww "#C02700"
   :wr "#C000A5"
   :rw "#5B00C0"
   :realtime "#0050C0"
   :process "#00C0C0"
   #"#585858"))

(def rel-priority
  "Which relationships have the highest priorities? Lower is more relevant."
  {:wr        0
   :ww        1
   :rw        2
   :process   3
   :realtime  4})

(defn highest-priority-rel
  "Given a set of relationships, returns the highest priority one; e.g., what
  do we think is the most fundamentally inferrable or important."
  [rels]
  (first (sort-by rel-priority rels)))

(defn rels->html
  "Turns a relationship set into an HTML AST node."
  [rels]
  [:html
   (->> (sort-by rel-priority rels)
        (map (fn [rel]
               (str "<font color=\"" (rel->color rel) "\">"
                    (name (short-rel rel))
                    "</font>")))
        (str/join ","))])

(defn op->node
  "Turns an operation into a node descriptor ast."
  [node-idx op]
  [:node (node-idx op)
   {:height     0.4
    :shape      :record
    :label      [:record-label (map mop->str (:value op))]
    :color      (type->color (:type op))
    :fontcolor  (type->color (:type op))}])

(defn op-op->edge
  "Given an analysis, node index, and pair of operations, yields an edge AST
  node."
  [analysis node-index a b]
  (let [edge      (g/edge (:graph analysis) a b)
        explainer (:explainer analysis)
        ex        (elle/explain-pair-data explainer a b)
        ; _         (prn ex)
        ; So... there's a chance the explainer might be able to give us a
        ; *local* explanation with a particular index into the source and
        ; destination transactions. Let's try to render that...
        an        (node-index a)
        bn        (node-index b)
        an        (if-let [ami (:a-mop-index ex)]
                    (str an ":f" ami)
                    an)
        bn        (if-let [bmi (:b-mop-index ex)]
                    (str bn ":f" bmi)
                    bn)]
    [:edge an bn
     {:label      (name (short-rel (:type ex)))
      :fontcolor  (rel->color (:type ex))
      :color      (rel->color (:type ex))}]))

(defn op->edges
  "Takes an analysis, a node-index, and an operation. Returns a sequence of ast
  edges out of that op"
  [analysis scc node-idx op]
  (->> (g/out (:graph analysis) op)
       (filter (g/->clj scc))
       (map (partial op-op->edge analysis node-idx op))))

(defn node-idx
  "Builds an map of nodes to node names."
  [nodes]
  (->> nodes
       (map-indexed (fn [i node]
                      [node (if-let [i (:index node)]
                              (str "T" i) ; We know the transaction number
                              (str "n" i))]))
       (into {})))

(defn scc->ast
  "Turns an scc in an analysis into a dot ast"
  [analysis scc]
  (let [node-idx (node-idx scc)]
    [:digraph
     (concat (map (partial op->node node-idx) scc)
             (mapcat (partial op->edges analysis scc node-idx) scc))]))

(defn save-dot!
  "Renders dot to a file. Options are the same as plot-analysis!"
  [^String dot directory opts i]
  (if (< (:max-plot-bytes opts 65536) ; 65K
         (.length dot))
    (info "Skipping plot of" (.length dot) "bytes")
    (case (:plot-format opts :svg)
      :png (rv/save-image (rv/dot->image dot)
                          (io/file directory (str i ".png")))
      :svg (spit (io/file directory (str i ".svg"))
                 (rv/dot->svg dot)))))

(defn plot-analysis!
  "Takes an analysis (e.g. {:graph g, :explainer e, :sccs [...]} and a
  directory, and renders every SCC in that analysis to a file in the given
  directory. Returns analysis.

  Options:

    :plot-format      Either :png or :svg
    :max-plot-bytes   Maximum number of bytes of DOT-formatted graph to feed
                      to graphviz. Big SCCs can make graphviz choke!"
  ([analysis directory]
   (plot-analysis! analysis directory {}))
  ([analysis directory opts]
   (when (seq (:sccs analysis))
     (io/make-parents (io/file directory ".")))
   (->> (:sccs analysis)
        (map-indexed vector)
        (pmap (fn [[i scc]]
                (-> analysis
                    (scc->ast scc)
                    dot
                    (save-dot! directory opts i))))
        dorun)
   analysis))

(defn view-scc
  "Shows a strongly connected component. Analysis should be a map of

    :graph      g
    :explainer  e

  Helpful for testing."
  [analysis scc]
  (let [ast (scc->ast analysis scc)
        dot (dot ast)]
    ;(println dot)
    (rv/view-image (rv/dot->image dot))))
