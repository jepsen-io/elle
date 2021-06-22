(ns elle.infer.cyclic
  "This namespace infers cyclic anomalies over analyses with transaction
  graphs--for instance, G1c, G2, G-single, etc."
  (:require [elle [core :as elle]
                  [explanation :as expl]
                  [txn-graph :as tg]
                  [txn       :as et]]))

(defn anomalies
  "Returns a map of cyclic anomalies present in an analysis."
  [analysis]
  (let [txn-graph       (:txn-graph analysis)
        pair-explainer  (reify elle/DataExplainer
                          (explain-pair-data [_ a b]
                            ; Bit of a hack: explain-pair-data is supposed to
                            ; return a map, so we're returning a defrecord
                            ; Explanation, which works as *both* a map and also
                            ; lets us do our text rendering later.
                            (assoc (tg/explain txn-graph a b)
                                   :a a
                                   :b b))

                          (render-explanation [_ expl a-name b-name]
                            (expl/->text expl {:txn-names {(:a expl) a-name
                                                           (:b expl) b-name}})))
        graph-analyzer (fn [history]
                         {:graph (tg/graph txn-graph)
                          :explainer pair-explainer})
        analyzer (apply elle/combine
                        (cons graph-analyzer
                              (et/additional-graphs analysis)))]
    (et/cycles analysis analyzer (:history analysis))))

(defn add-anomalies
  "Takes an analysis, and updates its :anomalies field to include any cyclic
  anomalies found."
  [analysis]
  (update analysis :anomalies merge (anomalies analysis)))
