(ns elle.explanation
  "Elle has to not only make inferences, but explain how it got them. This
  protocol supports constructing inferences which can be rendered as data
  structures or text.")

(set! *warn-on-reflection* true)

(defprotocol Explanation
  (->data [ex]
          "Converts the explanation to a data structure.")
  (->text [ex context]
          "Converts the explanation to plain text. An optional context map
          provides extra information used in rendering--for instance, short
          names for transactions."))

(def trivial
  "A trivial explanation which doesn't explain anything. Helpful for stubbing
  out methods."
  (reify Explanation
    (->data [ex]      :just-cuz)
    (->text [ex ctx]  "just cuz")))
