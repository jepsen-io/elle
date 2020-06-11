(ns elle.txn-test
  (:require [clojure [pprint :refer [pprint]]
                     [test :refer :all]]
            [elle.txn :refer :all]))

(defn valid-mop?
  [[f k v]]
  (is (#{:r :w} f))
  (is (integer? k))
  (case f
    :r (is (= nil v))
       (is (integer? v))))

(deftest wr-txns-test
  (let [txns (take 100 (wr-txns {:key-count 3}))
        mops (mapcat identity txns)
        ks   (map second mops)
        key-dist (frequencies ks)]
    (is (every? vector? txns))
    (is (every? #(<= 1 (count %) 2) txns))
    (is (every? valid-mop? mops))
    ; This is gonna vary by RNG, but there are 3 keys per pool by default,
    ; and their frequency (for the first 3 anyway) should be in ascending order.
    (is (< (key-dist 0) (key-dist 1) (key-dist 2)))))
