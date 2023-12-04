(ns elle.rels-test
  (:require [clojure [test :refer :all]
             [pprint :refer [pprint]]]
            [clojure.set :as set]
            [elle [rels :refer :all]])
  (:import (elle BitRels)))

(deftest raw-difference-test
  (are [expected rels minus]
       (= expected
          (.toClojure
            (BitRels.
              (BitRels/rawDifference (.rels (apply union rels))
                                     (.rels (apply union minus))))))
       #{:ww} [ww wr] [wr rw]
       #{:rwp :realtime} [rwp rw realtime] [rw]
       #{:rw}            [rwp rw realtime] [realtime rwp]))

(deftest raw-intersection-test
  (are [expected as bs]
       (= expected
          (.toClojure
            (BitRels.
              (BitRels/rawIntersection (.rels (apply union as))
                                       (.rels (apply union bs))))))
       #{}              [ww wr]           [wrp rwp]
       #{:realtime}     [ww realtime]     [realtime rw]
       #{:process :rwp} [rwp process ww]  [rwp process wr]))

(deftest to-clojure-test
  (are [expected rels] (= expected (.toClojure (apply union rels)))
       #{} []
       #{:ww} [ww]
       #{:ww :realtime} [ww realtime]))

(deftest iterate-test
  (is (= nil (seq none)))
  (are [rels] (= rels (seq (apply union rels)))
       [ww]
       [rw]
       [process]
       [realtime]
       [rwp]
       [ww wr]
       [ww rw realtime]
       [ww rwp realtime]))
