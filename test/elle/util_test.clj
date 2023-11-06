(ns elle.util-test
  (:require [clojure [test :refer :all]]
            [elle.util :as u]))

(deftest fand-test
  (testing "unary"
    (let [f (u/fand [#{1 3}])]
      (is (= 1   (f 1)))
      (is (= nil (f 2)))
      (is (= 3   (f 3)))))

  (testing "binary"
    (let [f (u/fand [#{1 3} #{2 3}])]
      (is (= nil (f 1)))
      (is (= nil (f 2)))
      (is (= 3   (f 3)))))

  (testing "nary"
    (let [f (u/fand [#{1 4} #{2 4} #{3 4}])]
      (is (= nil (f 1)))
      (is (= nil (f 2)))
      (is (= nil (f 3)))
      (is (= 4   (f 4))))))
