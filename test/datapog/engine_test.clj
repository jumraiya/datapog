(ns datapog.test.engine-test
  (:require [datapog.parser :refer [parse-program]]
            [datapog.engine :refer [compile-rule]]
            [clojure.test :refer [deftest is testing]]
            [matcher-combinators.test]))

(def program
  (parse-program
   ".decl a(x: symbol, y: number)
    a(aa, 1).
    a(bb, 2).
    .decl b(x:symbol)
    b(aa).
    p(x,y) :- a(x, y), b(x)."))

(deftest test-compile-rule
  (let [rule-fn (compile-rule (-> program :rules first))]
    (is (match?
         [["aa" "1"]]
         (rule-fn program)))))

(comment
  (clojure.test/run-tests 'datapog.test.engine-test))
