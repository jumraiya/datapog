(ns datapog.test.engine-test
  (:require [datapog.parser :refer [parse-program]]
            [datapog.engine :as engine]
            [clojure.test :refer [deftest is]]
            [matcher-combinators.test]))

(def program
  (parse-program
   ".decl a(x: symbol, y: number)
    a(aa, 1).
    a(bb, 2).
    .decl b(x:symbol)
    b(aa).
    .decl c(x:symbol, y: number)
    c(as, 2).
    p(x,y) :- a(x, y), b(x).
    p(x,z) :- c(x,z)."))

(deftest test-compile-rule
  (let [rule-fn (engine/compile-rule program (-> program :rules first))]
    (is (match?
         [["aa" 1]]
         (rule-fn program)))))

(deftest test-eval-pred
  (let [prog (engine/validate+compile-program program)]
    (is (match? [["aa" 1]
                 ["as" 2]]
         (engine/eval-pred "p" prog)))))

(deftest test-eval-constraints
  (let [prog (engine/validate+compile-program
              (parse-program
               ".decl age(name: symbol, years: number)
                age(young, 14).
                age(old, 62).
                senior(x) :- age(x, y), y > 60."))]
    (is (match? [["old"]]
                (engine/eval-pred "senior" prog)))))


(deftest test-eval-rule-incr
  (let [prog (-> program
                 (engine/validate+compile-program)
                 (assoc :deltas {"c" [["xs" 3]]}))]
    (is (match?
         [["xs" 3]]
         (engine/eval-rule-incr (-> prog :rules second) prog)))))

(deftest test-eval-pred-incr
  (let [prog (-> program
                 (engine/validate+compile-program)
                 (assoc :deltas {"c" [["xs" 3]]}))]
    (is (match?
         [["aa" 1] ["xs" 3]]
         (engine/eval-pred-incr "p" prog)))))

(deftest test-semi-naive-eval
  (is (match?
       {"a" [["aa" 1] ["bb" 2]]
        "b" [["aa"]]
        "c" [["as" 2]]
        "p" [["aa" 1] ["as" 2]]}
       (-> program
           (engine/validate+compile-program)
           (engine/semi-naive-eval)
           :facts))))

(deftest test-semi-naive-eval2
  (let [program (parse-program
                 ".decl edge(x: symbol, y:symbol)
                  edge(a,b). edge(b,c). edge(c,d).
                  tc(x,y) :- edge(x,y).
                  tc(x,y) :- edge(x,z), tc(z,y).")]
    (is (match?
         {"edge" [["a" "b"] ["b" "c"] ["c" "d"]]
          "tc" [["a" "b"] ["b" "c"] ["c" "d"] ["a" "c"] ["b" "d"] ["a" "d"]]}
         (-> program
             (engine/validate+compile-program)
             (engine/semi-naive-eval)
             :facts)))))

(comment
  (clojure.test/run-tests 'datapog.test.engine-test))
