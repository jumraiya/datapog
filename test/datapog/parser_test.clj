(ns datapog.test.parser-test
  (:require [datapog.parser :refer [parse-program]]
            [clojure.test :refer [deftest is testing]]
            [matcher-combinators.test]))

(deftest test-program-elements
  (testing "relations"
   (let [prog (parse-program ".decl rel(a: number, b: symbol)")]
     (is (match?
          {:relations {"rel" {"a" "number" "b" "symbol"}}}
          prog))))

  (testing "facts"
   (let [prog (parse-program "rel(2,3).")]
     (is (match?
          {:facts {"rel" [[2 3]]}}
          prog))))

  (testing "rules"
   (let [prog (parse-program "rel(x,y) :- a(p), f(b,d).")]
     (is (match?
          {:rules [{:head {:pred "rel", :terms ["x" "y"]}
                    :body [{:pred "a", :terms ["p"]}
                           {:pred "f", :terms ["b" "d"]}]}]}
          prog)))))


(deftest test-program
  (let [prog (parse-program
              ".decl a(x:number, y:symbol)
              .decl b(p:symbol)
              p(x, y) :- q(y).
              p(1,df).
              p(2, sd).")]
    (is (match?
         {:rules [{:head {:pred "p", :terms ["x" "y"]}
                   :body [{:pred "q", :terms ["y"]}]}]
          :deps {"p" [["q"]]}
          :preds {"p" ["x" "y"] "q" ["y"]}
          :relations {"a" {"x" "number", "y" "symbol"}, "b" {"p" "symbol"}}
          :facts {"p" [[1 "df"] [2 "sd"]]}}
         prog))))

(comment
  (clojure.test/run-tests 'datapog.test.parser-test))
