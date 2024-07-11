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
    (let [prog (parse-program "rel(x,y) :- a(p), !f(b,d).")]
      (is (match?
           {:rules [{:head {:pred "rel", :terms [{:type :var :val "x"} {:type :var :val "y"}]}
                     :body [{:pred "a" :terms [{:type :var :val "p"}]}
                            {:pred "f" :negated true :terms [{:type :var :val "b"} {:type :var :val "d"}]}]}]}
           prog))))

  (testing "rule with disjunction"
    (let [prog (parse-program "p(x,y) :- (a(x),c(x);b(y)).")]
      (is (match?
           {:rules [{:head
                     {:pred "p",
                      :terms [{:type :var, :val "x"} {:type :var, :val "y"}]},
                     :body
                     [{:pred :or,
                       :terms
                       [[{:pred "a", :terms [{:type :var, :val "x"}]}
                         {:pred "c", :terms [{:type :var, :val "x"}]}]
                        [{:pred "b", :terms [{:type :var, :val "y"}]}]]}]}]}
           prog)))))


(deftest test-program
  (let [prog (parse-program
              ".decl a(x:number, y:symbol)
              .decl b(p:symbol)
              p(x, y) :- q(y,'asd'),x=2.
              p(1,df).
              p(2, sd).")]
    (is (match?
         {:rules [{:head {:pred "p", :terms [{:type :var :val "x"} {:type :var :val "y"}]}
                   :body [{:pred "q", :terms [{:type :var :val "y"} {:type :string :val "asd"}]}
                          {:terms [{:type :var :val "x"} {:type :number :val 2}] :pred :eq}]}]
          :deps {"p" [["q" :eq]]}
          :preds {"p" [{:type :var :val "x"} {:type :var :val "y"}]
                  "q" [{:type :var :val "y"} {:type :string :val "asd"}]}
          :relations {"a" {"x" "number", "y" "symbol"}, "b" {"p" "symbol"}}
          :facts {"p" [[1 "df"] [2 "sd"]]}}
         prog))))

(comment
  (clojure.test/run-tests 'datapog.test.parser-test))
