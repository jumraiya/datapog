(ns datapog.test.parser-test
  (:require [datapog.parser :refer [parse-program]]
            [clojure.test :refer [deftest is testing]]
            [matcher-combinators.test]))

(deftest test-program-elements
  (testing "relations"
    (let [prog (parse-program ".decl rel(a: number, b: symbol)")]
      (is (match?
           {:relations {"rel" [["a" "number"] ["b" "symbol"]]}}
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
           prog))))
  (testing "rule with unnamed free variables"
    (let [prog (parse-program "p(x,y) :- a(x),b(_,y).")]
      (is (match?
           {:rules
            [{:head
              {:pred "p"
               :terms
               [{:type :var :val "x"} {:type :var :val "y"}]}
              :body
              [{:pred "a" :terms [{:type :var :val "x"}]}
               {:pred "b" :terms [{:type :ignore} {:type :var :val "y"}]}]}]}
           prog))))
  (testing "rule with named terms"
    (let [prog (parse-program "p(x,y) :- a(x),b(asd: y).")]
      (is (match?
           {:rules
            [{:head
              {:pred "p"
               :terms
               [{:type :var :val "x"} {:type :var :val "y"}]}
              :body
              [{:pred "a" :terms [{:type :var :val "x"}]}
               {:pred "b" :terms [{:type :named :key "asd" :val {:type :var :val "y"}}]}]}]}
           prog)))))


(deftest test-program
  (let [prog (parse-program
              ".decl a(x:number, y:symbol)
              .decl b(p:symbol)
              p(x, y) :- q(y,'asd'),x=2.
              al12(x,z) :- p(x,y), r1(y),y=2.
              p(1,df).
              p(2, sd).")]
    (is (match?
         {:rules [{:head {:pred "p", :terms [{:type :var :val "x"} {:type :var :val "y"}]}
                   :body [{:pred "q", :terms [{:type :var :val "y"} {:type :string :val "asd"}]}
                          {:terms [{:type :var :val "x"} {:type :number :val 2}] :pred :eq}]}
                  {:head {:pred "al12"
                          :terms
                          [{:type :var :val "x"}
                           {:type :var :val "z"}]}
                   :body [{:pred "p" :terms [{:type :var :val "x"} {:type :var :val "y"}]}
                          {:pred "r1" :terms [{:type :var :val "y"}]}
                          {:pred :eq :terms [{:type :var :val "y"} {:type :number :val 2}]}]}]
          :deps {"p" [["q" :eq]]}
          :preds {"p" [{:type :var :val "x"} {:type :var :val "y"}]
                  "q" [{:type :var :val "y"} {:type :string :val "asd"}]
                  "r1" [{:type :var :val "y"}]
                  "al12" [{:type :var :val "x"} {:type :var :val "z"}]}
          :relations {"a" [["x" "number"] ["y" "symbol"]] "b" [["p" "symbol"]]}
          :facts {"p" [[1 "df"] [2 "sd"]]}}
         prog))))

(comment
  (clojure.test/run-tests 'datapog.test.parser-test))
