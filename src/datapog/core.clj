(ns datapog.core
  (:require [clojure.pprint :refer [pprint]]
            [datapog.parser :as p]
            [datapog.utils.rel-algebra :as r]
            [datapog.engine :as engine])
  (:gen-class))



(defn -main
  "Reads a datalog program and outputs all resulting facts"
  [filename]
  (-> filename
      slurp
      p/parse-program
      engine/validate+compile-program
      engine/semi-naive-eval
      :facts
      pprint))

(comment

  (do
    (def prog (p/parse-program (slurp "/Users/jumraiya/projects/datapog/test/datapog/test_program.dl")))
    (-> "/Users/jumraiya/projects/datapog/test/datapog/test_program.dl"
      slurp
      p/parse-program
      engine/validate+compile-program
      engine/semi-naive-eval
      :facts
      pprint)
    (def r1 (-> prog :rules first :body))

    (def r2 (-> prog :rules second :body))

    (def g1 (:graph (r/gen-dep-graph prog r1)))
    
    (def g2 (:graph (r/gen-dep-graph prog r2))))
  )
