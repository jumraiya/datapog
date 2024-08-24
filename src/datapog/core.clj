(ns datapog.core
  (:require [datapog.parser :as p]
            [datapog.utils.rel-algebra :as r]
            [datapog.utils.mcsplit :as m])
  (:gen-class))



(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!"))

(comment

  (def prog (p/parse-program (slurp "/Users/jumraiya/projects/datapog/test/datapog/test_program.dl")))

  (def r1 (-> prog :rules first :body))

  (def r2 (-> prog :rules second :body))

  (def g1 (:graph (r/gen-dep-graph prog r1)))

  (def g2 (:graph (r/gen-dep-graph prog r2))))
