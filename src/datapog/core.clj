(ns datapog.core
  (:require [datapog.parser :as p])
  (:gen-class))

(defn run-program [body]
  (let [program (p/parse-program)]
    ))


(defn -main
  "I don't do a whole lot ... yet."
  [& args]
  (println "Hello, World!"))
