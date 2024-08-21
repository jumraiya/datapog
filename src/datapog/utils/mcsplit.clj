(ns datapog.utils.mcsplit
  (:require [lasync.core :as lasync]
            [clojure.set :as set]))

(defonce ^:private pool (lasync/pool))

(defn- gen-label-classes [graph mapped]
  (transduce
   (comp
    (remove mapped)
    (map #(vector
           (mapv (fn [v] (if (contains? (get-in graph [:edges v]) %) 1 0)) mapped) %)))
   (completing (fn [m [label v]] (update m label #(conj (or % #{}) v))))
   {}
   (-> graph :vertices keys)))

(defn- gen-labelled-groups
  "Given a mapping of vertices between two graphs. Returns a sequence of tuples, where a tuple contains sets of vertices in graph1 and graph2 with same labelling."
  [mapping graph1 graph2]
  (let [[mapped1 mapped2] (reduce (fn [[m1 m2] [v w]]
                                    [(conj m1 v) (conj m2 w)])
                                  [#{} #{}] mapping)
        labelled1 (gen-label-classes graph1 mapped1)
        labelled2 (gen-label-classes graph2 mapped2)]
    (merge-with vector labelled1 labelled2)))

 (defn init-label-groups [graph1 graph2]
  (transduce
   (comp
    (map (fn [[consts rels]]
           [rels (get-in graph2 [:constraint-map consts])]))
    (map (fn [[rels1 rels2]]
           (reduce
            (fn [data [v1 v2]]
              (reduce
               (fn [m [w1 w2]]
                 (let [t1 (get-in graph1 [:vertices v1])
                       t2 (get-in graph1 [:vertices v2])]
                   (if (and (= t1  (get-in graph2 [:vertices w1]))
                            (= t2 (get-in graph2 [:vertices w2])))
                     (-> m
                         (update-in [:G t1] #(conj (or % #{}) v1))
                         (update-in [:H t1] #(conj (or % #{}) w1))
                         (update-in [:G t2] #(conj (or % #{}) v2))
                         (update-in [:H t2] #(conj (or % #{}) w2)))
                     m)))
               data
               rels2))
            {}
            rels1))))
   (fn ([classes data]
        (reduce
         (fn [classes [t vertices]]
           (conj classes [vertices (get-in data [:H t])]))
         classes
         (:G data)))
     ([classes]
      (distinct classes)))
   []
   (:constraint-map graph1)))


(defn- calc-bound [m-count label-classes]
  (+ m-count
   (reduce #(+ %1 (min (count (first %2)) (count (second %2)))) 0 label-classes)))

(defn- swap-mapping [incumbent mapping]
  (if (> (count mapping) (count incumbent)) mapping incumbent))

(defn- check-edges [mapping v w graph1 graph2]
  (every?
   (fn [[m1 m2]]
     (= (get-in graph1 [:edges m1 v]) (get-in graph2 [:edges m2 w])))
   mapping))


 (defn- search [future mapping graph1 graph2 incumbent]
   (let [m-count (count mapping)
         i-count (count @incumbent)]
     (swap! incumbent swap-mapping mapping)
     (when (> (calc-bound m-count future) i-count)
       (let [[class1 class2 :as label-class]
             (reduce #(if (> (max (count (first %2)) (count (second %2)))
                             (max (count (first %1)) (count (second %2))))
                        %2 %1)
                     (first future) (rest future))
             v (reduce #(if (> (count (get-in graph1 [:edges %2]))
                               (count (get-in graph1 [:edges %1])))
                          %2 %1)
                       (first class1) (rest class2))
             add-vertices (fn [vertex res label graph source]
                            (into res
                                  (comp
                                   (remove #(= % vertex))
                                   (filter
                                    #(some
                                      (fn [rels]
                                        (when (not= -1 (.indexOf rels %))
                                          %))
                                      (get-in graph [:constraint-map label]))))
                                  source))]
         (doseq [w class2]
           (when (check-edges mapping v w graph1 graph2)
             (let [new-future
                   (reduce
                    (fn [new-future [comp1 comp2]]
                      (let [[new-class1 new-class2]
                            (reduce
                             (fn [[c1 c2] label]
                               [(add-vertices v c1 label graph1 comp1)
                                (add-vertices w c2 label graph2 comp2)])
                             [#{} #{}]
                             (set (into (-> graph1 :constraint-map keys)
                                        (-> graph2 :constraint-map keys))))]
                        (if (and (seq new-class1) (seq new-class2))
                          (conj new-future [new-class1 new-class2])
                          new-future)))
                    []
                    future)]
               (prn (conj mapping [v w]))
               (lasync/execute pool
                               #(search new-future (conj mapping [v w]) graph1 graph2 incumbent)))))
         (let [new-class1 (disj class1 v)
               new-future (into [] (remove #(= % label-class)) future)]
           (if (seq new-class1)
             (lasync/execute pool
                             #(search (conj new-future [new-class1 class2]) mapping graph1 graph2 incumbent))
             (lasync/execute pool
                             #(search new-future mapping graph1 graph2 incumbent))))))))

(defn mcsplit [graph1 graph2]
  (let [incumbent (atom [])
        v1 (group-by val (:vertices graph1))
        v2 (group-by val (:vertices graph2))
        classes (into []
                      (map
                       (fn [[t vertices]]
                         [(into #{} (map first) vertices)
                          (into #{} (map first) (get v2 t))]))
                      v1)]
    (lasync/execute pool #(search classes [] graph1 graph2 incumbent))
    (while (> (:activeCount (lasync/stats pool)) 0)
      (Thread/sleep 100)
      (println (str "Incumbent size: " (count @incumbent)
                    " active searches: " (:activeCount (lasync/stats pool)))))
    @incumbent))
