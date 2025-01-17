(ns datapog.utils.mcsplit
  (:require [lasync.core :as lasync]
            [clojure.set :as set]
            [datapog.utils.rel-algebra :as rel]))

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

(defn mk-label-groups [nodes graph]
  (let [nodes (set nodes)]
    (transduce
     (comp
      (map val)
      (map #(filter (fn [n] (contains? nodes n)) (mapv key %))))
     (completing (fn [classes nodes]
                   (conj classes (set nodes))))
     []
     (group-by val (:vertices graph)))))

 (defn init-label-groups [graph1 graph2]
   (let [mk-groups (fn [nodes graph]
                     (group-by val
                               (transduce
                                (map #(vector % (get-in graph [:vertices %])))
                                (completing conj)
                                {}
                                nodes)))
         mk-classes (fn [group1 group2]
                      (reduce (fn [classes [type nodes]]
                                (let [class1 (into #{} (map key) nodes)
                                      class2 (into #{} (map key) (get group2 type))]
                                  (if (and (seq class1) (seq class2))
                                    (conj classes [class1 class2])
                                    classes)))
                              []
                              group1))
         non-disj-nodes1 (mk-groups (rel/get-non-disj-nodes graph1) graph1)
         non-disj-nodes2 (mk-groups (rel/get-non-disj-nodes graph2) graph2)
         disj-nodes1 (rel/disj-node-seq-descending graph1)
         disj-nodes2 (rel/disj-node-seq-descending graph2)]
     (into
      (mk-classes non-disj-nodes1 non-disj-nodes2)
      (reverse
       (mapv (fn [nodes1 nodes2]
               (first
                (mk-classes (mk-groups nodes1 graph1) (mk-groups nodes2 graph2))))
             disj-nodes1
             disj-nodes2)))))


(defn- calc-bound [m-count label-classes]
  (+ m-count
   (reduce #(+ %1 (min (count (first %2)) (count (second %2)))) 0 label-classes)))

(defn- swap-mapping [incumbent mapping]
  (if (> (count mapping) (count incumbent)) mapping incumbent))

(defn- check-edges [mapping v w graph1 graph2]
  (and
   (if (rel/is-disj-node? v graph1)
     (cond
       ;; For OR nodes, they must have at least one mapped child
       (= "or" (get-in graph1 [:vertices v]))
       (< 1 (count (filter (fn [[node label]]
                             (some (fn [[m]]
                                     (when (and (= m node) (= label #{:or}))
                                       m))
                                   mapping))
                           (get-in graph1 [:edges v]))))
       ;; For root nodes, all children must be mapped
       (= "root" (get-in graph1 [:vertices v]))
       (every? (fn [[node]]
                 (some (fn [[m]]
                         (when (= m node)
                           m))
                       mapping))
               (get-in graph1 [:edges v]))
       ;; If the given node is part of a disjunction, it must have at least one mapped ancestor
       ;; that is NOT part of a disjunction subgraph
       :else (some #(when (and (some (fn [m] (when (= % (first m)) m)) mapping)
                               (not (rel/is-disj-node? % graph1)))
                      %)
                   (keys (get-in graph1 [:redges v]))))
     true)
   (if (rel/is-disj-node? w graph2)
     (cond
       (= "or" (get-in graph2 [:vertices w]))
       (< 1 (count (filter (fn [[node label]]
                             (some (fn [[_ m]]
                                     (when (and (= m node) (= label #{:or}))
                                       m))
                                   mapping))
                           (get-in graph2 [:edges w]))))
       (= "root" (get-in graph2 [:vertices w]))
       (every? (fn [[node]]
                 (some (fn [[_ m]]
                         (when (= m node)
                           m))
                       mapping))
               (get-in graph2 [:edges w]))
       :else (some #(when (and (some (fn [m] (when (= % (second m)) m)) mapping)
                               (not (rel/is-disj-node? % graph2)))
                      %)
                   (keys (get-in graph2 [:redges w]))))
     true)
   ;; All incoming edges from matched nodes should also match 
   (every?
    (fn [[m1 m2]]
      (= (get-in graph1 [:edges m1 v]) (get-in graph2 [:edges m2 w])))
    mapping)))

 (defn- search [future mapping graph1 graph2 incumbent]
  (let [m-count (count mapping)
        i-count (count @incumbent)]
    (swap! incumbent swap-mapping mapping)
    (when (> (calc-bound m-count future) i-count)
      (let [[class1 class2 :as label-class]
            (reduce #(cond
                       (not (rel/is-disj-node? (ffirst %1) graph1)) %1
                       (not (rel/is-disj-node? (ffirst %2) graph1)) %2
                       (and (rel/is-disj-node? (ffirst %1) graph1)
                            (not (#{"or" "root"}
                                  (get-in graph1 [:vertices (ffirst %1)])))) %1
                       (and (rel/is-disj-node? (ffirst %2) graph1)
                            (not (#{"or" "root"}
                                  (get-in graph1 [:vertices (ffirst %2)])))) %2
                       (#{"root"}
                        (get-in graph1 [:vertices (ffirst %1)])) %1
                       (#{"root"}
                        (get-in graph1 [:vertices (ffirst %2)])) %2
                       (> (max (count (first %2)) (count (second %2)))
                          (max (count (first %1)) (count (second %2)))) %2
                       :else %1)
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
              (search new-future (conj mapping [v w]) graph1 graph2 incumbent)
              #_(lasync/execute pool
                                #(search new-future (conj mapping [v w]) graph1 graph2 incumbent)))))
        (let [new-class1 (disj class1 v)
              new-future (into [] (remove #(= % label-class)) future)]
          (if (seq new-class1)
            (search (conj new-future [new-class1 class2]) mapping graph1 graph2 incumbent)
            #_(lasync/execute pool
                              #(search (conj new-future [new-class1 class2]) mapping graph1 graph2 incumbent))
            (search new-future mapping graph1 graph2 incumbent)
            #_(lasync/execute pool
                              #(search new-future mapping graph1 graph2 incumbent))))))))


 (defn find-mcs+mapping [graph1 graph2]
  (let [incumbent (atom [])
        classes (init-label-groups graph1 graph2)]
    (search classes [] graph1 graph2 incumbent)
                        ;(lasync/execute pool #(search classes [] graph1 graph2 incumbent))
    (while (> (:activeCount (lasync/stats pool)) 0)
      (Thread/sleep 100)
      (println (str "Incumbent size: " (count @incumbent)
                    " active searches: " (:activeCount (lasync/stats pool)))))
    (let [mapping @incumbent
          [new-nodes node-map] (transduce
                                (comp (map first)
                                      (map #(vector (get-in graph1 [:vertices %]) %))
                                      (map #(vector (gensym (first %)) (first %) (second %))))
                                (completing (fn [[new-nodes node-map] [new-node type old-node]]
                                              [(conj new-nodes [new-node type])
                                               (assoc node-map old-node new-node)]))
                                [[] {}]
                                mapping)
          rev-node-map (set/map-invert node-map)]
      (transduce
       (comp
        (map-indexed (fn [idx new-node]
                       [new-node (nth mapping idx)]))
        (map (fn [[new-node [v] :as data]]
               (conj data
                     (reduce
                      (fn [[edges cmap] [to label]]
                        (if-let [to (get node-map to)]
                          [(assoc edges to label)
                           (update cmap label
                                   #(conj (or % #{})
                                          [(first new-node) to]))]
                          [edges cmap]))
                      [{} {}]
                      (get-in graph1 [:edges v])))))
        (map (fn [[_ [v] :as data]]
               (conj data
                     (reduce
                      (fn [redges [from label]]
                        (if (contains? node-map from)
                          (assoc redges (get node-map from) label)
                          redges))
                      {}
                      (get-in graph1 [:redges v]))))))
       (fn ([common [[new-node type] [v] [edges cmap] redges]]
            (-> common
                (update :vertices assoc new-node type)
                (update :edges #(if (not-empty edges) (assoc % new-node edges) %))
                (update :redges #(if (not-empty redges) (assoc % new-node redges) %))
                (update :terms #(if-let [terms (seq (get-in graph1 [:terms v]))]
                                  (assoc % new-node (vec terms))
                                  %))
                (update :constraint-map #(merge-with into % cmap))))
         ([common]
          (let [remove-nodes (into #{} ;; We might end with nodes with no edges or disjunction nodes that are no longer part of a disjunction, remove them
                                   (comp
                                    (filter
                                     (fn [[node type]]
                                       (or (and (empty? (get-in common [:edges node]))
                                                (empty? (get-in common [:redges node])))
                                           (and (rel/is-disj-node? (get rev-node-map node) graph1)
                                                (not (#{"or" "root"} type))
                                                (nil? (some #(when (rel/is-disj-node?
                                                                    (get rev-node-map (first %)) graph1)
                                                               %)
                                                            (get-in common [:redges node])))))))
                                    (map first))
                                   (:vertices common))
                common (reduce
                        (fn [graph node]
                          (rel/delete-node node graph))
                        common
                        remove-nodes)
                mapping (remove (fn [[v]] (contains? remove-nodes (get node-map v))) mapping)]
            [mapping common])))
       {:edges {} :vertices {}}
       new-nodes))))

(defn merge-rules [graph1 graph2]
  (let [[mapping mcs] (find-mcs+mapping graph1 graph2)
        terms (into []
                    (comp (map val)
                          cat
                          (filter #(#{:named :var} (:type %))))
                    (:terms mcs))]
    ))
