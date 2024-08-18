(ns datapog.utils.rel-algebra
  "Utility functions to perform relational algebra operations on ASTs"
  [:require [clojure.walk :as w]])


(defn- comp-atoms [{a :pred} {b :pred}]
  (cond (= :or a) 1
        (= :or b) -1
        (and (keyword? a) (string? b)) 1
        (and (keyword? b) (string? a)) -1
        :else (compare a b)))

(defn- sort-conjunction [conjunction]
  (w/postwalk
     (fn [r]
       (if (and (map? r) (= :or (:pred r)))
         (update r :terms #(mapv
                            (fn [cnjn]
                              (sort-conjunction cnjn))
                            %))
         r))
     (sort comp-atoms conjunction)))

(defn gen-dep-graph [program rule-body]
  (let [relations (into [] (comp (remove #(#{:eq :lte :gte :lt :gt :or} (:pred %))) (map #(vector (gensym (:pred %)) (:pred %)))) rule-body)
        rel-map (into {} relations)
        build-constraints (fn [rel-map op constraint]
                            (let [[rel & rels]
                                  (sort-by #(if (sequential? %)
                                              (get rel-map (first %)) "zz")
                                           constraint)]
                              (transduce
                               (map
                                (fn [r]
                                  [[(first rel) (if (sequential? r) (first r) :const)]
                                   [op [(get rel-map (first rel)) (second rel)]
                                    (if (sequential? r)
                                      [(get rel-map (first r)) (second r)]
                                      r)]]))
                               (completing conj)
                               []
                               rels)))
        term-data (transduce
                   (comp
                    (remove #(#{:eq :lte :gte :lt :gt :or} (:pred %)))
                    (map-indexed
                     (fn [rel-idx {:keys [_pred terms]}]
                       (into {}
                             (map-indexed
                              (fn [term-idx term]
                                (vector term-idx [term [(-> relations (nth rel-idx) first)
                                                        (if (= (:type term) :named)
                                                          -1
                                                          term-idx)]])))
                             terms))))
                   (fn
                     ([data indices]
                      (-> data
                          (update :term-pos
                                  (fn [pos]
                                    (reduce (fn [pos [idx [term]]]
                                              (update pos term #(conj (if (nil? %) [] %) (+ idx (:offset data)))))
                                            pos indices)))
                          (update :term-paths
                                  (fn [paths]
                                    (reduce
                                     (fn [paths [idx [_ path]]]
                                       (assoc paths (+ idx (:offset data)) path))
                                     paths
                                     indices)))
                          (update :offset + (count indices))))
                     ([data]
                      (transduce
                       (comp
                        (map
                         (fn [[term positions]]
                           (case (:type term)
                             :var (when (> (count positions) 1)
                                    (mapv #(-> data :term-paths (get %)) positions))
                             (:number :string) (mapv #(-> data :term-paths (get %)) positions) (:val term))))
                        (filter some?))
                       (completing
                        (fn [data const]
                          (let [conditions (build-constraints rel-map = const)]
                            (-> data
                                (update :constraints conj (into [=] const))
                                (update :graph
                                    (fn [g]
                                      (reduce
                                       (fn [graph [path condition]]
                                         (-> graph
                                             (update-in (into [:edges] path) #(conj (or % #{}) condition))
                                             (update-in (into [:redges] (-> path reverse vec)) #(conj (or % #{}) condition))))
                                       g
                                       conditions)))))))
                       data
                       (:term-pos data))))
                   {:term-pos {} :term-paths {} :offset 0
                    :graph
                    {:vertices (into {} relations)
                     :edges {}}}
                   rule-body)
        term-data (transduce
                   (map
                    (fn [{:keys [pred terms]}]
                      (let [op (case pred :eq = :lte <= :gte >= :gt > :lt <)
                            values (mapv #(if (= :var (:type %))
                                            (->> (get-in term-data [:term-pos %])
                                                 (mapv (fn [pos]
                                                         (get-in term-data [:term-paths pos])))
                                                 sort first)
                                            (:val %))
                                         terms)
                            conditions (build-constraints rel-map op values)]
                        [op values conditions])))
                   (fn ([data [op values conditions]]
                        (-> data
                            (update :constraints conj
                                    [op values])
                            (update :graph
                                    (fn [g]
                                      (reduce
                                       (fn [graph [path condition]]
                                         (-> graph
                                             (update-in (into [:edges] path) #(conj (or % #{}) condition))
                                             (update-in (into [:redges] (-> path reverse vec)) #(conj (or % #{}) condition))))
                                       g
                                       conditions)))))
                     ([data]
                      (assoc-in data [:graph :constraint-map]
                                (reduce
                                 (fn [m [v1 edges]]
                                   (reduce
                                    (fn [m [v2 constraints]]
                                      (update m constraints #(conj (or % #{}) [v1 v2])))
                                    m
                                    edges))
                                 {}
                                 (get-in data [:graph :edges])))))
                   term-data
                   (filter #(#{:eq :lte :gte :lt :gt :or} (:pred %)) rule-body))]
    term-data))

(defn- merge-nodes
  "Given two nodes in two graphs, finds common edges between them and returns a 3-tuple of [new-common-vertex new-graph1 new-graph2]."
  [graph1 graph2 node1 node2]
  (let [edges1 (get-in graph1 [:edges node1])
        edges2 (get-in graph2 [:edges node2])
        common-edges (for [[edge1 constraints1] edges1
                           [edge2 constraints2] edges2
                           :when (= constraints1 constraints2)]
                       [edge1 edge2 constraints1])
        update-constraints (fn [cs parent child]
                             (into #{}
                                   (map
                                    (fn [c]
                                      (mapv #(if (and (sequential? %) (= (first %) parent))
                                               (assoc % 0 (name child)) %)
                                            c)))
                                   cs))]
    (when (seq common-edges)
      (let [parent-rel (get-in graph1 [:vertices node1])
            new-vertex (gensym "rel")
            rem-edges-1 (reduce #(dissoc %1 %2) edges1 (mapv first common-edges))
            rem-edges-2 (reduce #(dissoc %1 %2) edges2 (mapv second common-edges))]
        [(hash-map new-vertex (into {} (mapv
                                        (fn [[_ e cs]]
                                          [(gensym (get-in graph2 [:vertices e]))
                                           (update-constraints cs parent-rel new-vertex)])
                                        common-edges)))
         (-> graph1 (update :edges #(-> %
                                        (dissoc node1)
                                        (assoc new-vertex
                                               (reduce (fn [es [e cs]]
                                                         (assoc es e (update-constraints cs parent-rel new-vertex)))
                                                       {}
                                                       rem-edges-1))))
             (update :vertices (fn [v]
                                 (-> v
                                     (dissoc node1)
                                     (assoc new-vertex (name new-vertex))))))
         (-> graph2 (update :edges #(-> %
                                        (dissoc node2)
                                        (assoc new-vertex
                                               (reduce (fn [es [e cs]]
                                                         (assoc es e (update-constraints cs parent-rel new-vertex)))
                                                       {}
                                                       rem-edges-2))))
             (update :vertices dissoc node1)
             (update :vertices assoc new-vertex (name new-vertex)))]))))


(defn- get-common-subgraph
  "Tries to find and extract the maximum common graph for graph1,2 and starting on nodes 1,2 using BFS.
   Assumes graphs are topologically sorted."
  [graph1 graph2 node1 node2]
  (loop [common {} cur-1 node1 cur-2 node2 g1 graph1 g2 graph2]
    (let [adj1 (get-in graph1 [:edges node1])
          adj2 (get-in graph1 [:edges node1])])))
