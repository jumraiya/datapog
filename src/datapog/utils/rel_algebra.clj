(ns datapog.utils.rel-algebra
  "Utility functions to perform relational algebra operations on ASTs"
  (:require [clojure.walk :as w]
            [clojure.set :as set]))

(declare process-disjunction)

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

 (defn gen-dep-graph [program rule-body
                     & [term-data]]
  (let [prev-rels (or (:relations term-data) [])
        relations (into prev-rels
                        (comp (remove #(#{:eq :lte :gte :lt :gt :or} (:pred %)))
                              (map #(vector (gensym (:pred %)) (:pred %))))
                        rule-body)
        rel-idx-offset (count prev-rels)
        rel-map (into (or (-> term-data :graph :vertices) {}) relations)
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
                     (fn [rel-idx {:keys [pred terms]}]
                       (into {}
                             (map-indexed
                              (fn [term-idx term]
                                (let [[term term-idx] (if (= (:type term) :named)
                                                        (some #(when (= (:key term)
                                                                        (-> % second first))
                                                                 [(:val term) (first %)])
                                                              (map-indexed vector (get-in program [:relations pred])))
                                                        [term term-idx])]
                                  (vector term-idx [term [(-> relations (nth (+ rel-idx rel-idx-offset)) first)
                                                          term-idx]]))))
                             terms))))
                   (fn
                     ([data indices]
                      (-> data
                          (update :term-pos
                                  (fn [pos]
                                    (reduce (fn [pos [idx [term]]]
                                              (update pos term #(conj (or % #{}) (+ idx (:offset data)))))
                                            pos indices)))
                          (update :term-paths
                                  (fn [paths]
                                    (reduce
                                     (fn [paths [idx [_ path]]]
                                       (assoc paths (+ idx (:offset data)) path))
                                     paths
                                     indices)))
                          (update :offset + (inc (apply max (keys indices))))))
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
                   (or (and term-data (-> term-data
                                          (assoc :relations relations)
                                          (assoc-in [:graph :vertices] rel-map)))
                       {:term-pos {} :term-paths {} :offset 0
                        :relations relations
                        :graph {:vertices (into {} relations)
                                :edges {}}})
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
                   (filter #(#{:eq :lte :gte :lt :gt} (:pred %)) rule-body))
        term-data (reduce
                   #(process-disjunction program %1 %2)
                   term-data (filter #(= :or (:pred %)) rule-body))]
    term-data))

 (defn- process-disjunction [program term-data or-clause]
   (let [rel (gensym "or")
         [_ conjunctions]
         (reduce (fn [[offset cnjn-data] rule-body]
                   (let [data (gen-dep-graph program rule-body
                                             (assoc term-data :offset offset))
                         new-vertices (set/difference (-> data :graph :vertices keys set)
                                                      (-> term-data :graph :vertices keys set))
                         top-nodes (filter #(not (some (fn [e] (contains? e %))
                                                       (vals (reduce (fn [g v] (dissoc g v))
                                                                     (-> data :graph :edges)
                                                                     (-> term-data :graph :vertices keys)))))
                                           new-vertices)
                         [root-node data] (if (= 1 (count top-nodes))
                                            [(first top-nodes) data]
                                            (let [root (gensym "root")]
                                              [root (reduce
                                                     (fn [g node]
                                                       (-> g
                                                           (update-in [:graph :edges root] assoc #{} node)
                                                           (update-in [:graph :constraint-map #{}] #(conj (or % #{}) [root node]))))
                                                     data
                                                     top-nodes)]))
                         data (-> data
                               (assoc-in [:graph :edges rel root-node] #{:or})
                               (update-in [:graph :constraint-map #{:or}]
                                          #(conj (or % #{}) [rel root-node])))]
                     [(:offset data)
                      (conj cnjn-data data)]))
                 [(:offset term-data) []]
                 (:terms or-clause))]
                                                                                                           ;(println (pr-str conjunctions))
     (reduce
      (fn [data cnjn]
        (let [subgraph (:graph cnjn)]
          (-> data
              (update :term-pos (fn [pos] (merge-with #(into (set %1) %2)
                                                      pos (:term-pos cnjn))))
              (update :term-paths merge (:term-paths cnjn))
              (update-in [:graph :constraint-map] #(merge-with into % (:constraint-map subgraph)))
              (assoc :offset (:offset cnjn))
              (update-in [:graph :vertices] into (:vertices subgraph))
              (update-in [:graph :edges] #(merge-with into % (:edges subgraph)))
              (update-in [:graph :redges] #(merge-with into % (:redges subgraph))))))
      (-> term-data
          (assoc-in [:graph :vertices rel] "or")
          (update :constraints #(if (seq %2) (conj %1 %2) %1)
                  (into [`or]
                        (comp (map :constraints) (filter some?))
                        conjunctions)))
      conjunctions)))

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
