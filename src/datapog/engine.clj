(ns datapog.engine)


(defn eval-pred [pred program]
  (transduce
   (comp
    (filter #(= pred (-> % :head :pred)))
    (map #((:rule-fn %) program)))
   (completing
    into)
   []
   (:rules program)))

(defn eval-rule-incr [{:keys [rule-fn]} program]
  (transduce
   (comp
    (map (fn [[relation facts]]
           (rule-fn (assoc-in program [:facts relation] facts)))))
   (completing into)
   []
   (:deltas program)))

(defn eval-pred-incr [pred program]
  (transduce
   (comp
    (filter #(= pred (-> % :head :pred)))
    (map #(eval-rule-incr % program)))
   (completing into)
   []
   (:rules program)))

(defn compile-rule [program {:keys [head body]}]
  (let [program (gensym)
        pred-syms (into [] (comp (remove #(#{:eq :lte :gte :lt :gt} (:pred %))) (map #(vector (:pred %) (gensym)))) body)
        term-data (transduce
                   (comp
                    (remove #(#{:eq :lte :gte :lt :gt} (:pred %)))
                    (map-indexed
                     (fn [pred-idx {:keys [_pred terms]}]
                       (into {}
                             (map-indexed
                              (fn [term-idx term]
                                (vector term-idx [term (list nth (-> pred-syms (nth pred-idx) second)
                                                             (if (= (:type term) :named)
                                                               -1
                                                               term-idx))])))
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
                      (assoc data :constraints
                             (transduce
                              (comp
                               (map
                                (fn [[term positions]]
                                  (case (:type term)
                                    :var (when (> (count positions) 1)
                                           `(= ~@(mapv #(-> data :term-paths (get %)) positions)))
                                    (:number :string) `(= ~@(mapv #(-> data :term-paths (get %)) positions) ~(:val term)))))
                               (filter some?))
                              (completing conj)
                              []
                              (:term-pos data)))))
                   {:term-pos {} :term-paths {} :offset 0}
                   body)
        term-data (reduce
                   (fn [data {:keys [pred terms]}]
                     (update data :constraints conj
                             `(~(case pred :eq = :lte <= :gte >= :gt > :lt <)
                               ~@(mapv #(if (= :var (:type %))
                                          (-> data :term-paths
                                              (get (-> (:term-pos data) (get %) first)))
                                          (:val %))
                                       terms))))
                   term-data
                   (filter #(#{:eq :lte :gte :lt :gt} (:pred %)) body))
        for-clause (-> []
                       (into
                        (comp (map #(vector `(~(second %) (get-in ~program [:facts ~(first %)])))) cat cat) pred-syms)
                       (conj :when `(and ~@(:constraints term-data))))
        projection (mapv #(get-in term-data [:term-paths (first (get-in term-data [:term-pos %]))]) (:terms head))]
    ;; `(fn [~program]
    ;;    (for ~for-clause
    ;;      ~projection))
    (eval
     `(fn [~program]
        (for ~for-clause
          ~projection)))))

(defn validate+compile-program [program]
  (transduce
   (map-indexed
    (fn [idx rule]
      [idx (compile-rule program rule)]))
   (completing
    (fn [pr [idx rule-fn]]
      (update-in pr [:rules idx] assoc :rule-fn rule-fn)))
   program
   (:rules program)))

(defn semi-naive-eval [program]
   (let [program (transduce
                  (map (fn [[pred]]
                         [pred (eval-pred pred program)]))
                  (fn ([program]
                       (update program :facts merge (:deltas program)))
                    ([program [pred new-facts]]
                     (assoc-in program [:deltas pred] new-facts)))
                  program
                  (:preds program))]
     (loop [prog program]
       (let [old-deltas (:deltas prog)
             new-deltas (transduce
                         (comp
                          (map
                           (fn [[pred]]
                             [pred (eval-pred-incr pred (assoc prog :deltas old-deltas))]))
                          (map (fn [[pred rels]]
                                 [pred
                                  (remove
                                   (fn [r]
                                     (some? (some #(= r %) (get-in prog [:facts pred]))))
                                   rels)])))
                         (completing (fn [data [pred rels]]
                                       (assoc data pred rels)))
                         {}
                         (:preds prog))
             prog (-> prog
                      (update :facts (fn [fs]
                                       (reduce
                                        (fn [f [pred rels]]
                                          (update f pred into rels))
                                        fs new-deltas)))
                      (assoc :deltas new-deltas))]
         (if (every? empty? (-> prog :deltas vals))
           prog
           (recur prog))))))

