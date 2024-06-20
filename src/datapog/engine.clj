(ns datapog.engine)

(defn compile-rule [{:keys [head body] :as rule}]
  (let [program (gensym)
        pred-syms (into {} (map #(vector (:pred %) (gensym))) body)
        term-data (transduce
                   (map
                    (fn [{:keys [pred terms]}]
                      (into {}
                            (map-indexed
                             (fn [term-idx term]
                               (vector term-idx [term (list nth (get pred-syms pred) term-idx)])))
                            terms)))
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
                             (reduce
                              (fn [ret [term positions]]
                                (if (> (count positions) 1)
                                  (conj ret `(= ~@(mapv #(-> data :term-paths (get %)) positions)))
                                  ret))
                              [] (:term-pos data)))))
                   {:term-pos {} :term-paths {} :offset 0}
                   body)
        for-clause (-> []
                       (into
                        (comp (map #(vector `(~(second %) (get-in ~program [:facts ~(first %)])))) cat cat) pred-syms)
                       (conj :when `(and ~@(:constraints term-data))))
        projection (mapv #(get-in term-data [:term-paths (first (get-in term-data [:term-pos %]))]) (:terms head))]
    (eval
     `(fn [~program]
        (for ~for-clause
          ~projection)))))
