(ns datapog.utils.combinator)

(defn- crawl
  [f l]
    (map #(if (coll? %)
            (let [l2 (crawl f %)]
                (if (vector? %)
                  (vec l2)
                  l2))
            (f %))
         l))

(defn- replace-syms [syms xform]
  "Recursively go through an xform, replacing symbols using the given lookup map"
  (crawl #(or (get syms (if (symbol? %)
                          (-> % name symbol)
                          %))
              %) xform))

(defmacro defparser [name scanner dispatch-map body]
  (let [state-sym (gensym)
        body (replace-syms {'state state-sym} body)]
    `(def ^:private ~name
       (fn [text# ~state-sym]
         (let [[next-token# text#] (scanner text#)
               new-state# ~@body]
           (if-let [next-parser# (get ~dispatch-map (:type next-token#))]
             (next-parser# text# new-state#)
             (throw (Exception.
                     (str "Unexpected " next-token ", expected one of "
                          (keys ~dispatch-map))))))))))
