(ns datapog.parser)


(def t-decl ::decl)

(def t-word ::word)

(def t-colon ::colon)

(def t-dash ::dash)

(def t-comma ::comma)

(def t-dot ::dot)

(def t-open-paren ::open-paren)

(def t-close-paren ::close-paren)

(def t-number ::number)

(def t-unknown ::unknown)

(def t-eof ::eof)

(def epsilon ::epsilon-transition)

(def end ::end)

(declare rel-args)

(declare decl)

(declare start)

(declare rule-body)

(declare term)

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

(defn- next-token [text]
  (if text
    (let [text (.trim text)
          [match decl open-paren close-paren colon dash dot comma word number whatever]
          (re-find #"(.decl)|(\()|(\))|(:)|(-)|(\.)|(,)|([a-zA-Z]+)|([0-9]+)|(.*)" text)]
      [(cond
         (some? decl) {:type t-decl}
         (some? open-paren) {:type t-open-paren}
         (some? close-paren) {:type t-close-paren}
         (some? colon) {:type t-colon}
         (some? comma) {:type t-comma}
         (some? dash) {:type t-dash}
         (some? dot) {:type t-dot}
         (some? word) {:type t-word :val word}
         (some? number) {:type t-number :val number}
         true (if (> (.length text) 0)
                {:type t-unknown :val whatever}
                {:type t-eof}))
       (if (and text match (> (.length text) (.length match)))
         (.substring text (.length match)))])
    [{:type t-eof}]))


(defmacro defstate [name dispatch-map body]
  (let [state-sym (gensym)
        token-sym (gensym)
        text-sym (gensym)
        body (replace-syms {'state state-sym 'token token-sym 'text text-sym} body)]
    `(def ^:private ~name
       (fn [~token-sym ~text-sym ~state-sym]
         (let [data# ~body
               [new-state# ~text-sym] (if (sequential? data#)
                                        data#
                                        [data# ~text-sym])
               [next-token# new-text#] (next-token ~text-sym)]
           (if-let [next-parser# (or (get ~dispatch-map (:type next-token#))
                                     (get ~dispatch-map epsilon))]
             (if (= next-parser# end)
               [new-state# ~text-sym]
               (next-parser# next-token# new-text# new-state#))
             (throw (Exception.
                     (str "Unexpected " next-token# " in " ~name ", expected one of "
                          (keys ~dispatch-map))))))))))



;; Rules

(defstate atom-end {epsilon end}
  (identity state))

(defstate term* {t-comma term t-close-paren atom-end}
  (update state :terms conj (:val token)))

(defstate term {t-word term* t-number term*}
  (if (nil? (:terms state))
      (assoc state :terms [])
      state))

(defstate atom-start {t-open-paren term}
  (assoc state :pred (:val token)))

(defstate fact {epsilon end}
  (assoc state ::fact (::atom state)))

(defstate rule-end {epsilon end}
  (identity state))

(defstate rule-body* {t-comma rule-body t-dot rule-end}
  (let [[a-tom text] (atom-start token text (hash-map))]
    [(update state ::rule-body conj a-tom) text]))

(defstate rule-body {t-word rule-body*}
  (if (nil? (::rule-body state))
      (assoc state ::rule-body [])
      state))

(defstate rule {t-dash rule-body}
  (assoc state ::rule-head (::atom state)))

(defstate rule-or-fact {t-dot fact t-colon rule}
  (let [[a-tom text] (atom-start token text (hash-map))]
    [(assoc state ::atom a-tom) text]))


;; Relations

(defstate rel-end {epsilon end}
  (identity state))

(defstate rel-arg-type* {t-comma rel-args t-close-paren rel-end}
  (assoc-in state [::rel-args (::rel-arg-name state)] (:val token)))

(defstate rel-arg-type {t-word rel-arg-type*}
  (identity state))

(defstate rel-arg-name {t-colon rel-arg-type}
  (assoc state ::rel-arg-name (:val token)))

(defstate rel-args {t-word rel-arg-name}
  (identity state))

(defstate rel-start {t-open-paren rel-args}
  (assoc state ::rel-name (:val token)))

(defstate decl {t-word rel-start}
  (identity state))


;; Starting state
(defstate start {t-eof end t-decl decl t-word rule-or-fact}
  (identity state))

(defn parse-program [body]
  (loop [program {:rules []} text body]
   (let [[state text] (start nil text {})
         program (cond
                   (some? (::rel-name state))
                   (assoc-in program
                             [:relations (::rel-name state)]
                             (::rel-args state))
                   (some? (::fact state))
                   (assoc-in program [:facts (-> state ::fact :pred)]
                             (-> state ::fact :terms))
                   (some? (::rule-head state))
                   (update program :rules conj [(::rule-head state) (::rule-body state)]))]
     (if (and text (> (.length text) 0))
       (recur program text)
       program)))
  ;(start nil body {})
  )
