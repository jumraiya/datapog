(ns datapog.parser)


(def t-decl ::decl)

(def t-bang ::bang)

(def t-word ::word)

(def t-alnum ::alnum)

(def t-colon ::colon)

(def t-semicolon ::semicolon)

(def t-dash ::dash)

(def t-underscore ::underscore)

(def t-comma ::comma)

(def t-dot ::dot)

(def t-open-paren ::open-paren)

(def t-close-paren ::close-paren)

(def t-number ::number)

(def t-lte ::lte)

(def t-gte ::gte)

(def t-eq ::eq)

(def t-lt ::lt)

(def t-gt ::gt)

(def t-literal ::literal)

(def t-unknown ::unknown)

(def t-eof ::eof)

(def epsilon ::epsilon-transition)

(def end ::end)

(declare rel-args)

(declare decl)

(declare start)

(declare rule-body)

(declare rule-end)

(declare rule-body*)

(declare term)

(declare atom-start)

(declare disjunction)

(declare disjunction*)

(def ^:private token->term-type
  {t-word :var t-alnum :var t-literal :string t-number :number t-underscore :ignore})

(defn- crawl
  [f l]
  (map #(if (coll? %)
          (let [l2 (crawl f %)]
            (if (vector? %)
              (vec l2)
              l2))
          (f %))
       l))

(defn- replace-syms
  "Recursively go through an xform, replacing symbols using the given lookup map"
  [syms xform]
  (crawl #(or (get syms (if (symbol? %)
                          (-> % name symbol)
                          %))
              %) xform))
;; Lexer
(defn- next-token [text]
  (if text
    (let [text (.trim text)
          [match literal decl bang semicolon open-paren close-paren colon underscore dash dot comma alnum word number lte gte eq gt lt whatever]
          (re-find #"('[^']+')|(.decl)|(!)|(;)|(\()|(\))|(:)|(_)|(-)|(\.)|(,)|([a-zA-Z]+[0-9]+)|([a-zA-Z]+)|([0-9]+)|(<=)|(>=)|(=)|(>)|(<)|(.*)" text)]
      [(cond
         (some? literal) {:type t-literal :val (subs literal 1 (dec (.length literal)))}
         (some? bang) {:type t-bang}
         (some? semicolon) {:type t-semicolon}
         (some? decl) {:type t-decl}
         (some? open-paren) {:type t-open-paren}
         (some? close-paren) {:type t-close-paren}
         (some? colon) {:type t-colon}
         (some? underscore) {:type t-underscore}
         (some? comma) {:type t-comma}
         (some? alnum) {:type t-alnum :val alnum}
         (some? dash) {:type t-dash}
         (some? dot) {:type t-dot}
         (some? word) {:type t-word :val word}
         (some? lte) {:type t-lte :val :lte}
         (some? gte) {:type t-gte :val :gte}
         (some? eq) {:type t-eq :val :eq}
         (some? gt) {:type t-gt :val :gt}
         (some? lt) {:type t-lt :val :lt}
         (some? number) {:type t-number :val (Integer/parseInt number)}
         :else (if (> (.length text) 0)
                 {:type t-unknown :val whatever}
                 {:type t-eof}))
       (when (and text match (> (.length text) (.length match)))
         (.substring text (.length match)))])
    [{:type t-eof}]))


(defmacro defstate
  "Helper macro to build recursive descent parsers which consumes one (or more) token 
   for each state transition
   Defines a transition state as follows
   (defstate state-name {transition-map}
    {body}).
   Transition map defines transitions based on next token {token-1 new-state-1...}.
   Body is an xform whose evaluation result is used 
    - as the next accumulated state if a map is returned.
    - as the next accumuated state, remaining text if a tuple is returned.
   The latter functionality allows a state to consume more than one token.
   Three symbols in the body are mapped as follows
   state -> A map representing current accumulated state of parser
   token -> Current token
   text -> Remaining text to be parsed"
  [name dispatch-map body]
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
           (if-let [[next-parser# is-epsilon?#]
                    (if (contains? ~dispatch-map (:type next-token#))
                      [(get ~dispatch-map (:type next-token#)) false]
                      [(get ~dispatch-map epsilon) true])]
             (if next-parser#
               (if (= next-parser# end)
                 [new-state# ~text-sym]
                 (if is-epsilon?#
                   (next-parser# ~token-sym ~text-sym new-state#)
                   (next-parser# next-token# new-text# new-state#)))
               (throw (Exception.
                       (str "Unexpected " next-token# " in " ~name ", expected one of "
                            (keys ~dispatch-map)))))))))))



;; Rules

(defstate atom-end {epsilon end}
  (identity state))

(defstate term** {t-comma term t-close-paren atom-end}
  (update state :terms conj (assoc token :type ((:type token) token->term-type))))

(defstate named-term* {t-comma term t-close-paren atom-end}
  (update state :terms #(update % (-> % count dec) assoc :val (assoc token :type ((:type token) token->term-type)))))

(defstate named-term {t-word named-term* t-literal named-term* t-number named-term*}
  (update state :terms (fn [terms]
                         (update terms (-> terms count dec)
                                 #(assoc % :key (:val %) :type :named)))))

(defstate term* {t-colon named-term t-comma term t-close-paren atom-end}
  (update state :terms conj (assoc token :type ((:type token) token->term-type))))

(defstate term {t-word term* t-number term** t-underscore term** t-literal term**}
  (if (nil? (:terms state))
    (assoc state :terms [])
    state))


(defstate comp-end {epsilon end}
  (update state :terms conj (assoc token :type ((:type token) token->term-type))))

(defstate comp-op {t-word comp-end t-literal comp-end t-number comp-end}
  (-> state
      (assoc :terms [(:pred state)])
      (assoc :pred (:val token))
      ;(dissoc :pred)
      ))

(defstate pred-atom {epsilon term}
  (assoc state :pred (-> state :pred :val)))

(defstate atom-start* {t-open-paren pred-atom t-lte comp-op t-gte comp-op t-lt comp-op t-gt comp-op t-eq comp-op}
  (assoc state :pred (assoc token :type ((:type token) token->term-type))))

(defstate atom-start {t-word atom-start* t-alnum atom-start* epsilon atom-start* t-lte comp-op t-gte comp-op t-lt comp-op t-gt comp-op t-eq comp-op}
  (cond (= t-bang (:type token)) (assoc state :negated true)
        (= t-word (:type token)) (assoc state :pred
                                        (assoc token :type
                                               ((:type token) token->term-type)))
        :else state))

(defstate fact {epsilon end}
  (assoc state ::fact (::atom state)))

(defstate disjunction-end {t-dot rule-end t-comma rule-body epsilon end}
  (update state ::rule-body conj (hash-map :pred :or :terms (:terms state))))

(defstate disjunction** {t-bang disjunction* t-word disjunction*}
  (identity state))

(defstate disjunction* {t-semicolon disjunction** t-close-paren disjunction-end}
  (let [[data text] (rule-body* token text (hash-map ::rule-body []))]
    [(update state :terms conj (::rule-body data)) text]))

(defstate disjunction {t-word disjunction* t-bang disjunction*}
  (assoc state :terms []))

(defstate rule-end {epsilon end}
  (identity state))

(defstate rule-body* {t-comma rule-body t-dot rule-end epsilon end}
  (let [[a-tom text] (atom-start token text (hash-map))]
    [(update state ::rule-body conj a-tom) text]))

(defstate rule-body {t-word rule-body* t-alnum rule-body* t-bang rule-body* t-open-paren disjunction}
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
  (update state ::rel-args conj [(::rel-arg-name state) (:val token)]))

(defstate rel-arg-type {t-word rel-arg-type*}
  (identity state))

(defstate rel-arg-name {t-colon rel-arg-type}
  (assoc state ::rel-arg-name (:val token)))

(defstate rel-args {t-word rel-arg-name}
  (identity state))

(defstate rel-start {t-open-paren rel-args}
  (assoc state ::rel-name (:val token) ::rel-args []))

(defstate decl {t-word rel-start}
  (identity state))


;; Starting state
(defstate start {t-eof end t-decl decl t-word rule-or-fact t-alnum rule-or-fact}
  (identity state))

(defn- save-pred-terms-from-rule [program {::keys [rule-head rule-body]}]
  (let [check (fn [pred old-terms new-terms]
                (cond
                  (and (some? old-terms)
                       (= (count new-terms) (count old-terms))) new-terms
                  (nil? old-terms) new-terms
                  true new-terms
                  ;(not (keyword? pred)) (throw (Exception. (str "Inconsistent arity " new-terms "for " pred)))
                  ))]
    (reduce
     (fn [program {:keys [pred terms]}]
       (if (some? pred)
         (if (contains? (:relations program) pred)
           (do
             (check pred (get-in program [:relations pred]) terms)
             program)
           (assoc-in program [:preds pred]
                     (check pred (get-in program [:preds pred]) terms)))
         program))
     program
     (conj rule-body rule-head))))

(defn parse-program
  "Takes text representing a datalog program and parses it into a map containing rules, relation definitions and facts."
  [body]
  (loop [program {:rules [] :preds {}} text body]
    (let [[state text] (start nil text {})
          program (cond
                    (some? (::rel-name state))
                    (assoc-in program
                              [:relations (::rel-name state)]
                              (::rel-args state))
                    (some? (::fact state))
                    (update-in program [:facts (-> state ::fact :pred)]
                               #(conj (if (nil? %) [] %)
                                      (mapv :val (-> state ::fact :terms))))
                    (some? (::rule-head state))
                    (save-pred-terms-from-rule
                     (-> program
                         (update :rules conj {:head (::rule-head state)
                                              :body (::rule-body state)})
                         (update-in [:deps (-> state ::rule-head :pred)]
                                    #(conj (if (nil? %) [] %)
                                           (into [] (comp (map :pred) (filter some?))
                                                 (-> state ::rule-body)))))
                     state)
                    :else state)]
      (if (and text (> (.length text) 0))
        (recur program text)
        program)))
                                        ;(start nil body {})
  )
