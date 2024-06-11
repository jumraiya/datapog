(ns datapog.parser)


(def t-unknown ::unknown)

(def t-eof ::eof)

(defn- next-token []
  (if text
    (let [text (.trim text)
          [match options rest bar bracket-open bracket-close brace-open brace-close paren-open paren-close single-quote action-var word]
          (re-find #"(%)|(:[0-9]+)|(\|)|(\[)|(\])|(\{)|(\})|(\()|(\))|(\')|(\$[a-z]+)|([^\s\[\]\{\}\(\)']+)" text)]
      [(cond
         (-> options nil? not) {:type t-options-boundary :val "%"}
         (-> rest nil? not) {:type t-rest :val (Integer/parseInt (.substring rest 1))}
         (-> bar nil? not) {:type t-rest :val "|"}
         (-> bracket-open nil? not) {:type t-bracket-open :val "["}
         (-> bracket-close nil? not) {:type t-bracket-close :val "]"}
         (-> brace-open nil? not) {:type t-brace-open :val "{"}
         (-> brace-close nil? not) {:type t-brace-close :val "}"}
         (-> paren-open nil? not) {:type t-paren-open :val "("}
         (-> paren-close nil? not) {:type t-paren-close :val ")"}
         (-> single-quote nil? not) {:type t-single-quote :val "'"}
         (-> action-var nil? not) {:type t-action-var :val action-var}
         (-> word nil? not) {:type t-word
                             :val (cond
                                    (re-matches #"-?[0-9]+\.[0-9]+" word)
                                    (Float/parseFloat (re-matches #"-?[0-9]+\.[0-9]+" word))
                                    (re-matches #"-?[0-9]+" word)
                                    (Integer/parseInt (re-matches #"-?[0-9]+" word))
                                    true word)
                             }
         true (if (> (.length text) 0)
                {:type t-unknown}
                {:type t-eof}))
       (if (and text match (> (.length text) (.length match)))
         (.substring text (.length match)))])
    [{:type t-eof}]))

(defn parse-program [body]
  )
