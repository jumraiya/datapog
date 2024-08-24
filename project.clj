(defproject datapog "0.1.0-SNAPSHOT"
  :description "FIXME: write description"
  :url "http://example.com/FIXME"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[org.clojure/clojure "1.12.0-rc1"]
                 [com.github.flow-storm/flow-storm-dbg "3.17.2"]
                 [nubank/matcher-combinators "3.9.1"]
                 [tolitius/lasync "0.1.25"]
                 [com.phronemophobic/clj-graphviz "0.6.4"]
                 [com.phronemophobic.cljonda/graphviz-darwin-aarch64 "2.50.0-0.9.5"]]
  :main ^:skip-aot datapog.core
  :target-path "target/%s"
  :profiles {:uberjar {:aot :all
                       :jvm-opts ["-Dclojure.compiler.direct-linking=true"]}})
