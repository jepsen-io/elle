(defproject elle "0.1.6-SNAPSHOT"
  :description "Black-box transactional consistency checker, based on cycle detection"
  :url "https://github.com/jepsen-io/elle"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[slingshot "0.12.2"]
                 [dom-top "1.0.8-SNAPSHOT"]
                 [hiccup "1.0.5"]
                 [org.clojure/tools.logging "1.2.4"]
                 [rhizome "0.2.9"]
                 [io.jepsen/history "0.1.0-SNAPSHOT"]
                 [jepsen.txn "0.1.2"]
                 [io.lacuna/bifurcan "0.2.0-alpha6"]]
  :profiles {:dev {:dependencies [[org.clojure/clojure "1.11.1"]
                                  [spootnik/unilog "0.7.30"]]}}
  :jvm-opts ["-server"
             "-XX:-OmitStackTraceInFastThrow"
             ;"-XX:+PrintGC"
             ]
  :repl-options {:init-ns elle.core}
  :test-selectors {:default (fn [m] (not (or (:perf m)
                                             (:interactive m)
                                             (:overflow m))))
                   :all         (fn [m] true)
                   :perf        :perf
                   :focus       :focus
                   :overflow    :overflow
                   :interactive :interactive})
