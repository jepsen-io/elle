(defproject elle "0.1.3-SNAPSHOT"
  :description "Black-box transactional consistency checker, based on cycle detection"
  :url "https://github.com/jepsen-io/elle"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[slingshot "0.12.2"]
                 [dom-top "1.0.5"]
                 [hiccup "1.0.5"]
                 [knossos "0.3.7"
                  :exclusions [org.slf4j/slf4j-log4j12]]
                 [org.clojure/tools.logging "0.6.0"]
                 [rhizome "0.2.9"]
                 [jepsen.txn "0.1.2"]
                 [io.lacuna/bifurcan "0.1.0"]]
  :profiles {:dev {:dependencies [[org.clojure/clojure "1.10.1"]
                                  [spootnik/unilog "0.7.24"]]}}
  :jvm-opts ["-server"
             ;"-XX:-OmitStackTraceInFastThrow"
             ;"-XX:+PrintGC"
             ]
  :repl-options {:init-ns elle.core}
  :test-selectors {:default (fn [m] (not (or (:perf m)
                                             (:interactive m)
                                             (:overflow m))))
                   :all         (fn [m] true)
                   :perf        :perf
                   :overflow    :overflow
                   :interactive :interactive})
