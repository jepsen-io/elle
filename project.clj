(defproject elle "0.1.8-SNAPSHOT"
  :description "Black-box transactional consistency checker, based on cycle detection"
  :url "https://github.com/jepsen-io/elle"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[slingshot "0.12.2"]
                 [dom-top "1.0.9"]
                 [hiccup "1.0.5"]
                 [org.clojure/tools.logging "1.2.4"]
                 [rhizome "0.2.9"]
                 [io.jepsen/history "0.1.2"]
                 [jepsen.txn "0.1.2"]
                 [io.lacuna/bifurcan "0.2.0-alpha6"]]
  :java-source-paths ["src"]
  :javac-options ["-target" "1.8" "-source" "1.8"]
  :profiles {:dev {:dependencies [[com.gfredericks/test.chuck "0.2.14"]
                                  [org.clojure/clojure "1.11.1"]
                                  [org.clojure/test.check "1.1.1"]
                                  [spootnik/unilog "0.7.31"]]}}
  :jvm-opts ["-server"
             ;"-XX:-OmitStackTraceInFastThrow"
             ;"-XX:+PrintGC"
             ;"-agentpath:/home/aphyr/yourkit/bin/linux-x86-64/libyjpagent.so=disablestacktelemetry,exceptions=disable,delay=10000,usedmem=50"
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
