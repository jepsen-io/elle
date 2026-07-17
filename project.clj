(defproject elle "0.2.7"
  :description "Black-box transactional consistency checker based on cycle detection"
  :url "https://github.com/jepsen-io/elle"
  :license {:name "EPL-2.0 OR GPL-2.0-or-later WITH Classpath-exception-2.0"
            :url "https://www.eclipse.org/legal/epl-2.0/"}
  :dependencies [[org.clj-commons/slingshot "0.13.0"]
                 [com.aphyr/bifurcan-clj "0.1.4"]
                 ; Has to be here for our java classes to use Clojure
                 [org.clojure/clojure "1.12.5"]
                 [dom-top "1.0.11"]
                 [hiccup "2.0.0"]
                 [org.clojure/tools.logging "1.3.1"]
                 [rhizome "0.2.9"]
                 [io.jepsen/history "0.1.8"]
                 [io.jepsen/generator "0.1.2"]
                 [jepsen.txn "0.1.3"]]
  :java-source-paths ["src"]
  ; We need jepsen.history.Op available before we can compile our java code
  ;:prep-tasks [["compile" "jepsen.history"]
  ;             "javac"
  ;             "compile"]
  :javac-options ["--release" "21"
                  ]
  :profiles {:dev {:dependencies [[com.gfredericks/test.chuck "0.2.15"]
                                  [io.jepsen/history.sim "0.1.3"]
                                  [org.clojure/test.check "1.1.3"]
                                  [spootnik/unilog "0.7.32"
                                   :exclusions
                                   [com.fasterxml.jackson.core/jackson-core]]]}}
  :jvm-opts ["-server"
             "-XX:-OmitStackTraceInFastThrow"
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
