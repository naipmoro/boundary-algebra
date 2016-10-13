(defproject naipmoro/boundary-algebra "0.1.0"
  :description "elements of boundary algebra"
  :license {:name "Eclipse Public License"
            :url "http://www.eclipse.org/legal/epl-v10.html"} 
  :dependencies [[org.clojure/clojure "1.9.0-alpha13"]
                 [org.clojure/math.combinatorics "0.1.3"]
                 [net.mikera/core.matrix "0.55.0"]
                 [net.mikera/vectorz-clj "0.45.0"]
                 [com.velisco/tagged "0.4.1"]]
  :jvm-opts ^:replace ["-Xmx512m" "-server"]
  :repl-options {:init-ns naipmoro.boundary-algebra.core
                 :init (require 'naipmoro.boundary-algebra.core)} 
  :profiles {:dev {:dependencies [[criterium "0.4.4"]]} })
