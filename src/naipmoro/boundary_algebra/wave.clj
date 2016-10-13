(ns naipmoro.boundary-algebra.wave
  (:require [clojure.math.combinatorics :as combo]
            [clojure.core.reducers :as r]
            [clojure.core.matrix :as m]
            [clojure.spec :as s]))

(defn factors [n] 
  (filter #(zero? (rem n %)) (range 1 (inc (/ n 2)))))

(defn remove-repeats
  "Removes repeating sequences from a coll.
   (remove-repeat [1 1 1]) => [1]
   (remove-repeat [1 1 0 1 1 0]) => [1 1 0]
   (remove-repeat [1 1 0 1 0 0]) => [1 1 0 1 0 0] 
  "
  [coll]
  (let [factors (factors (count coll))]
    (loop [factors factors]
      (if-not (seq factors)
        coll
        (let [parts (partition (first factors) coll)
              fpart (first parts)]
          (if (every? #(= fpart %) parts)
            (vec fpart)
            (recur (rest factors))))))))

(defn gcd2 [a b]
  (loop [a (Math/abs a), b (Math/abs b)]
    (if (zero? b)
      a
      (recur b (mod a b)))))

(defn gcd [a b & more]
  (loop [g (gcd2 a b) more more]
    (if-not (seq more)
      g
      (recur (gcd2 g (first more)) (rest more)))))

(defn lcm2 [a b]
  (if (or (zero? a) (zero? b))
    0
    (Math/abs (* b (/ a (gcd2 a b))))))

(defn lcm
  ([] 1)
  ([a] a)
  ([a b & more]
   (if ((set (concat [a b] more)) 0)
     0
     (loop [l (lcm2 a b) more more]
       (if-not (seq more)
         l
         (recur (lcm2 l (first more)) (rest more)))))))

(defn rotate-right
  "cite: http://stackoverflow.com/a/20807015/3331307
   author: http://stackoverflow.com/users/2608009/omiel"
  [w n]
  (->> w
       cycle
       (drop n)
       (take (count w))
       vec))

(defprotocol IWaveForm
  "Protocol for binary cycles"
  (wave-form [wf]     "Returns the waveform")   
  (wave-cycle [wf]    "Returns the complete cycle of the waveform")     
  (wave-length [wf]   "Returns the waveform length")  
  (wave-pos [wf n]    "Returns the waveform position modulo n")   
  (wave-nth [wf n]    "Returns the nth value of the waveform")   
  (wave-take [wf n]   "Returns the first n values of the waveform")
  (wave-rotate [wf n] "Returns the waveform rotated n steps to the right")
  (wave-components [wf] "Returns the waveform's components")
  (wave-constant? [wf] "Tests whether the complete cycle of the waveform
                        is of length 1")
  )

(defrecord BooleanWave [form]
  IWaveForm
  (wave-form [w] (:form w))
  (wave-cycle [w] (remove-repeats (:form w)))
  (wave-length [w] (count (:form w)))
  (wave-pos [w n] (mod n (wave-length w)))
  (wave-nth [w n] (nth (cycle (:form w)) n))
  (wave-take [w n] (take n (cycle (:form w))))
  (wave-rotate [w n] (rotate-right (:form w) n))
  (wave-components [w] (map #(wave-rotate w %) (range (wave-length w))))
  (wave-constant? [w] (= 1 (count (set (:form w))))))

(defn wave [w] (->BooleanWave (remove-repeats w)))
