(ns naipmoro.boundary-algebra.core
  (:require [clojure.math.combinatorics :as combo]
            [clojure.core.reducers :as r]
            [clojure.core.matrix :as m]
            [clojure.java.io :as io]
            [clojure.spec :as s]
            [clojure.edn :as edn]
            [miner.tagged :as tag]           
            [naipmoro.boundary-algebra.wave :as wave])
  (:import  [naipmoro.boundary_algebra.wave BooleanWave])
  (:refer-clojure :exclude [associative? boolean?]))

(comment
  (do (require 'naipmoro.boundary-algebra.core)
     (in-ns 'naipmoro.boundary-algebra.core)
     (set! *print-length* 100))

  (require :reload-all 'naipmoro.boundary-algebra.core)
  )

(m/set-current-implementation :vectorz)

(defn separate
  "Given a 2-arity pred, an element e, and a coll, returns a vector 
   of 2 vectors: the first subvector will include all elements x in 
   coll that satisfy (pred e x); the second subvector will include 
   all elements y of coll that fail to satisfy (pred e y).
   (separate = 1 [2 1 3 1 1 4 4]) => [[1 1 1 1] [2 3 4 4]]
   (separate = 1 []) => [[1] []]
   (separate = 1 [1]) => [[1 1] []]
   (separate = 1 [2]) => [[1] [2]]"
  [pred e coll]
  (loop [in [], out [], coll coll]
    (if (empty? coll)
      [in out]
      (let [frst (first coll)]
        (if (pred e frst)
          (recur (conj in frst) out (rest coll))
          (recur in (conj out frst) (rest coll)))))))

(defn equivalence-classes [equiv-pred coll]
  "Given a 2-arity equivalence predicate equiv-pred and coll, 
   returns a vector of vectors, each subvector containing 
   equivalent elements of coll."
  (loop [classes [], coll coll]
    (if (empty? coll)
      classes
      (let [[yes no] (separate equiv-pred (first coll) coll)]
        (if (empty? no)
          (conj classes yes)
          (recur (conj classes yes) no))))))

(defn gray-code
  "Returns all possible k-tuples from #{0, 1, ... , n-1}"
  [n k]
  (combo/selections (range n) k))

(defn triples
  "Returns all triples from #{1, ... , n-1}. 
   Used in testing for associativity of boundary tables.
   (triples 3) => ((1 1 1) (1 1 2) (1 2 1) (1 2 2) 
                   (2 1 1) (2 1 2) (2 2 1) (2 2 2))"
  [n]
  (combo/selections (range 1 n) 3))

(def _ "Underscore will represent an empty slot" nil)

(def template-2i      [ [0 1]
                        [1 _] ])

(def template-2j      [ [0 1]
                        [1 _] ])

(def template-3i-void [ [0  1  2]
                        [1  0  _]
                        [2  _  0] ])

(def template-3i-bool [ [0  1  2]
                        [1  0  _]
                        [2  _  _] ])

(def template-3i      [ [0  1  2]
                        [1  _  _]
                        [2  _  _] ])

(def template-3j-idem [ [0  1  2]
                        [1  1  _]
                        [2  _  2] ])

(def template-3j-bool [ [0  1  2]
                        [1  1  _]
                        [2  _  _] ])

(def template-3j      [ [0  1  2]
                        [1  _  _]
                        [2  _  _] ])

(def template-4i-void [ [0  1  2  3]
                        [1  0  _  _]
                        [2  _  0  _]
                        [3  _  _  0] ])

(def template-4i-bool [ [0  1  2  3]
                        [1  0  _  _]
                        [2  _  _  _]
                        [3  _  _  _] ])

(def template-4i      [ [0  1  2  3]
                        [1  _  _  _]
                        [2  _  _  _]
                        [3  _  _  _] ])

(def template-4j-idem [ [0  1  2  3]
                        [1  1  _  _]
                        [2  _  2  _]
                        [3  _  _  3] ])

(def template-4j-bool [ [0  1  2  3]
                        [1  1  _  _]
                        [2  _  _  _]
                        [3  _  _  _] ])

(def template-4j      [ [0  1  2  3]
                        [1  _  _  _]
                        [2  _  _  _]
                        [3  _  _  _] ])

(def jtemplates [template-3j-idem template-3j-bool template-3j
                 template-4j-idem template-4j-bool template-4j])

(defn table-nth
  [table row col]
  (nth (nth table row) col))

(def upper-triangle (r/filter #(<= (first %) (second %))))

(defn open-slot
  [ttable]
  (r/filter #(nil? (table-nth ttable (first %) (second %)))))

;; (defn upper-triangle-slots-orig
;;   "Returns the 2d-indices of the open slots in the upper-triangle
;;    of a template table. Used for commutative tables."
;;   [ttable]
;;   (let [c (comp (open-slot ttable) upper-triangle)
;;         n (count ttable)
;;         idxs (combo/cartesian-product (range 1 n) (range 1 n))]
;;     (r/reduce conj [] (c idxs))))

(defn upper-triangle-slots
  "Returns the 2d-indices of the open slots in the upper-triangle
   of a template table. Used for commutative tables."
  [ttable]
  (let [c (comp (open-slot ttable) upper-triangle)
        n (count ttable)
        idxs (combo/cartesian-product (range 1 n) (range 1 n))]
    (into [] (c idxs))))

;; (defn possible-slots
;;   [optable]
;;   (let [n (dec (count optable))
;;         r (range 1 (count optable))]
;;     (combo/cartesian-product r r)))

;; (defn generate-rule
;;   [idxs perm]
;;   (zipmap idxs perm))

(defprotocol Fillable
  "Structure with empty nil slots"
  (fill [this rule] "Fill the slots according to a rule")
  (slots [this] "Return indices of empty slots")
  (sels [this] "Selections of all possible slot values")
  (rule [this sel] "Mapping from slots to a selection of values"))

(defrecord JuxtTemplate [template]
  Fillable
  (fill [this rule]
    (let [n (count template)
          arr (to-array-2d template)]
      (doseq [r (range n), c (range n)]
        (when-not (aget arr r c)
          (when-let [v (or (get rule [r c]) (get rule [c r]))]
            (aset arr r c v))))
      (vec (map vec arr))))
  (slots [this]
    (let [c (comp (open-slot template) upper-triangle)
          n (count template)
          idxs (combo/cartesian-product (range 1 n) (range 1 n))]
      (r/reduce conj [] (c idxs))))
  (sels [this]
    (let [n (count template)
          s (count (slots this))]
      (gray-code n s)))
  (rule [this perm] (zipmap (slots this) perm)))

(defrecord InclTemplate [template]
  Fillable
  (fill [this rule]
    (let [n (count template)
          arr (to-array-2d template)]
      (doseq [r (range n), c (range n)]
        (when-not (aget arr r c)
          (when-let [v (get rule [r c])]
            (aset arr r c v))))
      (vec (map vec arr))))
  (slots [this]
    (let [c (open-slot template)
          n (count template)
          idxs (combo/cartesian-product (range 1 n) (range 1 n))]
      (r/reduce conj [] (c idxs))))
  (sels [this]
    (let [n (count template)
          s (count (slots this))]
      (gray-code n s)))
  (rule [this perm] (zipmap (slots this) perm)))

(defprotocol Operation
  "Protocol for representations of boundary operations"
  (commutative? [this] "Tests commutativity of the operation")
  (associative-orig? [this] "Tests associativity of the operation")
  ;(lassociative? [this] "Tests Light's associativity of the operation")
  (associative? [this] "Tests Light's associativity* of the operation")
  (group? [this] "Tests whether the operation represents a group")
  (group*? [this] "Tests (w/light's assoc) whether the operation represents a group")
  (idempotent? [this] "Tests whether p p = p for all p")
  (void? [this] "Tests whether p p = 0 for all p"))

(defprotocol Algebraic
  "Protocol for algebraic structures"
  (isomorphic? [this other] "Tests whether two structures are isomorphic")
  (boolean? [this] "Tests whether structure is boolean")
  (brownian? [this] "Tests whether structure is brownian"))

(defn normal-form
  "Transforms a square N table or matrix into a matrix whose 
   first column = first row = [0 1 ... N-1]"
  [matrix]
  (let [m (m/matrix matrix)
        sm (sort m)
        tm (m/transpose sm)
        stm (sort tm)]
    (m/matrix (m/transpose stm))))


;; (defn row-check
;;   [table n i]
;;   (loop [j 0]
;;     (when (< j n)
;;       (if (not= (table-nth table i j) (table-nth table j i))
;;         false
;;         (recur (inc j))))))

(defn commutes?
  [table]
  (let [n (count table)
        row-check (fn [n i]
                    (loop [j 0]
                      (when (< j n)
                        (if (not= (table-nth table i j)
                                  (table-nth table j i))
                          false
                          (recur (inc j))))))]
    (loop [i 0]
      (if (= i n)
        true
        (if-not (nil? (row-check n i))
          false
          (recur (inc i)))))))


(defn associates?
  [table]
  (let [trpls (triples (count table))]
    (loop [ts trpls]
      (if-not (seq ts)
        true
        (let [t (first ts), x (first t), y (second t), z (nth t 2)]
          (if (not= (table-nth table (table-nth table x y) z)
                    (table-nth table x (table-nth table y z)))
            false
            (recur (rest ts))))))))

(defn latin-square?
  [matrix]
  (let [rows (m/rows matrix)
        cols (m/columns matrix)
        rows-cols (concat rows cols)]
    (loop [rc rows-cols]
      (if-not (seq rc)
        true
        (if-not (apply distinct? (first rc))
          false
          (recur (rest rc)))))))

(defn permutation->mapping
  "Given a permutation, returns a mapping,
   e.g., [3 1 2] => {1.0 3, 2.0 1, 3.0 2}.
   Keys are coerced into doubles to accord with 
   the vectorz implementation of matrix.core."
  [perm]
  (zipmap (map double (range 1 (inc (count perm)))) perm))

(defn permute-table
  "Given a matrix or table and a permutation mapping,
   returns a new matrix in normal form."
  [matrix pmap]
  (let [m (m/mutable matrix)
        n (m/row-count matrix)]
    (doseq [i (range n) j (range n) :let [v (m/select m i j)]]
      (m/set-selection! m i j (pmap v 0)))
    (normal-form m)))

(defn cayley-table
  [elements op]
  (let [n (count elements)
        m (m/new-matrix n n)]
    (doseq [x elements, y elements]
    (m/set-selection! m x y (op x y)))
     m))

(defn light-associative?
  "Light's associativity test, based on:
   https://gist.github.com/jfinkels/c33681e7f7b54421ea02"
  [m]
  (let [elements (range (m/row-count m)) 
        left (fn [a] (fn [x y] (m/mget m x (m/mget m a y))))
        right (fn [a] (fn [x y] (m/mget m (m/mget m x a) y)))]
    (loop [elems elements]
      (if-not (seq elems)
        true
        (let [a (first elems)]
          (if-not (m/equals (cayley-table elements (left a))
                            (cayley-table elements (right a)))
            false
            (recur (rest elems))))))))

(defn cayley-table-abridged
  [elements op]
  (let [n (count elements)
        m (m/new-matrix n n)]
    (doseq [x elements, y elements]
    (m/set-selection! m (dec x) (dec y) (op x y)))
     m))

(defn light-associative-abridged?
  "Light's associativity test adapted for the case of a known
   identity element 0 and a matrix in normal form. Only the
   square [(1,1)...(n,n)] needs to be tested."
  [matrix]
  (let [elements (range 1 (m/row-count matrix)) 
        left (fn [a] (fn [x y] (m/mget matrix x (m/mget matrix a y))))
        right (fn [a] (fn [x y] (m/mget matrix (m/mget matrix x a) y)))]
    (loop [elems elements]
      (if-not (seq elems)
        true
        (let [a (first elems)]
          (if-not (m/equals (cayley-table-abridged elements (left a))
                            (cayley-table-abridged elements (right a)))
            false
            (recur (rest elems))))))))

(extend-protocol Operation
  clojure.lang.Sequential
  (commutative? [table] (commutes? table))
  (associative-orig? [table] (associates? table))
  ;(lassociative? [table] (lassociative? (m/matrix table)))
  (associative? [table] (associative? (m/matrix table))) 
  (group? [table] (group? (m/matrix table)))
  (group*? [table] (group*? (m/matrix table)))

  mikera.matrixx.Matrix
  (commutative? [matrix] (m/symmetric? matrix))
  (associative-orig? [matrix]
    (let [trpls (triples (m/row-count matrix))]
    (loop [ts trpls]
      (if-not (seq ts)
        true
        (let [t (first ts),
              x (nth t 0), y (nth t 1), z (nth t 2)]
          (if (not= (m/mget matrix (m/mget matrix x y) z)
                    (m/mget matrix x (m/mget matrix y z)))
            false
            (recur (rest ts))))))))
  ;(lassociative? [matrix] (light-associative? matrix))
  (associative? [matrix] (light-associative-abridged? matrix))
  (group? [matrix] (and (associative? matrix) (latin-square? matrix)))
  (group*? [matrix] (and (associative? matrix) (latin-square? matrix)))
  (idempotent? [matrix]
    (loop [n (dec (m/row-count matrix))]
      (if (zero? n)
        true
        (if-not (= (m/mget matrix n n) (double n))
          false
          (recur (dec n))))))
  (void? [matrix]
    (loop [n (dec (m/row-count matrix))]
      (if (zero? n)
        true
        (if-not (zero? (m/mget matrix n n))
          false
          (recur (dec n)))))))

(extend-protocol Algebraic
  clojure.lang.Sequential
  (isomorphic? [table table2]
    (let [m (m/matrix table) m2 (m/matrix table2)]
      (isomorphic? m m2)))

  mikera.matrixx.Matrix
  (isomorphic? [matrix matrix2]
    (assert (= (m/shape matrix) (m/shape matrix2))
            "The dimensions of the 2 matrices are not equal.")
    (let [m (m/matrix matrix)
          n (m/row-count m)
          sels (combo/permutations (range 1 n))
          permaps (map permutation->mapping sels)]
      (loop [pmaps permaps]
        (if-not (seq pmaps)
          false
          (let [pmap (first pmaps)]
            (if (m/equals matrix (permute-table matrix2 pmap))
              (zipmap (map int (keys pmap)) (vals pmap))
              (recur (rest pmaps))
              )))))))

(defrecord BoundaryAlgebra [juxtaposition inclusion]
  Algebraic
  (isomorphic? [algebra algebra2]
    (assert (= (m/shape (:inclusion algebra)) (m/shape (:inclusion algebra2)))
            "The dimensions of the 2 algebras are not equal.")
    (let [incl (:inclusion algebra)
          incl2 (:inclusion algebra2)
          juxt (:juxtaposition algebra)
          juxt2 (:juxtaposition algebra2)
          n (m/row-count (:inclusion algebra))
          sels (combo/permutations (range 1 n))
          permaps (map permutation->mapping sels)]
      (loop [pmaps permaps]
        (if-not (seq pmaps)
          false
          (let [pmap (first pmaps)]
            (if (and (m/equals incl (permute-table incl2 pmap))
                     (m/equals juxt (permute-table juxt2 pmap)))
              (zipmap (map int (keys pmap)) (vals pmap))
              (recur (rest pmaps))
              ))))))
  (boolean? [algebra]
    (let [juxt (:juxtaposition algebra)
          incl (:inclusion algebra)
          n (m/row-count juxt)]
      (loop [elems (range 1 n)]
        (if-not (seq elems)
          false
          (let [v (first elems)]
            (if (and (= v (m/mget juxt v v))
                     (zero? (m/mget incl v v)))
              true
              (recur (rest elems))))))))
  (brownian? [algebra]
    (and (idempotent? (:juxtaposition algebra))
         (void? (:inclusion algebra)))))

(defn isomorphs
  "Given a collection of matrices or algebras, returns a vector of
   vectors, each subvector containing isomorphic matrices/algebras."
  [mats-or-algs]
  (equivalence-classes isomorphic? mats-or-algs))

(defn square-table?
  "Checks whether table is a square 2D structure"
  [table]
  (let [row-counts (set (map count table))]
    (and (contains? row-counts (count table))
         (= 1 (count row-counts)))))

;; Method for encoding BoundaryAlgebra records as EDN tagged literals,
;; to allow for writing them out to files and reading them back.
(defmethod print-method naipmoro.boundary_algebra.core.BoundaryAlgebra
  [this w] (tag/pr-tagged-record-on this w))

(defn obj->file
  "Writes the obj out to file"
  [obj f]
  (with-open [wtr (io/writer f)]
    (binding [*out* wtr, *print-length* nil]
      (pr obj))))

(defn file->obj
  "Reads the obj in from file"
  [f]
  (with-open [rdr (java.io.PushbackReader. (io/reader f))]
    (binding [*read-eval* false]
      (tag/read rdr))))

(defn create-template
  "Returns the most open operation template for a boundary algebra
   of k elements -- only the identity operation slots are filled."
  [k]
  (loop [t [(vec (range k))], i 1]
    (if (= i k)
      t
      (recur (conj t (vec (cons i (repeat (dec k) nil)))) (inc i)))))

(defn all-k-boundaries-orig
  "Returns a vector of all legal boundary algebras of k elements,
   grouped in isomorphic subvectors."
  [k]
  (let [temp (create-template k)
        itemp (->InclTemplate temp)
        jtemp (->JuxtTemplate temp)
        ips (sels itemp)
        jps (sels jtemp)
        irules (map #(rule itemp %) ips)
        jrules (map #(rule jtemp %) jps)
        its (map #(fill itemp %) irules)
        jts (map #(fill jtemp %) jrules)
        iassocs (filter associative-orig? its)
        jassocs (filter associative-orig? jts)
        algs (for [j jassocs i iassocs]
               (->BoundaryAlgebra j i))]
    (isomorphs algs)))



(defn all-k-boundaries
  "Returns a lazy seq of all legal boundary algebras of k elements."
  [k]
  (let [temp (create-template k)
        itemp (->InclTemplate temp)
        jtemp (->JuxtTemplate temp)
        itups (sels itemp)
        jtups (sels jtemp)
        irules (r/map #(rule itemp %))
        jrules (r/map #(rule jtemp %))
        its (r/map #(fill itemp %))
        jts (r/map #(fill jtemp %))
        iassocs (r/filter associative?)
        jassocs (r/filter associative?)
        itables (into [] ((comp iassocs its irules) itups))
        jtables (into [] ((comp jassocs jts jrules) jtups))]
    (for [j jtables i itables]
               (->BoundaryAlgebra j i))))

(defn all-isomorphic-k-boundaries
  "Returns a vector of all legal boundary algebras of k elements,
   grouped in isomorphic subvectors."
  [k]
  (isomorphs (all-k-boundaries k)))

;; (defn juxt-table
;;   "Creates a new JuxtTable"
;;   [table]
;;   {:pre [(square-table? table)]}
;;   (->JuxtTable table))

;; (defn incl-table
;;   "Creates a new InclTable"
;;   [table]
;;   {:pre [(square-table? table)]}
;;   (->InclTable table))

(comment ;check that every jtable is commutative

  (let [temp (->JuxtTemplate template-4j-bool)
        ps (sels temp)
        rules (map #(rule temp %) ps)
        tables (for [r rules]
                 (juxt-table (fill temp r)))]
    (every? commutative? tables))

  (let [temp (->InclTemplate template-3i)
        ps (sels temp)
        rules (map #(rule temp %) ps)
        ;; ts (map #(fill temp %) rs)
        ts (for [r rules]
             (m/matrix (fill temp r)))
        ass (filter associative? ts)
        isos (isomorphs ass)])

  (let [temp (->InclTemplate template-3i)
        ps (sels temp)
        rules (map #(rule temp %) ps)
        ts (map #(fill temp %) rules)
        ass (filter associative? ts)
        ms (map m/matrix ass)
        isos (isomorphs ms)]
    )
   ;; return all 3-boundary algebras
  (let [itemp (->InclTemplate template-3i)
        jtemp (->JuxtTemplate template-3j)
        ips (sels itemp)
        jps (sels jtemp)
        irules (map #(rule itemp %) ips)
        jrules (map #(rule jtemp %) jps)
        its (map #(fill itemp %) irules)
        jts (map #(fill jtemp %) jrules)
        iassocs (filter associative? its)
        jassocs (filter associative? jts)
        algs (for [j jassocs i iassocs]
               (->BoundaryAlgebra j i))]
    (isomorphs algs))

  ;; return all group 3-boundaries
  (let [itemp (->InclTemplate template-3i)
        jtemp (->JuxtTemplate template-3j)
        ips (sels itemp)
        jps (sels jtemp)
        irules (map #(rule itemp %) ips)
        jrules (map #(rule jtemp %) jps)
        its (map #(fill itemp %) irules)
        jts (map #(fill jtemp %) jrules)
        iassocs (filter group? its)
        jassocs (filter associative? jts)
        algs (for [j jassocs i iassocs]
               (->BoundaryAlgebra j i))]
    (isomorphs algs))
  
  );end comment

