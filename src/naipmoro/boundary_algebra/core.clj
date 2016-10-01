(ns naipmoro.boundary-algebra.core
  (:require [clojure.math.combinatorics :as combo]
            [clojure.core.reducers :as r]
            [clojure.core.matrix :as m])
  (:refer-clojure :exclude [associative?]))

(comment
  (do (require 'naipmoro.boundary-algebra.core)
     (in-ns 'naipmoro.boundary-algebra.core)
     (set! *print-length* 100))

  (require :reload-all 'naipmoro.differences.core)
  )

(m/set-current-implementation :vectorz)

(defn- separate
  [equiv? e coll]
  (loop [in [e], out [], coll coll]
    (if (empty? coll)
      [in out]
      (let [frst (first coll)]
        (if (equiv? e frst)
          (recur (conj in frst) out (rest coll))
          (recur in (conj out frst) (rest coll)))))))

;; pred is a 2-arity equivalence predicate
(defn equivalence-classes [pred coll]
  (loop [classes [], coll coll]
    (if (empty? coll)
      classes
      (let [[yes no] (separate pred (first coll) (rest coll))]
        (if (empty? no)
          (conj classes yes)
          (recur (conj classes yes) no))))))

(defn gray-code
  [n k]
  (combo/selections (range n) k))

(defn triples
  [n]
  (combo/selections (range 1 n) 3))

(defn idx->2d-idx
  [i sqn]
  [(quot i sqn) (mod i sqn)])

(def _ nil)


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
  [table]
  (r/filter #(nil? (table-nth table (first %) (second %)))))

(defn upper-triangle-slots
  "Returns the 2d-indices of the open slots in optable"
  [table]
  (let [c (comp (open-slot table) upper-triangle)
        n (count table)
        idxs (combo/cartesian-product (range 1 n) (range 1 n))]
    (r/reduce conj [] (c idxs))))

(defn possible-slots
  [optable]
  (let [n (dec (count optable))
        r (range 1 (count optable))]
    (combo/cartesian-product r r)))

(defn generate-rule
  [idxs perm]
  (zipmap idxs perm))

(defprotocol Fillable
  "Structure with empty nil slots"
  (fill [this rule] "Fill the slots according to a rule")
  (slots [this] "Return indices of empty slots")
  (perms [this] "Permutations of all possible slot values")
  (rule [this perm] "Mapping from slots to a permuation of values"))

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
  (perms [this]
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
  (perms [this]
    (let [n (count template)
          s (count (slots this))]
      (gray-code n s)))
  (rule [this perm] (zipmap (slots this) perm)))

(defprotocol BoundaryOperation
  "Protocol for representations of boundary operations"
  (commutative? [this] "Tests commutativity of the operation")
  (associative? [this] "Tests associativity of the operation")
  (isomorphic? [this other] "Tests whether two operations are isomorphic")
  (group? [this] "Tests whether the operation represents a group")
  (idempotent? [this] "Tests whether p p = p for all p")
  (void? [this] "Tests whether p p = 0 for all p"))

(defprotocol Algebra
  "Protocol for algebras"
  (brownian? [this] "Tests whether algebra is brownian"))

(defn normal-form
  [matrix]
  (let [m (m/matrix matrix)
        sm (sort m)
        tm (m/transpose sm)
        stm (sort tm)]
    (m/matrix (m/transpose stm))))

(comment

  (defprotocol OptMatrix
   "Square matrix that represents an operation"
   (m-commutative? [this] "Tests commutativity of the operation")
   (m-associative? [this] "Tests associativity of the operation")
   (m-isomorphic? [this other] "Tests whether table is isomorphic to another table"))

); end comment

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

(defn latin-square? [matrix]
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



(extend-protocol BoundaryOperation
  clojure.lang.Sequential
  (commutative? [table] (commutes? table))
  (associative? [table] (associates? table))
  (isomorphic? [table table2]
    (let [m (m/matrix table) m2 (m/matrix table2)]
      (isomorphic? m m2)))
  (group? [table] (group? (m/matrix table)))

  mikera.matrixx.Matrix
  (commutative? [matrix] (m/symmetric? matrix))
  (associative? [matrix]
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
  (isomorphic? [matrix matrix2]
    (assert (= (m/shape matrix) (m/shape matrix2))
            "The dimensions of the 2 matrices are not equal.")
    (let [m (m/matrix matrix)
          n (m/row-count m)
          perms (combo/permutations (range 1 n))
          permaps (map permutation->mapping perms)]
      (loop [pmaps permaps]
        (if-not (seq pmaps)
          false
          (let [pmap (first pmaps)]
            (if (m/equals matrix (permute-table matrix2 pmap))
              (zipmap (map int (keys pmap)) (vals pmap))
              (recur (rest pmaps))
              ))))))
  (group? [matrix] (and (associative? matrix) (latin-square? matrix)))
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

(defrecord BoundaryAlgebra [juxtaposition inclusion]
  BoundaryOperation
  (isomorphic? [algebra algebra2]
    (assert (= (m/shape (:inclusion algebra)) (m/shape (:inclusion algebra2)))
            "The dimensions of the 2 algebras are not equal.")
    (let [incl (:inclusion algebra)
          incl2 (:inclusion algebra2)
          juxt (:juxtaposition algebra)
          juxt2 (:juxtaposition algebra2)
          n (m/row-count (:inclusion algebra))
          perms (combo/permutations (range 1 n))
          permaps (map permutation->mapping perms)]
      (loop [pmaps permaps]
        (if-not (seq pmaps)
          false
          (let [pmap (first pmaps)]
            (if (and (m/equals incl (permute-table incl2 pmap))
                     (m/equals juxt (permute-table juxt2 pmap)))
              (zipmap (map int (keys pmap)) (vals pmap))
              (recur (rest pmaps))
              ))))))

  Algebra
  (brownian? [algebra]
    (and (idempotent? (:juxtaposition algebra))
         (void? (:inclusion algebra)))))

(defn isomorphs
  "Given a collection of matrices, returns a vector of vectors,
   each subvector containing isomorphic matrices."
  [matrices]
  (equivalence-classes isomorphic? matrices))

(defn square-table?
  "Checks whether table is a square 2D structure"
  [table]
  (let [row-counts (set (map count table))]
    (and (contains? row-counts (count table))
         (= 1 (count row-counts)))))

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
        ps (perms temp)
        rules (map #(rule temp %) ps)
        tables (for [r rules]
                 (juxt-table (fill temp r)))]
    (every? commutative? tables))

  (let [temp (->InclTemplate template-3i)
        ps (perms temp)
        rules (map #(rule temp %) ps)
        ;; ts (map #(fill temp %) rs)
        ts (for [r rules]
             (m/matrix (fill temp r)))
        ass (filter associative? ts)
        isos (isomorphs ass)]
    )

  (let [temp (->InclTemplate template-3i)
        ps (perms temp)
        rules (map #(rule temp %) ps)
        ts (map #(fill temp %) rules)
        ass (filter associative? ts)
        ms (map m/matrix ass)
        isos (isomorphs ms)]
    )
   ;; return all 2-boundary algebras
  (let [itemp (->InclTemplate template-3i)
        jtemp (->JuxtTemplate template-3j)
        ips (perms itemp)
        jps (perms jtemp)
        irules (map #(rule itemp %) ips)
        jrules (map #(rule jtemp %) jps)
        its (map #(fill itemp %) irules)
        jts (map #(fill jtemp %) jrules)
        iassocs (filter associative? its)
        jassocs (filter associative? jts)
        algs (for [j jassocs i iassocs]
               (->BoundaryAlgebra j i))]
    (isomorphs algs))

  ;; return all group 2-boundaries
  (let [itemp (->InclTemplate template-3i)
        jtemp (->JuxtTemplate template-3j)
        ips (perms itemp)
        jps (perms jtemp)
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

