(ns compute.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
            [datascript.query :as dq]
            [datascript.arrays :as da]
            [clojure.set :as set])
  (:import (datascript.query Context)))

(defn replace-query-vars
  [x]
  (if (and (symbol? x) (= \? (first (str x))))
    '_
    x))

(defn pattern?
  [node]
  (= datascript.parser.Pattern (type node)))

(defn predicate?
  [node]
  (= datascript.parser.Predicate (type node)))

(defn variable?
  [node]
  (= datascript.parser.Variable (type node)))

(defn constant?
  [node]
  (= datascript.parser.Constant (type node)))

(defn placeholder?
  [node]
  (= datascript.parser.Placeholder (type node)))

(defn find-rel?
  [node]
  (= datascript.parser.FindRel (type node)))

(defn =nth
  [n x y]
  (= x (nth y n)))

(defn pattern-clause->pred
  [pattern]
  (let [p (:pattern pattern)
        [e a v] p
        [e' a' v'] (mapv :value p)]
    (if (constant? e)
      (if (constant? a)
        (if (constant? v)
          #(and (=nth 1 e' %) (=nth 2 a' %) (=nth 3 v' %))
          #(and (=nth 1 e' %) (=nth 2 a' %)))
        (if (constant? v)
          #(and (=nth 1 e' %) (=nth 3 v' %))
          #(=nth 1 e' %)))
      (if (constant? a)
        (if (constant? v)
          #(and (=nth 2 a' %) (=nth 3 v' %))
          #(=nth 2 a' %))
        (if (constant? v)
          #(=nth 3 v' %)
          (constantly true))))))

(defn unparse-pattern
  [{[e a v] :pattern}]
  [(or (:symbol e) (:value e) '_) (or (:symbol a) (:value a) '_) (or (:symbol v) (:value v) '_)])

(defn compile-query
  [query-def]
  (let [[name query] query-def]
    {:name name
     :query `'~query
     :query-ast (dp/parse-query query)
     :facts #{}}))

(defn compile-rule
  [rule-def]
  (let [[name query _ rhs] rule-def
        cq (compile-query [name query])
        preds (into {} (->> cq :query-ast :qwhere (map (fn [p] [`'~(unparse-pattern p) (pattern-clause->pred p)]))))
        rhs-args (->> cq :query-ast :qfind :elements (map :symbol))
        rhs-fn `(fn [~@rhs-args]
                  ~rhs)]
    (assoc cq :preds preds
              :rhs-fn rhs-fn)))

(defmacro defrules
  [name rules]
  (let [cr (mapv compile-rule rules)]
    `(def ~name
       ~cr)))

(defrules rs
  [[::r1
    [:find ?e
     :where
     [?e :a 1]]
    =>
    [[:db/add! ?e :one true]]]

   [::r2
    [:find ?e ?v
     :where
     [?e :a ?v]
     [?e :one true]]
    =>
    (println ?e ?v)]])


(defn create-session
  [& rulesets]
  {:rules (vec (mapcat identity rulesets))
   :pending-tx-data #{}})

(defn run-rule
  [fact rule]
  (let [triggered? (loop [[[pattern pred] & preds] (:preds rule)]
                     #_(println pattern fact ((or pred (constantly nil)) fact))
                     (if (nil? pred)
                       false
                       (if (pred fact)
                         true
                         (recur preds))))]
    (if triggered?
      (let [op (first fact)
            update-fn (if (= :db/retract op) disj conj)
            facts (update-fn (:facts rule) (vec (rest fact)))
            rule (assoc rule :facts facts)
            bindings (d/q (:query rule) facts)
            existing-bindings (set (set (-> rule :activations keys)))
            new-bindings (set/difference bindings existing-bindings)
            retracted-bindings (set/difference existing-bindings bindings)
            rule (if (not-empty retracted-bindings)
                   (let [tx-data (set (->> retracted-bindings
                                           (mapcat (:activations rule))
                                           (filter #(not= :db/add! (first %)))
                                           (map #(assoc % 0 :db/retract))))
                         activations (apply dissoc (:activations rule) retracted-bindings)]
                     (-> rule
                         (assoc :activations activations)
                         (update :tx-data concat tx-data)))
                   rule)
            rule (if (not-empty new-bindings)
                   (let [activations (into {} (map (juxt identity #(apply (:rhs-fn rule) %)) new-bindings))
                         tx-data (set (mapcat val activations))]
                     (-> rule
                         (update :activations merge activations)
                         (update :tx-data concat tx-data)))
                   rule)]
        rule)
      rule)))


(defn transact1
  [session fact]
  (let [rules (mapv (partial run-rule fact) (:rules session))]
    (assoc session :rules rules)))

(defn transact
  [session tx-data]
  (loop [session (reduce transact1 session tx-data)]
    (let [tx-data (reduce set/union
                          #{}
                          (map :tx-data (:rules session)))
          session (update session :rules #(mapv (fn [r] (dissoc r :tx-data)) %))]
      #_(println tx-data)
      #_(clojure.pprint/pprint session)
      (if (not-empty tx-data)
        (recur (reduce transact1 session tx-data))
        session))))





