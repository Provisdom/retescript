(ns compute.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
            [datascript.query :as dq]
            [datascript.arrays :as da]
            [clojure.set :as set])
  (:import (datascript.query Context)))

(def game-over-q
  '[:find [?move ...]
    :where
    [?move :square _]])

(def move-request-q
  '[:find ?game ?player ?moves ?teaching-mode ?response-fn
    :where
    [?game :type ::Game]
    [?game :game-over false]
    [?game :current-player ?player]
    [?game :moves ?moves]
    [?game :teaching-mode ?teaching-mode]
    [?game :response-fn ?response-fn]])

(def move-response-q
  '[:find ?game ?request ?response ?player ?position
    :where
    [?game :type ::Game]
    [?request :type ::MoveRequest]
    [?request :game ?game]
    [?request :position ?position]
    [?response :type ::MoveResponse]
    [?response :game ?game]
    [?response :request ?request]
    [?response :position ?position]
    [?response :player ?player]])

(def cats-game
  '[:find ?game
    :where
    [?game :type ::Game]
    [not [?game :winner _]]
    [?game :moves ?moves]
    [(count ?moves) ?count]
    [(< ?count 9)]])

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
              :rhs-fn rhs-fn
              :activations {})))

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
    [[:db/add ?e :one true]]]

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
      (let [update-fn (if (= :db/retract (first fact)) disj conj)
            facts (update-fn (:facts rule) (vec (rest fact)))
            bindings (d/q (:query rule) facts)
            activations (into {} (map (juxt identity #(apply (:rhs-fn rule) %)) bindings))]
        (if (not-empty bindings)
          (-> rule
              (assoc :facts facts)
              (update :activations #(merge-with set/union %1 activations))
              (assoc :new-activations activations))
          (assoc rule :facts facts)))
      rule)))


(defn transact1
  [session fact]
  (let [rules (mapv (partial run-rule fact) (:rules session))]
    (assoc session :rules rules)))

(defn transact
  [session tx-data]
  (loop [session (reduce transact1 session tx-data)]
    (let [tx-data (reduce #(set/union %1 (set (mapcat val (:new-activations %2))))
                          #{}
                          (:rules session))]
      #_(clojure.pprint/pprint session)
      (if (not-empty tx-data)
        (recur (reduce transact1 (update session :rules #(mapv (fn [r] (dissoc r :new-activations)) %)) tx-data))
        session))))





