(ns compute.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
            [datascript.query :as dq]
            [datascript.arrays :as da]
            [clojure.set :as set]
            [compute.retescript.graph :as graph])
  (:import (datascript.query Context)))

(defn replace-query-vars
  [x]
  (if (and (symbol? x) (= \? (first (str x))))
    '_
    x))

(defn pattern?
  [node]
  (= datascript.parser.Pattern (type node)))

(defn function?
  [node]
  (= datascript.parser.Function (type node)))

(defn binding?
  [node]
  (or (pattern? node) (function? node)))

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

(defn unparse-pattern
  [{[e a v] :pattern}]
  [(or (:symbol e) (:value e) '_) (or (:symbol a) (:value a) '_) (or (:symbol v) (:value v) '_)])

(defn unparse-function
  [f]
  [(apply list (-> f :fn :symbol) (->> f :args (map #(or (:symbol %) (:value %))))) (-> f :binding :variable :symbol)])

(defn pattern-clause-binding-fn
  [pattern]
  (let [var->idx (->> (map vector pattern (range))
                      (filter (fn [[c _]] (dq/free-var? c)))
                      (map (fn [[c i]] [c i]))
                      (into {}))]
    `{:clause '~pattern
      :type :pattern
      :vars '~(-> var->idx keys set)
      :fn   (fn [x#]
              (when (dq/matches-pattern? '~pattern x#)
                (into {} (map (fn [[v# i#]] [v# (x# i#)]) '~var->idx))))}))

(defn function-clause-binding-fn
  [f args]
  (let [[body binding-var] f]
    `{:clause '~f
      :type :function
      :binding-var '~binding-var
      :args '~args
      :fn (fn [~@args] {'~binding-var ~body})}))


(defn compile-query
  [query-def]
  (let [[name query] query-def
        query-ast (dp/parse-query query)
        patterns (->> query-ast :qwhere (map (fn [p] `'~(unparse-pattern p))))]
    {:name      name
     :query     `'~query
     :query-ast query-ast
     :bindings  (->> query-ast
                     :qwhere
                     (filter pattern?)
                     (map (fn [p]
                            [`'~(unparse-pattern p)
                             `'{:vars ~(->> p :pattern (filter variable?) (map :symbol) set)
                                :bindings #{}}]))
                     (into {}))}))

(defn compile-rule
  [rule-def]
  (let [[name query _ & rhs] rule-def
        cq (compile-query [name query])
        binders (->> cq
                     :query-ast
                     :qwhere
                     (filter binding?)
                     (mapv (fn [p]
                             (cond
                               (pattern? p) (pattern-clause-binding-fn (unparse-pattern p))

                               (function? p) (function-clause-binding-fn (unparse-function p) (->> p :args (map :symbol) (filter dq/free-var?) vec))))))

        rhs-args (->> cq :query-ast :qfind :elements (mapv :symbol))
        rhs-fn `(fn [~@rhs-args]
                  ~@rhs)]
    (assoc cq :pattern-binders (->> binders (filter #(= :pattern (:type %))) vec)
              :function-binders (->> binders (filter #(= :function (:type %))) vec)
              :rhs-args `'~rhs-args
              :rhs-fn rhs-fn)))

(defn collapse-bindings
  [pattern-bindings collapsed-bindings]
  (loop [[[p {binding-vars :vars bindings :bindings} :as foo] & pattern-bindings] pattern-bindings
         collapsed-bindings collapsed-bindings]
    (if bindings
      (if (not-empty bindings)
        (let [collapsed-vars (-> collapsed-bindings first keys set)
              common-vars (set/intersection binding-vars collapsed-vars)]
          (recur pattern-bindings
                 (if (empty? bindings)
                   collapsed-bindings
                   (set
                     (filter some?
                             (for [cb collapsed-bindings
                                   b bindings]
                               (when (= (select-keys cb common-vars) (select-keys b common-vars))
                                 (merge cb b))))))))
        {:vars #{} :bindings #{}})
      {:vars (-> collapsed-bindings first keys set) :bindings collapsed-bindings})))

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
    (println ?e ?v)]

   [::r3
    [:find ?e ?x ?z
     :where
     [?e :a ?v]
     [(+ ?x 2) ?z]
     [(* ?v 0.3) ?x]]
    =>
    (println "X" ?x ?z)
    [[:db/add ?e :x ?x]]]])

(defn sort-function-bindings
  [rule]
  (if-let [function-binders (:function-binders rule)]
    (let [binding-vars (->> function-binders (map (juxt :binding-var identity)) (into {}))
          g (reduce (fn [g fb]
                      (reduce (fn [g v] (if-let [fb' (binding-vars v)] (update g fb conj fb') g))
                              g (:args fb)))
                    (into {} (map vector function-binders (repeat #{})))
                    function-binders)
          _ (clojure.pprint/pprint g)
          sorted-binders (-> g graph/kahn-sort reverse vec)]
      (assoc rule :function-binders sorted-binders))
    rule))

(defn create-session
  [& rulesets]
  {:rules           (vec (mapcat #(map sort-function-bindings %) rulesets))
   :pending-tx-data #{}})

(defn run-rule
  [fact rule]
  (let [f (subvec fact 1)
        pattern-binders (:pattern-binders rule)
        function-binders (:function-binders rule)
        ; TODO - check for conflicts
        fact-bindings (->> pattern-binders
                           (map (fn [{:keys [clause vars fn]}]
                                  [clause {:vars vars :bindings #{(fn f)}}]))
                           (filter (fn [[_ {bs :bindings}]] (not= #{nil} bs)))
                           (into {}))]
    (println (:name rule) fact fact-bindings)
    (if (not-empty fact-bindings)
      (let [op (first fact)
            update-fn (if (= :db/retract op) disj conj)
            collapsed-fact-binding (let [common-vars (apply set/intersection (map #(-> % val :vars) fact-bindings))
                                         bindings (reduce (fn [bs b]
                                                            (when (= (select-keys common-vars bs) (select-keys common-vars b))
                                                              (merge bs b)))
                                                          (map #(-> % val :bindings first) fact-bindings))]
                                     {:vars common-vars :bindings #{bindings}})
            collapsed-bindings (collapse-bindings (apply dissoc (:bindings rule) (keys fact-bindings)) (:bindings collapsed-fact-binding))
            collapsed-bindings (let [bs (set
                                          (for [bindings (:bindings collapsed-bindings)]
                                            (reduce (fn [b fb]
                                                      (if (set/subset? (set (:args fb)) (-> b keys set))
                                                        (assoc b (:binding-var fb) (get (apply (:fn fb) (map b (:args fb))) (:binding-var fb)))
                                                        b))
                                                    bindings function-binders)))]
                                 (assoc collapsed-bindings :vars (-> bs first keys set) :bindings bs))
            bindings (reduce (fn [bs [p b]]
                               (update-in bs [p :bindings] update-fn (first (:bindings b))))
                             (:bindings rule) fact-bindings)
            rule (assoc rule :bindings bindings)
            existing-bindings (set (-> rule :activations keys))
            new-bindings (set/difference (:bindings collapsed-bindings) existing-bindings)
            retracted-bindings (set/intersection existing-bindings (:bindings collapsed-bindings))
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
                   (let [activations (->> new-bindings
                                          (map (juxt identity
                                                     #(apply (:rhs-fn rule) (map % (:rhs-args rule)))))
                                          (into {}))
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





