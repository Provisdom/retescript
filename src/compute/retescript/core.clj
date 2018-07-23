(ns compute.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
            [datascript.query :as dq]
            [datascript.arrays :as da]
            [clojure.set :as set]
            [loom.graph :as graph]
            [loom.alg :as alg])
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
      :type   :pattern
      :vars   '~(-> var->idx keys set)
      :fn     (fn [x#]
                (when (dq/matches-pattern? '~pattern x#)
                  (into {} (map (fn [[v# i#]] [v# (x# i#)]) '~var->idx))))}))

(defn function-clause-binding-fn
  [f args]
  (let [[body binding-var] f]
    `{:clause      '~f
      :type        :function
      :binding-var '~binding-var
      :args        '~args
      :vars        '~(conj (set args) binding-var)
      :fn          (fn [~@args] {'~binding-var ~body})}))


(defn compile-query
  [query-def]
  (let [[name query] query-def
        query-ast (dp/parse-query query)
        patterns (->> query-ast :qwhere (map (fn [p] `'~(unparse-pattern p))))]
    {:name      name
     :query     `'~query
     :query-ast query-ast
     :bindings  {} #_(->> query-ast
                          :qwhere
                          (filter pattern?)
                          (map (fn [p]
                                 [`'~(unparse-pattern p)
                                  `'{:vars     ~(->> p :pattern (filter variable?) (map :symbol) set)
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
  [pattern-bindings {fact-binding-vars :vars fact-bindings :bindings}]
  (loop [[[pattern {binding-vars :vars bindings :bindings}] & pattern-bindings] pattern-bindings
         fact-bindings fact-bindings]
    (if (not-empty bindings)
      (let [common-vars (set/intersection binding-vars fact-binding-vars)]
        (recur pattern-bindings
               (if (empty? bindings)
                 fact-bindings
                 (set
                   (filter some?
                           (for [cb fact-bindings
                                 b bindings]
                             (when (= (select-keys cb common-vars) (select-keys b common-vars))
                               (merge cb b))))))))
      {:vars fact-binding-vars :bindings fact-bindings})))

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
    [[:db/add ?e :x ?x]]]

   [::r4
    [:find ?e1 ?v2
     :where
     [?e1 :a _]
     [_ :a ?v2]
     #_[?e1 :b ?v2]
     #_[(+ ?v2 1) ?q]]
    =>
    (println "R4" ?e1 ?v2)]])


#_(defn sort-function-bindings
    [rule]
    (if-let [function-binders (:function-binders rule)]
      (let [binding-vars (->> function-binders (map (juxt :binding-var identity)) (into {}))
            g (reduce (fn [g fb]
                        (reduce (fn [g v] (if-let [fb' (binding-vars v)] (update g fb conj fb') g))
                                g (:args fb)))
                      (into {} (map vector function-binders (repeat #{})))
                      function-binders)
            sorted-binders (-> g graph/kahn-sort reverse vec)]
        (assoc rule :function-binders sorted-binders))
      rule))

(defn join-graph-components
  [rule]
  (let [pbs (concat (:pattern-binders rule) (:function-binders rule))
        edges (loop [[pb & pbs] pbs
                     edges []]
                (if pb
                  (recur pbs (->> pbs
                                  (filter (fn [pb'] (not-empty (set/intersection (:vars pb) (:vars pb')))))
                                  (map (partial vector pb))
                                  (into edges)))
                  edges))
        g (as-> (graph/graph) g
                (apply graph/add-nodes g pbs)
                (apply graph/add-edges g edges))]
    (alg/connected-components g)))

(defn sort-function-bindings
  [function-bindings]
  (let [edges (->> (for [f1 function-bindings
                         f2 function-bindings]
                     (when (contains? (-> f1 :args set) (-> f2 :binding-var))
                       [f2 f1]))
                   (filter some?))
        g (-> (graph/digraph)
              (graph/add-nodes* function-bindings)
              (graph/add-edges* edges))]
    (alg/topsort g)))

(defn group-join-patterns
  [rule]
  (let [jbs (->> (join-graph-components rule)
                 (mapv (fn [jb]
                         (let [pbs (->> jb
                                        (filter #(= :pattern (:type %)))
                                        vec)
                               fbs (->> jb
                                        (filter #(= :function (:type %)))
                                        sort-function-bindings
                                        vec)
                               vars (apply set/union (map :vars (concat pbs fbs)))]
                           {:vars             vars
                            :pattern-binders  pbs
                            :function-binders fbs
                            :bindings         #{}}))))]
    (-> rule
        (assoc :joined-binders jbs)
        (dissoc :pattern-binders :function-binders))))

(defn create-session
  [& rulesets]
  {:rules           (vec (mapcat #(->> %
                                       #_(map sort-function-bindings)
                                       (map group-join-patterns))
                                 rulesets))
   :pending-tx-data #{}})

(defn join-bindings
  [{fact-vars :vars fact-binding :binding} {vars :vars bindings :bindings}]
  (let [common-vars (set/intersection vars fact-vars)]
    (let [b1 (select-keys fact-binding common-vars)]
      (->> bindings
           (filter #(= b1 (select-keys (:binding %) common-vars)))
           set))))

(defn merge-bindings
  [joined-bindings [fact-pattern {fact-binding :binding}]]
  (->> joined-bindings
       (map (fn [pb]
              (-> pb
                  (update :patterns conj fact-pattern)
                  (update :binding merge fact-binding))))
       set))

(defn update-pattern-bindings
  [op current-bindings [fact-pattern {fact-binding :binding :as fb} :as pfb]]
  (let [joined-bindings (join-bindings fb current-bindings)]
    (if (= op :db/retract)
      (if (empty? joined-bindings)
        current-bindings
        (update current-bindings :bindings set/difference joined-bindings))
      (if (empty? joined-bindings)
        (update current-bindings :bindings conj {:patterns #{fact-pattern} :binding fact-binding})
        (-> current-bindings
            (update :bindings set/difference joined-bindings)
            (update :bindings set/union (merge-bindings joined-bindings pfb)))))))

(defn update-bindings
  [op current-bindings pattern-fact-binding]
  (let [pattern-bindings (update-pattern-bindings op current-bindings pattern-fact-binding)
        function-binders (:function-binders pattern-bindings)]
    (update pattern-bindings :bindings #(->> %
                                             (map (fn [{b :binding :as pb}]
                                                    (assoc pb
                                                      :binding (reduce (fn [b fb]
                                                                         (if (and
                                                                               (not (contains? b (:binding-var fb)))
                                                                               (set/subset? (-> fb :args set) (-> b keys set)))
                                                                           (merge b (apply (:fn fb) (map b (:args fb))))
                                                                           b))
                                                                       b function-binders))))
                                             set))))

(defn cross-join
  [[x & xs]]
  (if (empty? xs)
    x
    (for [x1 x x2 (cross-join xs)]
      {:patterns (set/union (:patterns x1) (:patterns x2))
       :binding (merge (:binding x1) (:binding x2))})))

(defn run-rule
  [fact rule]
  (let [f (subvec fact 1)
        pattern-binders (mapcat :pattern-binders (:joined-binders rule))
        patterns (->> pattern-binders (map :clause) set)
        ; TODO - check for conflicts
        pattern-fact-bindings (->> pattern-binders
                                   (map (fn [{:keys [clause vars fn]}]
                                          [clause {:vars vars :binding (fn f)}]))
                                   (filter (fn [[_ {bs :binding}]] (some? bs)))
                                   (into {}))]
    (println (:name rule) fact pattern-fact-bindings)
    (if (not-empty pattern-fact-bindings)
      (let [op (first fact)
            bindings-by-join (->> rule
                                  :joined-binders
                                  (mapv (fn [jpb]
                                          (->> pattern-fact-bindings
                                               (reduce (fn [jpb [p fb :as pfb]]
                                                         (if (not-empty (set/intersection (:vars fb) (:vars jpb)))
                                                           (update-bindings op jpb pfb)
                                                           jpb))
                                                       jpb)))))
            rule (assoc rule :joined-binders bindings-by-join)
            cross-joins (->> bindings-by-join
                             (map :bindings)
                             cross-join
                             set)
            complete-bindings (->> cross-joins
                                   (filter #(= patterns (:patterns %)))
                                   (map :binding)
                                   set)
            existing-bindings (set (-> rule :activations keys))
            new-bindings (set/difference complete-bindings existing-bindings)
            retracted-bindings (set/difference existing-bindings complete-bindings)
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





