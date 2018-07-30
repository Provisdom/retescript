(ns compute.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
            [datascript.query :as dq]
            [datascript.arrays :as da]
            [clojure.set :as set]
            [loom.graph :as graph]
            [loom.alg :as alg]
            [clojure.pprint :refer [pprint]])
  (:import (datascript.query Context)))

(defn replace-query-vars
  [x]
  (if (and (symbol? x) (= \? (first (str x))))
    '_
    x))

(defn pattern?
  [node]
  (= datascript.parser.Pattern (type node)))

(defn and?
  [node]
  (= datascript.parser.And (type node)))

(defn not?
  [node]
  (= datascript.parser.Not (type node)))

(defn or?
  [node]
  (= datascript.parser.Or (type node)))

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

(defn unparse-predicate
  [p]
  [(apply list (-> p :fn :symbol) (->> p :args (map #(or (:symbol %) (:value %)))))])

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

(defn predicate-clause-fn
  [f args]
  (let [[body] f]
    `{:clause '~f
      :type   :predicate
      :args   '~args
      :vars   '~(set args)
      :fn     (fn [~@args] ~body)}))

(defn function-clause-binding-fn
  [f args]
  (let [[body binding-var] f]
    `{:clause      '~f
      :type        :function
      :binding-var '~binding-var
      :args        '~args
      :vars        '~(conj (set args) binding-var)
      :fn          (fn [~@args] {'~binding-var ~body})}))

(defn clause-paths
  [negate? paths [clause & clauses]]
  (if clause
    (cond
      (and? clause) (let [paths' (clause-paths negate? paths (:clauses clause))]
                      (recur negate? paths' clauses))

      (not? clause) (let [paths' (clause-paths (not negate?) paths (:clauses clause))]
                      (recur negate? paths' clauses))

      (or? clause) (let [paths' (vec (mapcat #(clause-paths negate? paths [%]) (:clauses clause)))]
                     (recur negate? paths' clauses))

      :else (let [paths' (mapv #(conj % (assoc clause :negate? negate?)) paths)]
              (recur negate? paths' clauses)))
    paths))

(defn compile-query
  [query-def]
  (let [[name query] query-def
        query-ast (dp/parse-query query)
        paths (clause-paths false [[]] (:qwhere query-ast))
        path-binders (->> paths
                          (map #(->> %
                                     (mapv (fn [p]
                                             (-> (cond
                                                   (pattern? p) (pattern-clause-binding-fn (unparse-pattern p))

                                                   (function? p) (function-clause-binding-fn (unparse-function p) (->> p :args (map :symbol) (filter dq/free-var?) vec))

                                                   (predicate? p) (predicate-clause-fn (unparse-predicate p) (->> p :args (map :symbol) (filter dq/free-var?) vec)))
                                                 (assoc :negate? (:negate? p)))))))
                          (mapv (fn [binders]
                                  {:pattern-binders  (->> binders (filter #(= :pattern (:type %))) vec)
                                   :function-binders (->> binders (filter #(= :function (:type %))) vec)
                                   :predicates       (->> binders (filter #(= :predicate (:type %))) vec)
                                   :bindings         {}})))]
    {:name         name
     :query        `'~query
     :query-ast    query-ast
     :path-binders path-binders}))

(defn compile-rule
  [rule-def]
  (let [[name query _ & rhs] rule-def
        cq (compile-query [name query])


        rhs-args (->> cq :query-ast :qfind :elements (mapv :symbol))
        rhs-fn `(fn [~@rhs-args]
                  ~@rhs)]

    (assoc cq :rhs-args `'~rhs-args
              :rhs-fn rhs-fn)))

(defmacro defrules
  [name rules]
  (let [cr (mapv compile-rule rules)]
    `(def ~name
       ~cr)))

(defn join-graph-components
  [rule]
  (let [pbs (concat (:pattern-binders rule))
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

(defn sort-function-binders
  [function-binders]
  (let [edges (->> (for [f1 function-binders
                         f2 function-binders]
                     (when (contains? (-> f1 :args set) (-> f2 :binding-var))
                       [f2 f1]))
                   (filter some?))
        g (-> (graph/digraph)
              (graph/add-nodes* function-binders)
              (graph/add-edges* edges))]
    (vec (alg/topsort g))))

(defn group-join-patterns
  [rule]
  (let [jbs (->> (join-graph-components rule)
                 (mapv (fn [jb]
                         (let [pbs (->> jb
                                        (filter #(= :pattern (:type %)))
                                        vec)
                               vars (apply set/union (map :vars pbs))]
                           {:vars            vars
                            :pattern-binders pbs
                            :bindings        #{}}))))]
    (-> rule
        (assoc :joined-binders jbs)
        (dissoc :pattern-binders))))

(defn group-and-sort-path-binders
  [path-binders]
  (mapv (fn [binders]
          (-> binders
              (update :function-binders sort-function-binders)
              group-join-patterns))
        path-binders))

(defn create-session
  [& rulesets]
  {:rules           (vec (map #(update % :path-binders group-and-sort-path-binders)
                              (apply concat rulesets)))
   :pending-tx-data #{}})

(defn merge-bindings
  [pb {fact-pattern :clause fact-binding :binding}]
  (-> pb
      (update :patterns conj fact-pattern)
      (update :binding merge fact-binding)))

(defn unmerge-bindings
  [pb {fact-pattern :clause fact-binding :binding}]
  (let [patterns (disj (:patterns pb) fact-pattern)
        vars (->> patterns
                  (apply concat)
                  (filter symbol?)
                  set)]
    (assoc pb :patterns patterns
              :binding (select-keys (:binding pb) vars))))

(defn join-bindings
  [joined-pattern-binder op {fact-pattern :clause fact-vars :vars fact-binding :binding :as pfb}]
  (let [joined? (volatile! false)
        joined-bindings (->> (:bindings joined-pattern-binder)
                             (mapv (fn [%]
                                     (let [binding (:binding %)
                                           join? (reduce (fn [j? fv]
                                                           (if j?
                                                             (let [fb (get fact-binding fv)]
                                                               (and j? (or (nil? fb) (= fb (get binding fv)))))
                                                             j?))
                                                         true fact-vars)]
                                       (vswap! joined? #(or join? %))
                                       (if join?
                                         (if (= op :db/retract)
                                           (unmerge-bindings % pfb)
                                           (merge-bindings % pfb))
                                         %))))
                             (filter (comp not-empty :binding))
                             set)]
    (if @joined?
      (assoc joined-pattern-binder :bindings joined-bindings)
      (update joined-pattern-binder :bindings conj {:patterns #{fact-pattern} :binding fact-binding}))))

(defn update-pattern-bindings
  [op joined-pattern-binder pattern-fact-binding]
  (let [joined-pattern-binder (join-bindings joined-pattern-binder op pattern-fact-binding)]
    joined-pattern-binder))

(defn cross-join
  [[x & xs :as foo]]
  (if (empty? xs)
    x
    (for [x1 x x2 (cross-join xs)]
      (merge x1 x2))))

(defn bind-patterns
  [f pattern-binders]
  (->> pattern-binders
       (map (fn [{:keys [fn] :as pb}]
              (assoc pb :binding (fn f))))
       (filter (comp some? :binding))))

(defn update-path-binders
  [fact path-binders]
  (let [f (subvec fact 1)
        pattern-fact-bindings (mapv (partial bind-patterns f) (map :pattern-binders (:joined-binders path-binders)))]
    (if (not-empty pattern-fact-bindings)
      (let [op (first fact)
            updated-joined-binders (mapv (fn [jpb pfbs]
                                           (reduce
                                             (fn [jpb pfb]
                                               (update-pattern-bindings op jpb pfb))
                                             jpb pfbs))
                                         (:joined-binders path-binders) pattern-fact-bindings)
            updated-path-binders (assoc path-binders :joined-binders updated-joined-binders)]
        updated-path-binders)
      path-binders)))

(defn path-bindings
  [path-binders]
  (let [function-binders (:function-binders path-binders)
        predicates (:predicates path-binders)
        cross-joins (->> (:joined-binders path-binders)
                         (map (fn [joined-pattern-binder]
                                (let [pattern-binders (:pattern-binders joined-pattern-binder)
                                      patterns (->> pattern-binders
                                                    (filter (complement :negate?))
                                                    (map :clause)
                                                    set)
                                      negated-patterns (->> pattern-binders
                                                            (filter :negate?)
                                                            (map :clause)
                                                            set)]
                                  (->> (:bindings joined-pattern-binder)
                                       (filter #(and (empty? (set/difference patterns (:patterns %)))
                                                     (empty? (set/intersection negated-patterns (:patterns %)))))
                                       (map :binding)
                                       set))))
                         cross-join
                         set)
        complete-bindings (->> cross-joins
                               (filter (fn [b] (reduce (fn [match? pred]
                                                         (and match?
                                                              (if (:negate? pred)
                                                                (not (apply (:fn pred) (map b (:args pred))))
                                                                (apply (:fn pred) (map b (:args pred))))))
                                                       true predicates)))
                               set)
        bindings (->> complete-bindings
                      (reduce (fn [bs b]
                                (let [b' (loop [[function-binder & function-binders] function-binders
                                                b b]
                                           (if (and b function-binder)
                                             (let [fb (apply (:fn function-binder) (map b (:args function-binder)))
                                                   v (:binding-var function-binder)]
                                               (recur
                                                 function-binders
                                                 (when (or (nil? (b v)) (= (b v) (fb v)))
                                                   (merge b fb))))
                                             b))]
                                  (if b' (conj bs b') bs)))
                              #{}))]
    bindings))

(defn run-rule
  [facts rule]
  (println "*******" (:name rule) #_facts)
  (let [updated-path-binders (reduce (fn [path-binders fact]
                                       (mapv (partial update-path-binders fact) path-binders))
                                     (:path-binders rule) facts)
        rule (assoc rule :path-binders updated-path-binders)]
    (if (:rhs-fn rule)
      (let [bindings (reduce set/union #{} (map path-bindings (:path-binders rule)))
            existing-bindings (set (-> rule :activations keys))
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
                         (update :tx-data set/union tx-data)))
                   rule)
            rule (if (not-empty new-bindings)
                   (let [activations (->> new-bindings
                                          (map (juxt identity
                                                     #(apply (:rhs-fn rule) (map % (:rhs-args rule)))))
                                          (into {}))
                         tx-data (set (mapcat val activations))]
                     (-> rule
                         (update :activations merge activations)
                         (update :tx-data set/union tx-data)))
                   rule)]
        rule)
      rule)))


(defn transact1
  [session fact]
  (let [rules (mapv (partial run-rule fact) (:rules session))]
    (assoc session :rules rules)))

(defn transact
  [session tx-data]
  (loop [session (transact1 session tx-data)]
    (let [tx-data (apply set/union (map :tx-data (:rules session)))
          session (update session :rules #(mapv (fn [r] (dissoc r :tx-data)) %))]
      #_(println tx-data)
      #_(clojure.pprint/pprint session)
      (if (not-empty tx-data)
        (recur (transact1 session tx-data))
        session))))

(defn query
  [session rule-name]
  (let [rule (->> session :rules (filter #(= rule-name (:name %))) first)]
    (reduce set/union #{} (map path-bindings (:path-binders rule)))))

(defrules rs
  [[::r1
    [:find ?e
     :where
     [?e :a ?v]
     [(= 1 ?v)]]
    =>
    [[:db/add ?e :one true]]]

   [::r2
    [:find ?e ?v
     :where
     [?e :a ?v]
     [?e :one true]]
    =>
    [[:db/add ?e :foo :bar]]
    #_(println "R2" ?e ?v)]

   [::r3
    [:find ?e ?x ?z
     :where
     [?e :a ?v]
     [(+ ?x 2) ?z]
     [(* ?v 0.3) ?x]]
    =>
    #_(println "R3" ?x ?z)
    [[:db/add ?e :x ?x]]]

   [::r4
    [:find ?e1 ?v2
     :where
     [?e1 :a _]
     [_ :a ?v2]
     #_[_ :b ?v2]
     #_[(identity ?v2) ?q]
     #_[(inc ?v2) ?q]
     #_[?e1 :a ?q]]
    =>
    [[:db/add ?e1 :foo :bar]]
    #_(println "R4" ?e1 ?v2)]

   [::r5
    [:find ?e ?v ?w ?q
     :where
     [?e :a ?v]
     [?e :b ?w]
     [?e :c ?q]
     (not [?e :c 1]
          [?e :d 2]
          [(> ?w 5)]
          #_[(identity ?e) ?e])
     (or [?e :a 1]
         (and [?e :a 2]
              [?e :b 1]))]
    =>
    #_(println "R5" ?e ?v ?w ?q)
    [[:db/add ?e :foo :bar]]]

   [::q1
    [:find ?e ?v ?w ?q
     :where
     [?e :a ?v]
     [?e :b ?w]
     [?e :c ?q]
     (not [?e :c 1]
          [?e :d 2]
          [(> ?w 5)]
          #_[(identity ?e) ?e])
     (or [?e :a 1]
         (and [?e :a 2]
              [?e :b 1]))]]])

(def s (create-session rs))


