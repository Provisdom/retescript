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

(defn tree-seq-path
  "Like core's tree-seq but returns a lazy sequence of vectors of the
  paths of the nodes in a tree, via a depth-first walk. It optionally
  applies node-fn to each node before adding it to the path. branch?
  must be a fn of one arg that returns true if passed a node that can
  have children (but may not).  children must be a fn of one arg that
  returns a sequence of the children. Will only be called on nodes for
  which branch? returns true. Root is the root node of the tree."
  [branch? children root & [node-fn]]
  (let [node-fn (or node-fn identity)
        walk (fn walk [path node]
               (let [new-path (conj path (node-fn node))]
                 (lazy-seq
                    (cons new-path
                            (when (branch? node)
                              (mapcat (partial walk new-path) (children node)))))))]
    (walk [] root)))

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
    `{:clause      '~f
      :type        :predicate
      :args        '~args
      :vars        '~(set args)
      :fn          (fn [~@args] ~body)}))

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

      (not? clause) (let [paths' (vec (mapcat #(clause-paths (not negate?) paths [%]) (:clauses clause)))]
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
                                  {:pattern-binders (->> binders (filter #(= :pattern (:type %))) vec)
                                   :function-binders (->> binders (filter #(= :function (:type %))) vec)
                                   :predicates (->> binders (filter #(= :predicate (:type %))) vec)
                                   :bindings  {}})))]
    {:name      name
     :query     `'~query
     :query-ast query-ast
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

(defrules rs
  [#_[::r1
      [:find ?e
       :where
       [?e :a ?v]
       [(= 1 ?v)]]
      =>
      [[:db/add ?e :one true]]]

   #_[::r2
      [:find ?e ?v
       :where
       [?e :a ?v]
       [?e :one true]]
      =>
      (println ?e ?v)]

   #_[::r3
      [:find ?e ?x ?z
       :where
       [?e :a ?v]
       [(+ ?x 2) ?z]
       [(* ?v 0.3) ?x]]
      =>
      (println "X" ?x ?z)
      [[:db/add ?e :x ?x]]]

   #_[::r4
      [:find ?e1 ?v2
       :where
       [?e1 :a _]
       [_ :a ?v2]
       #_[_ :b ?v2]
       [(identity ?v2) ?q]
       #_[(inc ?v2) ?q]
       [?e1 :a ?q]]
      =>
      (println "R4" ?e1 ?v2)]

   [:r5
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
    (println "R5" ?e ?v ?w ?q)
    [[?e :foo :bar]]]])


(defn join-graph-components
  [rule]
  (let [pbs (concat (:pattern-binders rule) #_(:function-binders rule))
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
                               #_#_fbs (->> jb
                                            (filter #(= :function (:type %)))
                                            sort-function-binders
                                            vec)
                               vars (apply set/union (map :vars pbs))]
                           {:vars            vars
                            :pattern-binders pbs
                            #_#_:function-binders fbs
                            :bindings        #{}}))))]
    (-> rule
        (assoc :joined-binders jbs)
        (dissoc :pattern-binders #_:function-binders))))

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
                  (update :patterns set/union fact-pattern)
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
        (update current-bindings :bindings conj {:patterns fact-pattern :binding fact-binding})
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
       :binding  (merge (:binding x1) (:binding x2))})))

(defn bind-patterns
  [f pattern-binders]
  (->> pattern-binders
       (map (fn [{:keys [clause vars fn]}]
              [clause (fn f)]))
       (filter (fn [[_ b]] (some? b)))
       (reduce (fn [[ps {vs :vars bs :binding}] [p b]] [(conj ps p)
                                                        (let [bs (merge bs b)]
                                                          {:vars (-> bs keys set) :binding bs})])
               [#{} {:vars #{} :binding {}}])))

(defn run-path-binders
  [fact rhs-fn rhs-args path-binders]
  (let [f (subvec fact 1)
        pattern-binders (mapcat :pattern-binders (:joined-binders path-binders))
        patterns (->> pattern-binders (map :clause) set)
        function-binders (:function-binders path-binders)
        predicates (:predicates path-binders)
        ; TODO - check for conflicts
        pattern-fact-bindings (mapv (partial bind-patterns f) (map :pattern-binders (:joined-binders path-binders)))]
    (println fact pattern-fact-bindings)
    (if (not-empty pattern-fact-bindings)
      (let [op (first fact)
            bindings-by-join (mapv (fn [jpb pfb] (update-pattern-bindings op jpb pfb)) (:joined-binders path-binders) pattern-fact-bindings)
            updated-path-binders (assoc path-binders :joined-binders bindings-by-join)
            cross-joins (->> bindings-by-join
                             (map (fn [jb]
                                    (->> jb
                                         :bindings
                                         (filter (fn [%] (set/subset? (-> % :binding keys set) (:vars jb)))))))
                             cross-join
                             set)
            complete-bindings (->> cross-joins
                                   (filter #(= patterns (:patterns %)))
                                   (map :binding)
                                   (filter (fn [b] (reduce (fn [match? pred]
                                                             (and match? (apply (:fn pred) (map b (:args pred)))))
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
                                  #{}))
            _ (pprint bindings)
            existing-bindings (set (-> updated-path-binders :activations keys))
            _ (pprint existing-bindings)
            new-bindings (set/difference bindings existing-bindings)
            _ (pprint new-bindings)
            retracted-bindings (set/difference existing-bindings bindings)
            _ (pprint retracted-bindings)
            updated-path-binders (if (not-empty retracted-bindings)
                                   (let [tx-data (set (->> retracted-bindings
                                                           (mapcat (:activations updated-path-binders))
                                                           (filter #(not= :db/add! (first %)))
                                                           (map #(assoc % 0 :db/retract))))
                                         activations (apply dissoc (:activations updated-path-binders) retracted-bindings)]
                                     (-> updated-path-binders
                                         (assoc :activations activations)
                                         (update :tx-data concat tx-data)))
                                   updated-path-binders)
            updated-path-binders (if (not-empty new-bindings)
                                   (let [activations (->> new-bindings
                                                          (map (juxt identity
                                                                     #(apply rhs-fn (map % rhs-args))))
                                                          (into {}))
                                         tx-data (set (mapcat val activations))]
                                     (-> updated-path-binders
                                         (update :activations merge activations)
                                         (update :tx-data concat tx-data)))
                                   updated-path-binders)]
        updated-path-binders)
      path-binders)))

(defn run-rule
  [fact rule]
  (println "*********" (:name rule))
  (let [updated-path-binders (mapv (partial run-path-binders fact (:rhs-fn rule) (:rhs-args rule)) (:path-binders rule))
        tx-data (reduce into [] (map :tx-data updated-path-binders))]
    (assoc rule :path-binders updated-path-binders
                :tx-data tx-data)))

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





