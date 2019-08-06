(ns provisdom.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
            [datascript.db :as db]
            [clojure.set :as set]
            [clojure.spec.alpha :as s]
            [clojure.pprint :refer [pprint]]))

(defn query-valid?
  [query]
  (pprint query)
  (try
    (dp/parse-query query)
    (catch Exception e
      false)))

(s/def ::name (s/or :keyword keyword? :string string? :symbol symbol?))
(s/def ::query query-valid?)
(defn find-symbol
  [element]
  (or (:symbol element) (-> element :args first :symbol)))
(s/def ::=> fn?)
(s/def ::rule-def (s/keys :req-un [::name ::query ::=>]))

(defn check-rule
  [{:keys [query name =>] :as rule-def}]
  (try
    (dp/parse-query query)
    (catch Exception e
      (throw (ex-info (.getMessage e) {:rule-def rule-def}))))
  (when-let [ex (s/explain-data ::name name)]
    (throw (ex-info "Rule name fails spec" {:explain-data ex :rule-def rule-def})))
  (when-let [ex (s/explain-data ::=> =>)]
    (throw (ex-info "Rule RHS (:=>) fails spec" {:explain-data ex :rule-def rule-def})))
  rule-def)

(defn eval-rule-form
  [rule-form]
  (-> rule-form
      (update :name eval)
      (update :query eval)
      (as-> rf
            (if (fn? (:=> rf))
              rf
              (update rf :=> eval)))))

(defn compile-rule-form
  [rule-def]
  (let [[name query _ rhs-fn] rule-def
        rule-form {:name     `'~name
                   :query    (if (or (vector? query) (map? query)) `'~query query)
                   :rhs-form `'~rhs-fn
                   :=>       rhs-fn}]
    (check-rule (eval-rule-form rule-form))
    rule-form))

(defn compile-rule
  [rule-def]
  (-> rule-def
      compile-rule-form
      eval-rule-form))


(defmacro defrule
  [name query _ =>]
  (let [rule-def (compile-rule-form [name query _ =>])]
    (check-rule (eval rule-def))
    `(def ~name
       ~rule-def)))

(defn create-session
  [schema & ruleses]
  {:rules (->> ruleses
               (mapcat #(if (map? %) [%] %))
               (map check-rule)
               (map #(assoc % :bindings {}))
               vec)
   :db    (d/empty-db schema)})

(defn update-bindings
  [{:keys [name query => bindings] :as rule} db]
  (let [current-results (set (d/q query db))
        old-results (-> bindings keys set)
        added-results (set/difference current-results old-results)
        retracted-results (set/difference old-results current-results)
        db' (->> (select-keys bindings retracted-results)
                 (mapcat (fn [[_ ds]]
                           (->> ds
                                (map (fn [d] (assoc d 0 :db/retract))))))
                 (d/db-with db))
        [db'' added-bindings] (reduce (fn [[db bs] b]
                                        (let [rhs-tx (try
                                                       (apply => b)
                                                       (catch Exception e
                                                         (throw (ex-info "Exception evaluating RHS"
                                                                         {:rule (select-keys rule [:name :query :rhs-form])
                                                                          :bindings b
                                                                          :ex e}))))
                                              split-unconditional (group-by #(= :db/add! (first %)) rhs-tx)
                                              conditional-tx (split-unconditional false)
                                              unconditional-tx (->> (split-unconditional true)
                                                                    (mapv #(case (count %)
                                                                             2 (second %)
                                                                             4 (assoc % 0 :db/add))))
                                              db' (try
                                                    (d/db-with db unconditional-tx)
                                                    (catch Exception e
                                                      (throw (ex-info "Exception transacting RHS result"
                                                                      {:rule (select-keys rule [:name :query :rhs-form])
                                                                       :rhs-tx unconditional-tx
                                                                       :ex e}))))
                                              tx-report (try
                                                          (d/with db' conditional-tx)
                                                          (catch Exception e
                                                            (throw (ex-info "Exception transacting RHS result"
                                                                            {:rule (select-keys rule [:name :query :rhs-form])
                                                                             :rhs-tx conditional-tx
                                                                             :ex e}))))
                                              {db'' :db-after tx-data :tx-data} tx-report]
                                          [db'' (assoc bs b (->> tx-data
                                                                 (filter (fn [{:keys [added]}] added))
                                                                 (map (fn [{:keys [e a v]}] [:db/add e a v]))
                                                                 set))]))
                                      [db' {}] added-results)
        #_#_added-bindings (->> added-results
                                (map (fn [b]
                                       (->> b
                                            (apply =>)
                                            set
                                            (vector b))))
                                (into {}))
        #_#_added-datoms (->> added-bindings
                              (mapcat val)
                              set)]
    (when (or (not-empty added-results) (not-empty retracted-results))
      (tap> {:tag ::update-bindings
             :name name
             :added-results added-results
             :added-bindings added-bindings
             :retracted-results retracted-results
             :retracted-bindings (select-keys bindings retracted-results)}))
    [(merge added-bindings (apply dissoc bindings retracted-results))
     db'']))

(defn transact
  ; TODO - check tx-data is vector of datoms?
  [session tx-data]
  (loop [{:keys [rules] :as session} (update session :db d/db-with tx-data)]
    (let [session' (reduce (fn [{:keys [db] :as rs} rule]
                             (let [[bs db'] (update-bindings rule db)]
                               (-> rs
                                   (update :rules conj (assoc rule :bindings bs))
                                   (assoc :db db'))))
                           (assoc session :rules []) rules)]
      (if (= (:db session) (:db session'))
        session
        (recur session')))))