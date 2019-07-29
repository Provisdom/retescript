(ns provisdom.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
            [datascript.db :as db]
            [clojure.set :as set]
            [clojure.pprint :refer [pprint]]))

(defn find-symbol
  [element]
  (or (:symbol element) (-> element :args first :symbol)))

(defn compile-rule
  [rule-def]
  (let [[name query _ rhs-fn] rule-def
        query-ast (dp/parse-query query)
        #_#_rhs-args (->> query-ast :qfind :elements (mapv find-symbol))
        #_#_rhs-fn `(fn [~@rhs-args]
                      ~@rhs)]
    {:name     name
     :query    `'~query
     #_#_:rhs-args `'~rhs-args
     :rhs-fn   rhs-fn
     :bindings {}}))

(defmacro defrules
  [name rules]
  (let [cr (mapv compile-rule rules)]
    `(def ~name
       ~cr)))

(defn create-session
  [schema & ruleses]
  {:rules (->> ruleses (mapcat identity) vec)
   :db    (d/empty-db schema)})

(defn update-bindings
  [{:keys [query rhs-fn bindings] :as rule} db]
  (let [current-results (set (d/q query db))
        old-results (-> bindings keys set)
        added-results (set/difference current-results old-results)
        retracted-results (set/difference old-results current-results)
        [db' added-bindings] (reduce (fn [[db bs] b]
                                       (let [{db' :db-after tx-data :tx-data} (d/with db (apply rhs-fn b))]
                                         [db' (assoc bs b (->> tx-data
                                                               (filter (fn [{:keys [added]}] added))
                                                               (map (fn [{:keys [e a v]}] [:db/add e a v]))
                                                               set))]))
                                     [db {}] added-results)
        #_#_added-bindings (->> added-results
                                (map (fn [b]
                                       (->> b
                                            (apply rhs-fn)
                                            set
                                            (vector b))))
                                (into {}))
        #_#_added-datoms (->> added-bindings
                              (mapcat val)
                              set)
        db'' (->> (select-keys bindings retracted-results)
                  (mapcat (fn [[_ ds]]
                            (->> ds
                                 (map (fn [d] (assoc d 0 :db/retract))))))
                  (d/db-with db'))]
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