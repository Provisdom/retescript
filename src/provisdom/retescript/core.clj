(ns provisdom.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
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
   :db (d/empty-db schema)})

(defn update-bindings
  [{:keys [query rhs-fn bindings]} db]
  (let [current-results (set (d/q query db))
        old-results (-> bindings keys set)
        added-results (set/difference current-results old-results)
        retracted-results (set/difference old-results current-results)
        added-bindings (->> added-results
                            (map (fn [b]
                                   (->> b
                                        (apply rhs-fn)
                                        set
                                        (vector b))))
                            (into {}))
        added-datoms (->> added-bindings
                          (mapcat val)
                          set)
        retracted-datoms (->> (select-keys bindings retracted-results)
                              (mapcat (fn [[_ ds]]
                                        (->> ds
                                             (map (fn [d] (assoc d 0 :db/retract))))))
                              set)]
    [(merge added-bindings (apply dissoc bindings retracted-results))
     (set/union added-datoms retracted-datoms)]))

(defn transact
  ; TODO - check tx-data is vector of datoms?
  [session tx-data]
  (loop [{:keys [rules db] :as session} session
         tx-data tx-data]
    (println tx-data db)
    (if (not-empty tx-data)
      (let [db' (d/db-with db tx-data)
            [session' new-datoms] (reduce (fn [[rs ds'] rule]
                                            (let [[bs ds] (update-bindings rule db')]
                                              [(update rs :rules conj (assoc rule :bindings bs)) (set/union ds' ds)]))
                                          [(assoc session :db db' :rules []) #{}] rules)]
        (recur session' (vec new-datoms)))
      session)))






