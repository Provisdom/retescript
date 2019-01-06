(ns provisdom.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as dp]
            [clojure.set :as set]
            [clojure.pprint :refer [pprint]]))

(defn compile-rule
  [rule-def]
  (let [[name query _ & rhs] rule-def
        query-ast (dp/parse-query query)
        rhs-args (->> query-ast :qfind :elements (mapv :symbol))
        rhs-fn `(fn [~@rhs-args]
                  ~@rhs)]
    {:name     name
     :query    `'~query
     :rhs-args `'~rhs-args
     :rhs-fn   rhs-fn
     :bindings {}}))

(defmacro defrules
  [name rules]
  (let [cr (mapv compile-rule rules)]
    `(def ~name
       {:rules ~cr
        :db (d/db (d/create-conn))})))

(defn update-bindings
  [{:keys [query rhs-fn bindings] :as rule} db]
  (let [current-results (d/q query db)
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

(defn transact-datom
  [{:keys [rules db] :as session} datom]
  (let [db' (d/db-with db [datom])]
    (reduce (fn [[rs ds'] rule]
              (let [[bs ds] (update-bindings rule db')]
                [(update rs :rules conj (assoc rule :bindings bs)) (set/union ds' ds)]))
            [(assoc session :db db' :rules []) #{}] rules)))

(defn transact
  ; TODO - check tx-data is vector of datoms?
  [session tx-data]
  (loop [session session
         datoms tx-data]
    (if (not-empty datoms)
      (let [[session' new-datoms] (reduce (fn [[rs ds] d]
                                            (let [[rs' ds'] (transact-datom rs d)]
                                              [rs' (concat ds ds')]))
                                          [session #{}] datoms)]
        (recur session' new-datoms))
      session)))






