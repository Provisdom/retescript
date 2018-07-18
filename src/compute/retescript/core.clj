(ns compute.retescript.core
  (:require [datascript.core :as d]
            [datascript.parser :as p]
            [datascript.query :as dq]
            [clojure.walk :refer [postwalk]]))

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

(defn alpha-clause?
  [node]
  (or
    (predicate? node)
    (pattern? node)))

(defn placeholder-eq
  [s v]
  (if (placeholder? v)
    `true
    `(= ~s ~(:value v))))

(defn alpha-clause->pred
  [node]
  (cond
    (predicate? node)
    (let [f (-> node :fn :symbol)
          args (mapv #(or (:symbol %) (:value %)) (:args node))
          params (->> node :args (filter variable?) (mapv :symbol))]
      ;;; TODO - resolve function symbol
      `(fn [~@params] (apply ~(resolve f) ~@args)))

    (pattern? node)
    (let [[e a v] (:pattern node)
          e' (gensym 'e)
          a' (gensym 'a)
          v' (gensym 'v)]
      (case (->> node :pattern (filter variable?) count)
        0 `(fn [[~'_ ~e' ~a' ~v']] (and ~(placeholder-eq e' e) ~(placeholder-eq a' a) ~(placeholder-eq v' v)))

        1 (cond
            (variable? e) `(fn [[~'_ ~'_ ~a' ~v']] (and ~(placeholder-eq a' a) ~(placeholder-eq v' v)))
            (variable? a) `(fn [[~'_ ~e' ~'_ ~v']] (and ~(placeholder-eq e' e) ~(placeholder-eq v' v)))
            (variable? v) `(fn [[~'_ ~e' ~a' ~'_]] (and ~(placeholder-eq e' e) ~(placeholder-eq a' a))))
        2 (cond
            (constant? e) `(fn [[~'_ ~'e ~'_ ~'_]] ~(placeholder-eq e' e))
            (constant? a) `(fn [[~'_ ~'_ ~'a ~'_]] ~(placeholder-eq a' a))
            (constant? v) `(fn [[~'_ ~'_ ~'_ ~'v]] ~(placeholder-eq v' v)))))))

(defn q->nodes
  [ast]
  (let [wh (:qwhere ast)
        patterns (filter #(= datascript.parser.Pattern (type %)) wh)]))

