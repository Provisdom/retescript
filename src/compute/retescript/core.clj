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

(defn q->nodes
  [ast]
  (let [wh (:qwhere ast)
        patterns (filter #(= datascript.parser.Pattern (type %)) wh)]))

