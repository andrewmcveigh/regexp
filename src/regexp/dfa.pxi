(ns regexp.dfa
  (:require
   [pixie.string :as string]))

(defn print-syntax-tree
  ([indent tree]
   
   ))

'(. (* (| a b)) a)

"    ."
"   / \\"
"  *   a"
"  |"
"  |"
" / \\"
"a   b"

(defmulti print-node (fn [indent x] (type x)))

(defn print-leaf-node [indent [op a b]]
  (let [n (inc indent)
        pre (or (some-> (repeat indent "--") seq string/join) "")]
    (str pre "--" op "--" \newline
         pre "-/" (if b "-\\-" "---") \newline
         pre
         (if a (print-node n a) "")
         (if (and a b) "---" "")
         (if b (print-node n b) "-"))))

(defmethod print-node Symbol [_ x]
  (name x))

(defmethod print-node PersistentList [indent x]
  (print-leaf-node indent x))

(defmethod print-node Cons [indent x]
  (print-leaf-node indent x))


;; (println (print-node 0 '(* (| a b))))

;; (defn print-level [level nodes]
;;   (if (every? symbol? nodes)
;;     [level (count nodes) (->> nodes
;;                               (map name)
;;                               (partition 2)
;;                               (map (partial interpose "   "))
;;                               (interpose " "))]
;;     (let [[l c s] (G)])
;;     ))

(defmulti ->tree (fn [_ x] (type x)))

(defmethod ->tree Cons [level [op l r]]
  (let [n (inc level)]
    {:op op :nodes [:l (->tree n l) :r (->tree n r) :level level]}))

(defmethod ->tree Symbol [_ x] x)

(defmethod ->tree Nil [_ _])

;; (->tree 0 '(. (* (| a b)) a))

(loop [tree '[[a b c d e f]
              [| | | g]
              [. .]
              [.]]
       level 1]
  (let [h (first tree)]
    (when h
      (let [space (string/join (repeat level "-"))
            indent (string/join (repeat level "--"))]
        (->> h
             (map name)
             (partition 2)
             (map (partial interpose (str space "---")))
             (interpose space)
             (flatten)
             (string/join)
             (str indent)
             (println))
        (println (str indent "-" (string/join (str "--" space) (repeat (/ (count h) 2) "\\ /"))))
        (recur (rest tree) (inc level))))))
