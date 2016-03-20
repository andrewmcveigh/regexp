(ns regexp.core
  (:require
   [pixie.set :as set]
   [pixie.string :as string]))

(def alpha-range
  [\a \b \c \d \e \f \g \h \i \j \k \l \m \n \o \p \q \r \s \t \u \v
   \w \x \y \z \A \B \C \D \E \F \G \H \I \J \K \L \M \N \O \P \Q \R
   \S \T \U \V \W \X \Y \Z])
(def alpha? (set alpha-range))
(def numeric-range [\0 \1 \2 \3 \4 \5 \6 \7 \8 \9])
(def numeric? (set numeric-range))
(def alpha-numeric-range (concat alpha-range numeric-range))
(def alpha-numeric? (set alpha-numeric-range))
(def repeat? #{\+ \* \? \{})
(def delim? #{\( \) \[ \] \{ \}})
(def meta? #{\^ \$ \.})
(def special? (set/union repeat? delim? meta? #{\|}))
(def tab? #{\tab})
(def return? #{\return})
(def newline? #{\newline})
(def formfeed? #{\formfeed})
(def whitespace? (set/union tab? return? newline? formfeed? #{\space}))
(def word? (conj alpha-numeric? \_))
(def not-word? (complement word?))
(def digit? numeric?)

(defprotocol IExpr
  (modify-last [_ f args]))

(defmacro defexpr [type & [args? & body]]
  (let [args? (if (vector? args?) args? [])
        body (if (seq args?) body (concat args? body))
        type-name (string/lower-case (name type))
        fn-name (symbol (str "->" type-name))]
    `(do
       (declare ~fn-name)
       (defrecord ~type [~@args? ~'expr]
         IObject
         (-str [_#] (str "#<" ~(name type) " " ~args? " " (pr-str ~'expr) ">"))
         (-repr [_#] (str "#<" ~(name type) " " ~args? " " (pr-str ~'expr) ">"))
         IPersistentCollection
         (-conj [_# x#]
           (~fn-name ~@args? (conj (cond-> ~'expr (vector? ~'expr) vec) x#)))
         IExpr
         (modify-last [_# f# args#]
           (~fn-name ~@args?
            (apply update-in ~'expr [(dec (count ~'expr))] f# args#)))
         ~@body)
       (defn ~fn-name
         [~@args? x#]
         (~(symbol (str "->" (name type)))
          ~@args?
          (cond (vector? x#) x# (list? x#) (vector x#) :else [x#]))))))

(defn char-at [input {:keys [pos length] :as s}]
  (when (and (>= pos 0) (< pos length))
    (nth input pos)))

(defprotocol IEdge
  (-epsilon? [_])
  (-traverse [_]))

(deftype Edge [epsilon? name f]
  IObject
  (-str [_] (str "#-"
                 (if epsilon? "E-" "-")
                 (or name (string/join (take 5 (str f))))
                 "->--"))
  (-repr [this] (-str this))
  IEdge
  (-epsilon? [_] epsilon?)
  (-traverse [_ {:keys [capture? pos length] :as state} input]
    (if epsilon?
      (f state input)
      (when-let [r (f input state)]
        [r input (reduce #(update-in %
                                     [:groups %2 :value]
                                     (fnil str "")
                                     (char-at input state))
                         (update-in state [:pos] inc)
                         capture?)]))))

(defn edge
  ([f] (->Edge nil nil f))
  ([s f] (->Edge nil s f)))

(defn epsilon
  ([f] (->Edge true nil f))
  ([s f] (->Edge true s f)))

(defn epsilon? [e] (and (instance? Edge e) (-epsilon? e)))

(defprotocol INfa
  (-compile [x i]))

(extend-protocol INfa
  Character
  (-compile [x i]
    (let [j (inc i)
          f #{x}]
      [j {i {(edge (pr-str f) (comp f char-at)) j}}])))

(defn compile-expr [x i]
  (reduce (fn [[i acc] x]
            (let [[j compiled] (-compile x i)]
              [j (merge acc compiled)]))
          [i {}]
          (:expr x)))

(defexpr Expr []
  INfa
  (-compile [x i]
    (compile-expr x i)))

(defn group-fn [i mark]
  (fn [s input]
    [true input (cond-> (assoc-in s [:groups i mark] (:pos s))
                  (= :start mark)
                  (update-in [:capture?] (fnil conj #{}) i)
                  (= :end mark)
                  (update-in [:capture?] disj i))]))

(defexpr Group [capture?]
  INfa
  (-compile [x i]
    (if capture?
      (let [j (inc i)
            [k compiled] (compile-expr x j)
            n (inc k)]
        [n (assoc compiled
                  i {(epsilon "^group" (group-fn i :start)) j}
                  k {(epsilon "group$" (group-fn i :end)) n})])
      (compile-expr x i))))

(defn compile-optional [x i]
  (let [j (inc i)
        [k compiled] (-compile x j)]
    [k (merge {i #{j k}} compiled)]))

(defn compile-kleene-star [x i]
  (let [j (inc i)
        [k compiled] (-compile x j)
        n (inc k)]
    [n (merge {i #{j n} k #{j n}} compiled)]))

(defn compile-kleene-plus [x i]
  (let [[j compiled] (-compile x i)
        k (inc j)
        n (inc k)]
    [k (merge {j #{i k}} compiled)]))

(defn flip [f]
  (fn [& args]
    (apply f (reverse args))))

(defexpr Repeat [from to]
  INfa
  (-compile [x i]
    (let [[expr] (:expr x)]
      (if (integer? to)
        (let [range (- to from)
              [j c] (if (zero? from)
                      (let [j (inc i)] [j {i #{j}}])
                      (reduce (flip compile-expr) i (repeat from expr)))
              [k d] (reduce (flip compile-optional) j (repeat range expr))]
          [k (merge c d)])
        (case from
          0 (compile-kleene-star expr i)
          1 (compile-kleene-plus expr i))))))

(defn bracket-edge [negate? j f]
  (if (instance? Escape f)
    (let [f (:f f)]
      [(edge f (cond-> f negate? complement)) j])
    [(edge f (comp (cond-> f negate? complement) char-at)) j]))

(defexpr Bracket [negate?]
  INfa
  (-compile [x i]
    (let [j (inc i)
          edges (->> (:expr x)
                     (map (partial bracket-edge negate? j))
                     (into {}))]
      [j {i edges}])))

(defexpr Choice []
  INfa
  (-compile [x i]
    (let [[k acc] (reduce (fn [[i acc] x]
                            (let [[j compiled] (-compile x i)]
                              [(inc j)
                               (-> acc
                                   (merge compiled)
                                   (update-in [:beg] (fnil conj #{}) i)
                                   (update-in [:end] (fnil conj #{}) j))]))
                          [(inc i) {}]
                          (:expr x))]
      [k (-> acc
             (dissoc :beg)
             (dissoc :end)
             (merge (into {} (map (fn [i] [i k]) (:end acc))))
             (assoc i (:beg acc)))])))

(defexpr Meta []
  INfa
  (-compile [x i]
    (let [[c] (:expr x)
          j (inc i)]
      (case c
        \. [j {i {(edge "." (constantly true)) j}}]
        \^ [j {i {(epsilon "^" (fn [{:keys [pos] :as state} input]
                                 [(zero? pos) input state])) j}}]
        \$ [j {i {(epsilon "$" (fn [{:keys [pos length] :as state} input]
                                 [(= pos length) input state])) j}}]))))

(defn boundary? [{:keys [pos length] :as state} input]
  [(or (= pos 0)
       (= pos length)
       (some-> (char-at input (update-in state [:pos] dec)) not-word?)
       (some-> (char-at input (update-in state [:pos] inc)) not-word?))
   input
   state])

(def escape-chars
  {\t (comp tab? char-at)
   \r (comp return? char-at)
   \n (comp newline? char-at)
   \f (comp formfeed? char-at)
   \s (comp whitespace? char-at)
   \S (comp (complement whitespace?) char-at)
   \w (comp word? char-at)
   \W (comp not-word? char-at)
   \d (comp numeric? char-at)
   \D (comp (complement numeric?) char-at)
   \b boundary?})

(def escape-edge
  {\t (partial edge "\\tab")
   \r (partial edge "\\return")
   \n (partial edge "\\newline")
   \f (partial edge "\\formfeed")
   \s (partial edge "\\s")
   \S (partial edge "\\S")
   \w (partial edge "\\w")
   \W (partial edge "\\W")
   \d (partial edge "\\d")
   \D (partial edge "\\D")
   \b (partial epsilon "\\b")})

(defrecord Escape [esc? c f]
  IObject
  (-repr [_] (str "#<\\" c ">"))
  INfa
  (-compile [x i]
    (let [j (inc i)]
      [j {i {((escape-edge c) f) j}}])))

(defn escape [c]
  (or (some->> c special? (->Escape nil c))
      (some->> c escape-chars (->Escape true c))
      (throw [::UnsupportedEscapeCharacter
              (str c " is not a supported escape character")])))

(defn read-while [f s]
  (loop [[c & [d :as more] :as s] s out []]
    (if c
      (cond (= \\ c) (recur (rest more) (conj out (escape d)))
            (f c) (recur more (conj out c))
            :else [out s])
      [out s])))

(defn read-until [f s]
  (read-while (complement f) s))

(defn read-group [[expr [a b :as s]]]
  (let [capturing? (not (and (= a \?) (= b \:)))
        s' (if capturing? s (drop 2 s))
        [expr' [_ & s'']] (read* [(->expr []) s'] \))]
    [(conj expr (->group capturing? expr')) s'']))

(defn index-of [coll x]
  (first (keep-indexed (fn [i y] (when (= x y) i)) coll)))

(defn parse-bracket-expr [[h :as expr]]
  (let [[char-set expr] (if (= \- h) [#{\-} (rest expr)] [#{} expr])]
    (loop [[a & [b c :as more]] expr char-set char-set esc []]
      (if a
        (cond (instance? Escape a)
              (if (:esc? a)
                (recur more char-set (conj esc a))
                (recur more (conj char-set (:c a)) esc))
              (and (alpha-numeric? a) (= \- b) (alpha-numeric? c))
              (if (< (index-of alpha-numeric-range a)
                     (index-of alpha-numeric-range c))
                (let [range (->> alpha-numeric-range
                                 (drop-while (partial not= a))
                                 (take-while (partial not= c)))]
                  (recur (drop 2 more) (apply conj char-set c range) esc))
                (throw [::InvalidRange (str "Range expr [" a b c "] invalid")]))
              (and b (= \- a))
              (throw [::InvalidRange (str "Range expr [" a b c "] invalid")])
              :else
              (recur more (conj char-set a) esc))
        (conj esc char-set)))))

(defn read-bracket-expr [[expr [c :as s]]]
  (let [[t s] (if (= c \^)
                [:^ (rest s)]
                [nil s])
        [form s'] (read-until #{\[ \]} s)
        [r s''] (condp = (first s')
                  \[ (throw [::NestedBracketExpression
                             "Bracket expressions [] cannot be nested"])
                  \] [(->bracket t (parse-bracket-expr form)) (rest s')]
                  (throw [::UnclosedBracketExpression
                          "Bracket expression [] must be closed"]))]
    [(conj expr r) s'']))

(defn partition-by [f [h & more]]
  (loop [last (f h) acc (list (list h)) [h & more] more]
    (if h
      (let [this (f h)]
        (if (= this last)
          (recur this (cons (cons h (first acc)) (rest acc)) more)
          (recur this (cons (list h) acc) more)))
      (reverse acc))))

(defn split-on [c coll]
  (->> coll
       (partition-by #{c})
       (remove (partial every? #{c}))))

(defn exp [x n]
  (reduce * (repeat n x)))

(defn charseq->int [coll]
  (loop [acc 0 exponent 0 [c & more] (reverse coll)]
    (if c
      (recur (+ acc (* (exp 10 exponent) (- (int c) 48))) (inc exponent) more)
      acc)))

(defn read-repeat-n [[expr s]]
  (let [[r [l & s']] (read-while (conj numeric? \,) s)]
    (if (= l \})
      (let [[from to & more] (split-on \, r)
            from (if (seq from) (charseq->int from) 0)
            to (when (seq to) (charseq->int to))]
        (if more
          (throw [::TooManyRepeatElements "> 2 elements in repeat {n,m}"])
          [[from to] s']))
      (throw [::UnclosedBraceExpression "Brace {} exprs must be closed"]))))

(defn read-repeat [init-ch [expr [c :as s] :as state]]
  (let [[range s'] (if (= \{ init-ch)
                     (read-repeat-n state)
                     [(case init-ch
                        \? [0 1]
                        \* [0 :infinity]
                        \+ [1 :infinity]) s])]
    [(modify-last expr #(->repeat %2 %3 %1) range) s']))

(defn read-choice [[expr s]]
  (let [choice (if (instance? Choice expr) expr (->choice expr))
        [expr' s'] (read* [(->expr []) s] #{\| \)})]
    [(conj choice expr') s']))

(defn read-meta [[expr [c & s]]]
  [(conj expr (->meta c)) s])

(defn read-special [[expr [c & tail :as s] :as state]]
  (cond (repeat? c) (read-repeat c [expr tail])
        (= \[ c) (read-bracket-expr [expr tail])
        (= \( c) (read-group [expr tail])
        (= \| c) (read-choice [expr tail])
        :else (read-meta [expr s])))

(defn read-expr [[expr s]]
  (let [[r s'] (read-until special? s)]
    [(apply conj expr r) s']))

(defn read* [[_ [c] :as state] return-on]
  (let [result (cond (and (char? return-on) (= c return-on)) :read/finished
                     (and (set? return-on) (return-on c)) :read/finished
                     (special? c) (read-special state)
                     :default (read-expr state))]
    (if (= :read/finished result)
      state
      (let [[forms' s'] result]
        (if (seq s')
          (recur [forms' s'] return-on)
          [forms' nil])))))

(defn read [pattern]
  (-> [(->expr [(->repeat 0 :infinity (->meta \.))]) pattern]
      (read* :read/EOF)
      (first)))

(defn compile [x]
  (let [expr (cond (string? x) (read x)
                   (satisfies? IExpr x) x
                   :else (throw [:UnknownExprType
                                 (str "Don't know how to compile" x)]))
        [end compiled] (-compile expr 0)]
    (assoc compiled end :match)))

(defprotocol IState
  (run-state [_])
  (eval-state [_])
  (exec-state [_]))

(deftype State [a s]
  IState
  (run-state [_] [a s])
  (eval-state [_] a)
  (exec-state [_] s))

(defn transition [nfa state]
  (let [[[state input] {:keys [pos length] :as groups}] (run-state state)
        follow (fn [[edge s]]
                 (let [[r input' groups] (-traverse edge groups input)]
                   (if r
                     (->State [s input'] groups)
                     (->State :fail groups))))]
    (if-let [head (nfa state)]
      (let [match? (= head :match)
            epsilon-edges (filter (comp epsilon? key) head)]
        (cond match?
              [(->State :match groups)]
              (or (integer? head) (keyword? head)) ;; epsilon edge
              [(->State [head input] groups)]
              (set? head) ;; epsilon edges
              (map #(->State [% input] groups) head)
              (and (>= pos length) (empty? epsilon-edges))
              [(->State :fail groups)]
              (>= pos length) ;; must be some epsilon edges left
              (map follow epsilon-edges)
              :else
              (map follow head)))
      (throw [::NoState (str "No state " (pr-str state) " in graph")]))))

(defn run [nfa state]
  (let [results (->> (transition nfa state)
                     (flatten)
                     (remove (comp #{:fail} eval-state)))
        matches (filter (comp #{:match} eval-state) results)]
    (if (seq matches)
      (first matches)
      (flatten (map (partial run nfa) results)))))

(def match? (comp #{:match} eval-state))
(def fail? (comp #{:fail} eval-state))

(defn ->state [s]
  (->State [0 s] {:pos 0 :length (count s)}))

(defn re-groups [re s]
  (let [result (run (compile re) (->state s))]
    (some-> (if (satisfies? ISeqable result)
              (when (some match? result) (first result))
              (when (match? result) result))
            (run-state))))

(defn matches? [re s]
  (= :match (first (re-groups re s))))

;; (re-groups "^(\\w+)://([\\w\\.]+)(:)?" "http://localhost.test:8888/thing/for?x=2#thing")

;; Local Variables:
;; eval: (define-clojure-indent (defexpr '(2 nil nil (1))))
;; End:
