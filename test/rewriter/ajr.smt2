(set-logic ALL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const x Int)
(declare-fun f (Bool) Bool)
(simplify (f (or a (= (= a b) (= b a)))))

