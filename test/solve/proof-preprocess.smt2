; preprocessing solves x, then the rest is refuted
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (= x (+ y 1)))
(assert (or (< x y) (= y (+ x 2))))
(check-sat)
