; In pure linear quantifier-free arithmetic, cvc5's default is
; --arith-rewrite-equalities: static-rewrite turns (= a b) into two inequalities.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (or (= x (+ y z)) (> x 3)))
(assert (> y z))
(check-sat)
