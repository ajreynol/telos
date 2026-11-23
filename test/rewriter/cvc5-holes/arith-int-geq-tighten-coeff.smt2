; Integer tightening under a rational coefficient. Rules exist: telos proves it with arith_poly_norm_rel and arith-int-geq-tighten; cvc5's reconstruction fails.
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (>= (* (/ 1 3) (to_real x)) (/ 3 2)) (>= x 5))))
(check-sat)
