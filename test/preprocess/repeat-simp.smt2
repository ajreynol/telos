; With arrays, UF and bit-vectors and no quantifiers, cvc5's default is
; --repeat-simp: non-clausal simplification runs again, and here solves a := false
; once x := 0 has simplified the second assertion.
(set-logic QF_AUFBVLIRA)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const x Int)
(declare-const y Int)
(declare-const s Real)
(assert (ite (= a (<= (* y 1) (abs -3))) (< (+ (to_real y) (to_real 0)) (to_real 1)) (ite (= (to_real 1) (/ (to_real y) (to_real -3))) c (= x 0))))
(assert (= (< 0 1) (=> a (= x 1))))
(assert (ite (=> (<= (* 0/1 s) (* (to_real 0) 0/1)) (= x 0)) (not (>= (- x 1) (* 0 1))) (not (is_int (to_real 0)))))
(check-sat)
