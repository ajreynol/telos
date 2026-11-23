; (/ c y) for an Int constant c and an Int y becomes (/ c.0 (to_real y)). No CPC rule.
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (/ (- 3) y) (/ (- 3.0) (to_real y)))))
(check-sat)
