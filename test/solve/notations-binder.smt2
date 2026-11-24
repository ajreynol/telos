; numerals in real positions under a quantifier's variables
(set-logic ALL)
(assert (not (forall ((y Real)) (or (> y 0) (<= y 0)))))
(check-sat)
