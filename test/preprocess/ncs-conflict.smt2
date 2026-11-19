; Non-clausal simplification: the circuit propagator finds a conflict (c is
; false, so (> x 0) is, so a and b are, against the first assertion), so the
; assertions become false.
(set-logic ALL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const x Int)
(assert (or a b))
(assert (=> a (> x 0)))
(assert (=> b (> x 0)))
(assert (or (not (> x 0)) c))
(assert (not c))
(check-sat)
