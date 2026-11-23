; cvc5 finds the conflict by propagation: the central equality engine
; propagates (= (f b) (f (f (f b)))), which is asserted false, and the SAT
; solver asks for its explanation.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(assert (= a (f b)))
(assert (= b (f a)))
(assert (not (= (f (f a)) a)))
(check-sat)
