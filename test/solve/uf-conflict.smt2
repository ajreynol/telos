; cvc5 finds the conflict by propagation: the UF solver propagates a literal
; that is asserted false, and the SAT solver asks for its explanation.
(set-logic QF_UFLIA)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun x () Int)
(declare-fun g (U) Int)
(assert (= a (f b)))
(assert (= b (f a)))
(assert (not (= (f (f a)) a)))
(assert (> (g a) x))
(check-sat)
