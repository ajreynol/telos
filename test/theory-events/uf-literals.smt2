; A conjunction of UF literals, one of them an `and` after static learning
; (`distinct`): its literals are asserted once each.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(assert (not (= (f a) (f b))))
(assert (distinct a (f a) b))
(check-sat)
