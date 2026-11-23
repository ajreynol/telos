; A conflict in the central equality engine: (P (f a)) and (P (f b)) are merged
; by congruence, which merges true and false (EQ_CONSTANT_MERGE).
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun P (U) Bool)
(declare-fun a () U) (declare-fun b () U)
(assert (P (f a)))
(assert (not (P (f b))))
(assert (= (f (f a)) (f b)))
(assert (= a (f a)))
(check-sat)
