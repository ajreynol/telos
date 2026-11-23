; Two preprocessed assertions contradict each other: the SAT solver answers
; unsat after preregistering every atom, before asserting any.
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U) (declare-fun b () U) (declare-fun c () U)
(assert (not (= b (f b))))
(assert (not (= (f a) (f c))))
(assert (= (f a) (f (f a))))
(assert (= c (f a)))
(assert (not (= b (f (f b)))))
(check-sat)
