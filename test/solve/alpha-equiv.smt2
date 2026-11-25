; alpha-equivalence up to the order of variables and of disjuncts
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun Q (U) Bool)
(declare-fun R (U U) Bool)
(assert (forall ((i U) (j U)) (or (P i) (Q j) (R i j))))
(assert (not (forall ((y U) (x U)) (or (R x y) (Q y) (P x)))))
(check-sat)
