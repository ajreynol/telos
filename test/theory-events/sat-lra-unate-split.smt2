(set-logic QF_LRA)(declare-fun x () Real)(declare-fun y () Real)(declare-fun z () Real)
(assert (not (= (+ x y) 2.0)))
(check-sat)
