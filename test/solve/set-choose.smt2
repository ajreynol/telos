; set.choose: a member of a nonempty set, and a function of it
(set-logic ALL)
(declare-fun A () (Set Int))
(declare-fun a () Int)
(assert (set.member 10 A))
(assert (= a (set.choose A)))
(check-sat)
