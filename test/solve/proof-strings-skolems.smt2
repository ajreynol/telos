; A full proof with a reduction whose skolem is a function (str.to_int).
(set-logic ALL)
(declare-fun x () String)
(assert (= (str.to_int x) 42))
(assert (= (str.len x) 1))
(check-sat)
