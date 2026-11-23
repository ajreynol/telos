; datatypes: a clash of constructors and a cycle
(set-logic QF_DT)
(declare-datatypes ((L 0)) (((nil) (cons (hd Bool) (tl L)))))
(declare-const x L)
(declare-const y L)
(assert (or (= x nil) (= x (cons true y))))
(assert ((_ is cons) x))
(assert (= y (cons false x)))
(check-sat)
