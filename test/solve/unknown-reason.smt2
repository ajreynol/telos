; an unknown, with its reason: telos says on standard error why
(set-logic ALL)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (forall ((y Int)) (> (f y) (* y y x))))
(check-sat)
(get-info :reason-unknown)
