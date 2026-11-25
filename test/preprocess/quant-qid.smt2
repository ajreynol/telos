; a nested quantifier is prenexed when its annotation is not a pattern
(set-logic ALL)
(declare-fun p (Int Int) Bool)
(declare-fun r (Int) Bool)
(assert (forall ((x Int)) (or (r x) (forall ((y Int)) (! (p x y) :qid id)))))
(assert (forall ((x Int)) (or (r x) (forall ((y Int)) (! (p y x) :pattern ((p y x)))))))
(check-sat)
