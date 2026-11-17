; Quantifiers (cvc5's QuantifiersRewriter, first stage): exists elimination,
; prenex merging, constant bodies, miniscoping over and/ite, unused variables.
; cvc5 prints the variables of miniscoped quantifiers with fresh names.
(set-logic ALL)
(declare-const a Bool)
(declare-const x Int)
(declare-fun P (Int) Bool)
(simplify (forall ((y Int)) true))
(simplify (forall ((y Int)) a))
(simplify (exists ((y Int)) (P y)))
(simplify (forall ((y Int)) (forall ((z Int)) (P (+ y z)))))
(simplify (forall ((y Int) (z Int)) (P y)))
(simplify (forall ((y Int)) (and (P y) a (P (+ y 1)))))
(simplify (forall ((y Int)) (ite a (P y) (P x))))
(simplify (exists ((y Int)) (forall ((z Int)) (P (+ y z)))))
(simplify (forall ((y Int)) (and a (forall ((z Int)) (P z)))))
