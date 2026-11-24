; Binders that reuse a name: a `let` or a macro must not be captured by them.
(set-logic ALL)
(declare-sort U 0)
(declare-fun p (U U) Bool)
(declare-fun a () U)
(declare-fun b () U)
(define-fun q ((u U)) Bool (exists ((x U)) (not (= x u))))
; (the `let` is of the outer `x`: captured, `(= y x)` would be true)
(assert (forall ((x U)) (let ((y x)) (forall ((x U)) (= y x)))))
; a shadowed `let` of a numeral
(assert (let ((n 2)) (= 7 (let ((n 7)) n))))
(assert (not (= a b)))
(check-sat)
