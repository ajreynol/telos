; Preprocessing (cvc5's ProcessAssertions) as ported so far: top-level
; conjunctions split (AssertionPipeline::push_back), the rewrite pass, conflicts,
; and define-fun as a macro. Matches cvc5 -o post-asserts with
; --simplification=none --no-static-learning, apart from cvc5's define-fun lines
; and the (assert true) it keeps in their place.
(set-logic ALL)
(declare-sort U 0)
(declare-const u U)
(declare-const v U)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const a Bool)
(declare-const b Bool)
(declare-fun f (Int) Int)
(define-fun g ((w Int)) Int (+ w 1))
(assert (= x (+ y 1)))
(assert (or a (> (f x) (g y))))
(assert (and a (and (< x 10) (not (= u v)))))
(assert (not (or a b)))
(assert (xor a (> (g z) 0)))
(assert true)
(check-sat)
