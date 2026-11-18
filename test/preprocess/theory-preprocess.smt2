; The theory-preprocess pass: term formula removal (non-Boolean ite, Boolean
; terms inside terms) and arithmetic operator elimination (div, mod, /,
; to_int, is_int, abs), with skolem lemmas after the (assert true). Matches
; cvc5 -o post-asserts --simplification=none --no-static-learning up to the
; numbering of skolems and Int/Real casts (see scripts/fuzz-pp.py). Lemmas of
; skolems compared with each other are not: telos's order on skolems is not
; cvc5's (node ids, i.e. creation order).
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(declare-const r Real)
(declare-const a Bool)
(declare-const b Bool)
(declare-fun f (Int) Int)
(declare-fun g (Bool) Int)
(assert (> (f (ite a x (ite b y 0))) 3))
(assert (< (ite a x (ite b y 0)) (g (and a b))))
(assert (> (div x y) 3))
(assert (> (mod x 3) (f x)))
(assert (> (abs x) 3))
(assert (> (to_int r) 3))
(assert (is_int r))
(assert (> (div x 0) 3))
(check-sat)
