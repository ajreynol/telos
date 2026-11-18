; Non-clausal simplification (cvc5's NonClausalSimp): literals learned by the
; circuit propagator, solved into substitutions (printed as define-fun, the
; variables no longer declared) or used as constant propagations, and applied
; to the assertions. Matches cvc5 -o post-asserts --no-static-learning up to the
; order of the define-funs.
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const w Int)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
; x := (+ 1 y), y := (+ 2 z)
(assert (= x (+ y 1)))
(assert (= y (+ z 2)))
(assert (> (f x) z))
; a := true, then b := true by propagation through the or
(assert a)
(assert (or (not a) b))
(assert (=> b (> w 0)))
; a constant propagation: (g w) := 3
(assert (= (g w) 3))
(assert (> (g w) (f w)))
; c := (not (= w 5))
(assert (not (= c (= w 5))))
(check-sat)
