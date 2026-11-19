(set-logic ALL)
(declare-const x Int)
(declare-const r Real)
(declare-const t (Tuple Int Bool Int))
(declare-const bx (_ BitVec 4))
(declare-const by (_ BitVec 4))
(declare-const s String)
(declare-const c Bool)
(declare-const S (Set Int))
; tuple updater, expanded to a tuple
(assert (> ((_ tuple.select 0) ((_ tuple.update 2) t x)) 3))
; bit-vectors' SolveEq, and (= b (bvnot b))
(assert (or c (= #b1000 (bvadd by #b1111))))
(assert (xor (= bx (bvnot bx)) c))
; (= (to_real x) 0.0) solved as x := 0
(assert (= (to_real 0) (to_real x)))
; the str.substr cases of rewriteStrEqualityExt, and CTN_SPLIT's order
(assert (or c (= "" (str.substr s 0 1)) (not (str.contains "ab" (str.substr s 0 1)))))
; a set constant in normal form: a constant propagation
(assert (= (set.singleton (set.choose S)) (set.union (set.singleton 2) (set.singleton 0))))
(check-sat)
