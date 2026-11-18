; static-rewrite of string equalities (cvc5's rewriteStrEqualityExt):
; equal and constant ends unified, constant clashes, non-containment, and the
; str.replace cases; and theory-preprocess of str.from_code (a purification
; skolem with its eager reduction lemma). Matches cvc5 -o post-asserts
; --simplification=none --no-static-learning up to the orientation of
; equalities.
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const n Int)
(assert (= (str.++ x "ab") (str.++ y "b")))
(assert (= (str.++ x y) (str.++ x z)))
(assert (= "" (str.replace x y "a")))
(assert (= (str.replace x "a" "b") x))
(assert (not (= "1" (str.replace "" y "ab"))))
(assert (= (str.len (str.from_code n)) 1))
(check-sat)
