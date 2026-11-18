; Theory preprocessing (ppRewrite) of bit-vectors and datatypes: datatype
; updaters expanded to an ite on the tester (then purified), equalities of
; tuples split (static-rewrite), the bit-vector overflow predicates eliminated,
; and UltAddOne. Matches cvc5 -o post-asserts --no-static-learning
; up to the order of commutative arguments.
(set-logic ALL)
(declare-datatypes ((Lst 0)) (((cons (head Int) (tail Lst)) (nil))))
(declare-const l Lst)
(declare-const x Int)
(declare-const y Int)
(declare-const tp (Tuple Int Int))
(declare-const a (_ BitVec 4))
(declare-const b (_ BitVec 4))
(assert (= l ((_ update head) l x)))
(assert (= tp (tuple x y)))
(assert (bvuaddo a b))
(assert (bvsmulo a b))
(assert (bvult a (bvadd b #b0001)))
(check-sat)
