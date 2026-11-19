; BvPpAssert: an extract of a variable equal to a constant is solved, with
; purification skolems for the other bits.
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(declare-const z (_ BitVec 8))
(declare-const c Bool)
(assert (= ((_ extract 5 2) x) #b1010))
(assert (= #b11 ((_ extract 1 0) y)))
(assert (= ((_ extract 7 4) z) #b0001))
(assert (or c (= (bvadd x y) z)))
(check-sat)
