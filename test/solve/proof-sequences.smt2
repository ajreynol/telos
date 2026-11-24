; telos: --dump-proofs
; Sequences: the injectivity of seq.unit, and extensionality.
(set-logic QF_SLIA)
(declare-sort E 0)
(declare-fun s () (Seq E))
(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))
(declare-fun z () Int)
(assert (or (distinct s (seq.update s 0 (seq.unit (seq.nth s 0))))
            (and (> z 10) (= (seq.len x) (seq.len y)) (= (seq.++ x (seq.unit z)) (seq.++ y (seq.unit 5))))))
(check-sat)
