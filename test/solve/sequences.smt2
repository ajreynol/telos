; telos: --dump-models
; Sequences: units, seq.nth, updates, and a model.
(set-logic ALL)
(declare-fun x () (Seq Int))
(declare-fun y () (Seq Int))
(declare-fun b () (Seq (Seq Bool)))
(declare-fun i () Int)
(assert (= (seq.len x) 3))
(assert (= (seq.nth x 1) 7))
(assert (= y (seq.update x 0 (seq.unit 5))))
(assert (seq.prefixof (seq.++ (seq.unit 5) (seq.unit i)) y))
(assert (= b (seq.unit (seq.++ (seq.unit true) (seq.unit false)))))
(check-sat)
