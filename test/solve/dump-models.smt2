; run with --dump-models: the model follows sat
; telos: --dump-models
(set-logic QF_UFLIA)
(declare-fun g (Int) Int)
(declare-const a Int)
(declare-const c Int)
(assert (= (g a) (+ c 1)))
(assert (distinct a c))
(assert (>= c 0))
(check-sat)
