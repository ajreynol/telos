; An assertion that rewrites to false: the pipeline is in conflict
; (AssertionPipeline::markConflict), and its only assertion is false.
(set-logic ALL)
(declare-const a Bool)
(declare-const x Int)
(assert a)
(assert (and (> x 0) (> 1 2)))
(assert (not a))
(check-sat)
