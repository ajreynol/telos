; Extended functions whose reductions have bounded quantified formulas:
; instantiated at last call, over the model's ranges.
(set-logic ALL)
(declare-fun x () String)
(declare-fun z () String)
(assert (= (str.len x) 3))
(assert (not (= x (str.rev x))))
(assert (not (str.contains x "a")))
(assert (= (str.at x 0) "b"))
(assert (not (str.<= z "aB")))
(check-sat)
