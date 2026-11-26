; an internal fact of strings derived twice, with other premises: its proof is
; from the premises of the edge it made (`assertInternalFact`)
(set-logic ALL)
(declare-fun x () String)
(assert (distinct (str.replace x (str.at x 0) "") (str.substr x 1 (str.len x))))
(check-sat)
