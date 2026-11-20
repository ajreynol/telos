; Preprocessing gives false: no events after the solver's initialization.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(assert (not p))
(check-sat)
