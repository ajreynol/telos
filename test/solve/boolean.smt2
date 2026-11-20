; Preprocessing solves every literal: only the checks at full effort remain.
(set-logic ALL)
(declare-fun p () Bool)
(declare-fun q () Bool)
(declare-fun r () Bool)
(assert p)
(assert (not q))
(assert (= r (not p)))
(check-sat)
