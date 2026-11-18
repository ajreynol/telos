; STR_LEQ_ID: (str.<= x x) --> true (known; see Telos/Theory/Strings.lean).
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.<= x x) true)))
(check-sat)
