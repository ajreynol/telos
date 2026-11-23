; strings: lengths and concatenation
(set-logic QF_SLIA)
(declare-const x String)
(declare-const y String)
(assert (= (str.++ x "ab") (str.++ "ba" y)))
(assert (< (str.len y) 1))
(check-sat)
