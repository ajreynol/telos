; IDOF_LEN: len(x) - n < len(y) implies (str.indexof x y n) --> -1.
; str-indexof-oob covers only n > len(x).
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.indexof (str.substr x n 1) x 1) (- 1))))
(check-sat)
