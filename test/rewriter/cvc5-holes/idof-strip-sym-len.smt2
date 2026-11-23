; IDOF_STRIP_SYM_LEN: strip a prefix of known length below the start index.
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.indexof (str.++ "a" x) x 1) (+ (- 1 0) (str.indexof x x 0)))))
(check-sat)
