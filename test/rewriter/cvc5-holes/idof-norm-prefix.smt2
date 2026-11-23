; IDOF_NORM_PREFIX: characters before the start index are replaced by "A".
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.indexof (str.++ "a" x) "a" 1) (str.indexof (str.++ "A" x) "a" 1))))
(check-sat)
