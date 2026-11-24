; A full proof with reductions of extended functions (string_reduction).
(set-logic ALL)
(declare-fun s () String)
(assert (not (= (str.update (str.++ "a" s "b") (+ 1 (str.len s)) "a") (str.++ "a" s "a"))))
(check-sat)
