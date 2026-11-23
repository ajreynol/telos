; CTN_REPL_LEN_ONE_TO_CTN: (str.contains (str.replace x y x) z) --> (str.contains x z) if |z| <= 1.
; str-contains-repl-self-tgt-char needs (= (str.len z) 1), so |z| <= 1 is not covered.
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.contains (str.replace x y x) (str.substr y n 1)) (str.contains x (str.substr y n 1)))))
(check-sat)
