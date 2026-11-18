; RE_CHAR_IN_STR_STAR: (str.in_re c (re.* (str.to_re x))) --> (= x c) for a one-character constant c.
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.in_re "b" (re.* (str.to_re x))) (= x "b"))))
(check-sat)
