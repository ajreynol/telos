; RE_ANDOR_CONST_REMOVE (re.union): drop (str.to_re c) when c is in another member.
; re-union-const-elim exists; cvc5's elaboration fails.
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (re.union (str.to_re "b") (re.range "a" "c") (str.to_re x)) (re.union (re.range "a" "c") (str.to_re x)))))
(check-sat)
