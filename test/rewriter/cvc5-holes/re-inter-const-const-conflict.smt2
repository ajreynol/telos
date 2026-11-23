; RE_INTER_CONST_CONST_CONFLICT with (str.to_re ""). Rules exist: telos proves it with re-inter-cstring-neg; cvc5's reconstruction fails.
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (re.inter (str.to_re "a") (str.to_re x) (str.to_re "")) re.none)))
(check-sat)
