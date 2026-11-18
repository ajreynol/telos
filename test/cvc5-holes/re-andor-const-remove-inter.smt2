; RE_ANDOR_CONST_REMOVE (re.inter): drop a member that contains a constant (str.to_re c) also in the intersection.
; Rules exist (re-inter-cstring, aci_norm), but cvc5's elaborator only handles results that are str.to_re or re.none.
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (re.inter (str.to_re "b") (str.to_re x) re.allchar) (re.inter (str.to_re "b") (str.to_re x)))))
(check-sat)
