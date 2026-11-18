; CTN_STRIP_ENDPT with a str.from_int endpoint: a needle ending in a non-digit cannot end in it.
; str-overlap-endpoints-ctn needs the stripped endpoints to be constants; cvc5's elaboration fails (trust id THEORY_REWRITE).
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.contains (str.++ x (str.from_int n)) "ab") (str.contains x "ab"))))
(check-sat)
