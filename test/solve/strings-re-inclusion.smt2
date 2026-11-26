; the inclusion of regular expressions, whose search is exponential without a
; cache (`Telos/Core/ReIncl.lean`): in the second case, with an intersection in both
(set-logic QF_SLIA)
(declare-const x String)
(define-fun S () RegLan (re.* re.allchar))
(define-fun I () RegLan (re.inter (re.union (str.to_re "a-1") (str.to_re "a-2")) (re.++ (str.to_re "a-") S)))
(assert (or
  (and (str.in_re x (re.++ (str.to_re "wiz") S (str.to_re "foobar") S (str.to_re "baz/") S))
    (not (str.in_re x
      (re.++ (str.to_re "wiz") S (str.to_re "foo") re.allchar (str.to_re "ar") S (str.to_re "baz/") S))))
  (and (str.in_re x (re.++ (str.to_re "tag:") I (str.to_re ":end")))
    (not (str.in_re x (re.++ (str.to_re "tag:") I (str.to_re ":end") S))))))
(check-sat)
