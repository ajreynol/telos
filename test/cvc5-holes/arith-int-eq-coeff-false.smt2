; An integer equality with no integer solution. telos proves it; cvc5's reconstruction fails.
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (= (/ 1 2) (* (/ 1 3) (to_real x))) false)))
(check-sat)
