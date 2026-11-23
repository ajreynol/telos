; cvc5 --dump-proofs --proof-format-mode=cpc: this needs a TRUST_THEORY_REWRITE step
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (/ (to_real x) (to_real y)) (/ x y))))
(check-sat)
