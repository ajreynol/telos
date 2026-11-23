; cvc5 --dump-proofs --proof-format-mode=cpc: this needs a TRUST_THEORY_REWRITE step
(set-logic ALL)
(declare-const x Int)
(assert (not (is_int (to_real x))))
(check-sat)
