; cvc5 --dump-proofs --proof-format-mode=cpc: this needs a TRUST_THEORY_REWRITE step
(set-logic ALL)
(declare-const s (Set Int))
(assert (not (= (set.union s s) s)))
(check-sat)
