# Theory-engine tests

Each `NAME.smt2` is a benchmark for `telos --theory-events`:

- `NAME.expected` is telos's output (the events, then the answer, or the error),
  checked by CI;
- `NAME.cvc5` is cvc5's trace, recorded with a cvc5 built with
  `cvc5-theory-events.patch`:
  `cvc5 --safe-mode=safe --ee-mode=central --produce-proofs -o theory-events NAME.smt2`.

`scripts/fuzz-solve.py --recorded --strict test/solve/*.smt2` compares the two
without cvc5, as CI does: every supported case has the same events as cvc5.
`unsupported-ite` is skipped, because it has SAT structure. With `--proofs`,
the refutation of each `unsat` is also checked by Ethos.
