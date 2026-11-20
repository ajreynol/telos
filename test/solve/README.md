# Theory-engine tests

Each `NAME.smt2` is a benchmark for `telos --theory-events`:

- `NAME.expected` is telos's output (the events, then the answer, or the error),
  checked by CI;
- `NAME.cvc5` is cvc5's trace, recorded with a cvc5 built with
  `cvc5-theory-events.patch`:
  `cvc5 --safe-mode=safe --ee-mode=central --produce-proofs -o theory-events NAME.smt2`.

`scripts/fuzz-solve.py --recorded test/solve/*.smt2` compares the two without
cvc5. Until the UF solver is in (milestone 2 of
`docs/theory-engine-plan.md`), telos has no propagations, so only `boolean` and
`false` agree.
