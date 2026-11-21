# Theory-engine tests

Each `NAME.smt2` is a benchmark for `telos --theory-events`:

- `NAME.expected` is telos's output (the events, then the answer, or the error),
  checked by CI;
- `NAME.cvc5` is cvc5's trace, recorded with a cvc5 built with
  `cvc5-theory-events.patch`:
  `cvc5 --safe-mode=safe --ee-mode=central --produce-proofs -o theory-events NAME.smt2`.

`scripts/fuzz-solve.py --recorded --strict test/solve/*.smt2` compares the two
without cvc5, as CI does: every supported case has the same events as cvc5.
The `sat-*` cases have SAT structure, which telos's SAT solver (a port of
cvc5's MiniSat) solves: their traces are recorded with `--sat-solver=minisat`
added (cvc5's default SAT solver is CaDiCaL), with the logic's decision mode:
stop-only for QF_LRA (`sat-lra-ite` has skolem definitions that become
relevant), and justification where the script sets it
(`sat-uf-justification`). Their `sat` answers are certified by
the model check, with the arithmetic solver's values. An `unsat` of the SAT solver is
certified by the certificate of its refutation (`sat-or-unsat`; `sat-dt-lemmas*`
need the certificates of datatypes lemmas, `sat-lra-unsat*` the Farkas
certificates of arithmetic conflicts and lemmas, and `sat-lia-unsat` and
`sat-lia-dio-conflict` those of branches and of the Diophantine solver's
conflicts). `sat-lia-*` have branch and bound (`sat-lia-branch`), the
Diophantine solver's cuts (`sat-lia-dio-cut`, with the `pop` of its
speculative scope) and conflicts. With `--proofs`,
the refutation of each `unsat` is also checked by Ethos.
