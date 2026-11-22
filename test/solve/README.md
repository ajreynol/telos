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
relevant, `sat-lra-ite-unsat` is a certified `unsat` with them), and justification where the script sets it
(`sat-uf-justification`). Their `sat` answers are certified by
the model check, with the arithmetic solver's values. An `unsat` of the SAT solver is
certified by the certificate of its refutation (`sat-or-unsat`; `sat-dt-lemmas*`
need the certificates of datatypes lemmas, `sat-lra-unsat*` the Farkas
certificates of arithmetic conflicts and lemmas, and `sat-lia-unsat` and
`sat-lia-dio-conflict` those of branches and of the Diophantine solver's
conflicts). `sat-lia-*` have branch and bound (`sat-lia-branch`), the
Diophantine solver's cuts (`sat-lia-dio-cut`, with the `pop` of its
speculative scope) and conflicts. `sat-uflra-*` combine UF and arithmetic:
a split of the care graph (`COMBINATION_SPLIT`) that arithmetic then refutes
(`sat-uflra-split-unsat`), and a model with the values of arithmetic for the
classes of the equality engine (`sat-uflra-model`); `sat-uflia-split*` the
same over integers. `sat-dtlia-*` have datatypes with integer fields (`sat-dtlia-fresh-dependent`: a
fresh value that a constructor term depends on): values
of arithmetic applications evaluated from their arguments (`sat-dtlia-model`),
fresh values of datatypes with integer fields (`sat-dtlia-fresh`), datatypes'
split skipped after arithmetic's lemma (`sat-dtlia-needcheck`), and a shared
disequality that rewrites to `true` (`sat-dtlia-constant-fact`). With `--proofs`,
the refutation of each `unsat` is also checked by Ethos.

The `*-unate-*` cases check the order of the disjuncts of unate lemmas, which
is cvc5's order of node ids (`NodeOrder`): of the nodes a rewrite creates
(`sat-uflia-unate-rewrite`), and of an equality split into two inequalities,
over integers (`sat-lia-unate-split`) and over reals (`sat-lra-unate-split`).
`sat-sets-*` exercise the theory of sets (`Telos/Solver/Theory/Sets.lean`): the
disequality lemma `SETS_DEQ` (`sat-sets-deq`), with the upward closure and the
proxies (`sat-sets-up-closure`), a conflict of a member of a set equal to the
empty set during the search (`sat-sets-mem-eq-conflict`), and certified `unsat`
answers whose refutations use the lemmas' and conflicts' certificates
(`Telos/Solver/SetsLemma.lean`, `EE.conflictOfSets`): with the downward closure
(`sat-sets-unsat-down-closure`) and the upward one (`sat-sets-unsat`).
