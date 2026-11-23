# What telos proves

This is the detailed account of telos's correctness theorems: what they state,
how they connect to Logos's semantics, how `sat` and `unsat` answers are
certified, and what the theorems rely on. Paths are relative to the repository
root. For an overview, see the [front page](../README.md).

The theorems are in `verification/TelosFull/Main.lean`:

```sh
lake -d verification build              # proofs, with the Logos theorems they use as a hypothesis (CI)
lake -d verification build TelosFull    # also Logos's proofs: the unconditional theorems
```

The default build, which CI runs, proves them with the Logos theorems they use
as a hypothesis (`[LogosFacts]`, `verification/TelosProofs/Core/LogosFacts.lean`);
`TelosFull` discharges that hypothesis from Logos's proofs.

## The solver

```lean
theorem Telos.solve_unsat_correct (h : Frontend.solve sc u vs = .ok .unsat) : sc.satisfiability false
theorem Telos.solve_sat_correct   (h : Frontend.solve sc u vs = .ok .sat)   : sc.satisfiability true
```

`Frontend.solve sc u vs` is the answer of `telos --solve` on the parsed script
`sc`, with the user's options `u` (and `vs`, the SAT solver even for a
conjunction of literals): preprocessing, then the theory engine, with the SAT
solver. The conclusion is in **Logos's semantics**:

```lean
-- telos (verification/TelosProofs/Solver/Correct.lean)
def Frontend.Script.satisfiability (sc : Script) (b : Bool) : Prop :=
  ∃ as, inputAssertions sc = .ok as ∧ eo_satisfiability (Preprocess.inputNode as).toEo b

-- Logos (Cpc/Spec.lean, Cpc/SmtModel.lean)
def eo_satisfiability (t : Term) (b : Bool) : Prop := smt_satisfiability (__eo_to_smt t) b
inductive smt_satisfiability : SmtTerm → Bool → Prop
  | intro_true  (t) : (∃ M, model_wf M ∧ __smtx_model_eval M t = .Boolean true) → smt_satisfiability t true
  | intro_false (t) : (∀ M, model_wf M → __smtx_model_eval M t = .Boolean false) → smt_satisfiability t false
```

So the meaning of a script's answer is a **composition** of three maps, and
the theorems are about the last two:

| step | from → to | by | status |
|---|---|---|---|
| 1. front end | SMT-LIB text → `List Node` (the assertions, `define-fun`s expanded) | Logos's parser, `Frontend.inputAssertions` | not verified |
| 2. translation | `Node` → Logos `Term` (the CPC/Eunoia term) | `Node.toEo` (`Telos/Core/Node/ToEo.lean`); the conjunction `inputNode` | specification (`TRUSTED.md`) |
| 3. semantics | Logos `Term` → satisfiable or not | Logos: `__eo_to_smt` to an SMT term, then `smt_satisfiability` over well-formed models (`model_wf`) and Logos's evaluation (`__smtx_model_eval`) | Logos's specification (`TRUSTED.md`) |

`unsat` means: the conjunction of the assertions, translated, evaluates to
`false` in every well-formed model; `sat`, that it evaluates to `true` in one.
This is the semantics in which Logos proves its checker sound, so an answer
means what a CPC refutation of the same term, checked by Logos, would
establish.

**The general form.** The two theorems are corollaries of
`Telos.solveScript_unsat_correct` and `solveScript_sat_correct`, about
`Frontend.solveScript` with any of its options (events, preprocessing, proofs,
cvc5's node order, the SAT solver), which `telos --theory-events` also runs:

```lean
theorem Telos.solveScript_unsat_correct (sc u) (ee pp wp co vs te ev : Bool)
    (h : Frontend.solveScript sc u ee pp wp co vs te ev = .ok (out, r)) (hu : r.answer = .unsat)
    (hin : Frontend.ppInput sc u = .ok (opts, as)) (hb : ∀ a ∈ as, HasBoolType a.toEo) :
    ∀ M, model_wf M → ¬ TrueIn M (Preprocess.inputNode as).toEo
theorem Telos.solveScript_sat_correct (sc u) (ee pp wp co vs te ev : Bool)
    (h : Frontend.solveScript sc u ee pp wp co vs te ev = .ok (out, r)) (hs : r.answer = .sat)
    (hin : Frontend.ppInput sc u = .ok (opts, as)) :
    ∃ M, model_wf M ∧ TrueIn M (Preprocess.inputNode as).toEo
```

Both are about the input assertions as read, not the preprocessed ones. The
`sat` theorem does not depend on preprocessing at all, since it checks the
model against the input. The `unsat` theorem uses that preprocessing preserves
models (a skolem is the term it purifies, in Logos's semantics).

## How the proofs compose with Logos's

Logos's correctness theorem is the soundness of its checker
(`proven_from_empty_valid`): a CPC proof that the checker accepts proves a
formula that is true in every well-formed model. telos uses it for every step
it justifies by a CPC rule (in the rewriter, the preprocessor and the theories'
certificates), through the class `LogosFacts`, which restates the Logos
theorems telos uses: the checker's soundness, congruence, and facts about the
evaluation (a Boolean term evaluates to a Boolean, the operations on maps and
sets). The default build proves telos's theorems from `LogosFacts`
(`Telos.Frontend.solve_unsat` and `solve_sat`); `TelosFull` proves each field of
`LogosFacts` from the Logos theorem it restates, and so the unconditional
theorems.

telos's own proofs cover the rest: the certificate checkers (unit propagation,
Farkas combinations, equality proofs), the verified explanation, the model
evaluator, and the step from "not true in any model" to Logos's "false in every
model".

## How answers are certified

The search itself (the SAT solver, cvc5's MiniSat port, and the theory solvers)
is not trusted.

**`unsat`.** An `unsat` stands only if a certificate of the refutation checks,
and the checkers are proved sound:

- with the SAT solver (`Telos/Solver/SatProof.lean`, `SatProof.Cert.check_sound`),
  the clauses the solver used, each with its justification:
  - a clause of the CNF of an input formula, or a definition of a connective's
    literal (Tseitin);
  - a theory conflict, certified by an equality proof (`EqProof.check_sound`,
    `Telos/Solver/EqProof.lean`) whose theory steps are CPC rules run through
    Logos's checker;
  - an arithmetic conflict, certified by a Farkas combination
    (`Telos/Solver/LinCert.lean`);
  - a theory lemma, with a proof by CPC rules that it is valid (the datatypes,
    sets, strings, quantifiers and nonlinear arithmetic lemmas,
    `Telos/Solver/NlLemma.lean`). A lemma whose proof telos lacks (some of the
    strings lemmas, so far) is left out of the certificate, so a refutation
    that needs it is `unknown`, never an unchecked `unsat`.

  The clauses the solver learned, and finally the empty clause, are rechecked
  by reverse unit propagation. Every check is recomputed from the clauses, not
  taken from the solver;
- for a conjunction of literals without the SAT solver, the equality engine's
  explanation of the conflict, recomputed by a proved explanation
  (`EE.explainLitV_sound`, `Telos/Solver/Explain.lean`), or an equality proof.

**`sat`.** telos builds a model from the equality engine and the theories'
values (`Telos/Solver/Model.lean`), and evaluates the input assertions in it.
The model builder is not trusted; the evaluator is proved to compute Logos's
evaluation, in a well-formed Logos model built from the model
(`Solver.satisfies_sound`). So a `sat` holds whatever the solver did.

**In practice**, a bug in the search, the theory solvers, the model builder or
the certificate builders cannot make telos answer wrongly. It can make telos
answer `unknown`, which it then explains: a certificate that did not check is
reported as such (`cert-unsat/…`, `cert-sat/…`), not hidden.

## The rewriter and the preprocessor

```lean
theorem Telos.rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t)
theorem Telos.preprocess_correct (as : List Node) (h : (Preprocess.inputNode as).WellTyped)
    (opts : Preprocess.PPOptions := {}) :
    (Preprocess.inputNode as).Equiv (Preprocess.preprocessCert as opts).1
```

`t.Equiv s` (`verification/TelosProofs/Core/Spec.lean`) says that the CPC
formula `(= t s)` is well typed and valid: `t` and `s` have the same type and
the same value in every well-formed model, which is what a CPC proof of
`(= t s)` establishes. `preprocessCert as` is the conjunction of the
preprocessed assertions, as a certified rewrite of `inputNode as`.

## How steps are justified

**CPC is the vocabulary.** The rules of CPC (RARE rewrites, theory rewrites,
preprocessing rules such as `skolem_intro` or `arith_reduction`) are what each
step is justified by, and Logos proves each of them sound.

**Proof checking is the baseline, not the only method.** The simplest way to
justify a step is to build its CPC proof and run Logos's checker on it; one
theorem about checked steps then covers every rewrite and every pass. telos
does this where it is cheap: a rewrite rule applied to one term. But checking
re-does, in Logos's tree-recursive programs, work telos has already done, and
on large or highly shared terms it is far too slow. So the rewriter and the
preprocessor use faster methods where it matters, each with a Lean proof, done
once, that it establishes what a checked proof would:

- *static* steps (`Telos/Core/Static.lean`): a cheap side condition, with a
  theorem that the checker would accept the step (arithmetic normalization);
- *semantic* steps (`Telos/Core/Semantic.lean`): a side condition decided on
  telos's own terms, with a theorem that it implies equivalence (reorganizing
  the pipeline's conjunction, substitution, Boolean propagation).

Terms are shared as DAGs: nodes carry their hash, compare in constant time when
they are the same in memory, and the fast methods never traverse shared terms
as trees.

**Printed proofs are for external auditing.** The CPC proofs telos prints
(`--proof`, checked by Ethos) let anyone audit a result without trusting telos
or Lean; the theorems do not rely on them. A result is computed the same way
whether or not a proof is asked for (proven: `simplify_output`,
`postAssertsFull_output`), and the proof is built afterwards from its
certificate. Steps justified by a Lean theorem are turned into CPC proofs from
the data their side conditions checked (`Telos/Preprocess/ProofExt.lean`), and
large proofs are printed with shared terms defined once
(`Telos/Core/Proof/Shared.lean`).

## What the theorems rest on

- **The specification** ([`TRUSTED.md`](../TRUSTED.md)): Logos's semantics of
  CPC (its terms, the SMT translation, the type checker and the model
  semantics, at the pinned commit), telos's translation of its nodes to Logos
  terms (`Telos/Core/Node/ToEo.lean`), and the definitions of `Node.Equiv` and
  `Script.satisfiability`. A mistake there makes the theorems true of the wrong
  thing, so they are reviewed as specifications.
- **Axioms**: Lean's `propext`, `Classical.choice` and `Quot.sound` only. No
  `sorry`, no declared axiom, and no `native_decide` (Logos's proofs do not use
  it); `#assert_axioms` fails the build otherwise
  (`verification/TelosProofs/Axioms.lean`).
- **Lean**: the kernel; the compiler and the runtime too, for running telos.

## What they do not cover

- **Parsing and printing.** The theorems are about the parsed script. Logos's
  SMT-LIB parser and telos's front end are not verified, nor is the printing of
  the answer; a parsing bug could make telos solve a different problem than the
  one written.
- **Completeness.** Nothing says telos answers `sat` or `unsat`; `unknown` is
  always allowed.
- **Agreement with cvc5.** That telos makes cvc5's inferences, in cvc5's order,
  is tested by differential fuzzing on cvc5's traces, not proved.
- **Printed proofs.** The CPC proofs telos prints (`--proof`) are for external
  auditing, by Ethos or Logos; the theorems do not rely on them.
