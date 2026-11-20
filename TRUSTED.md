# Trusted base

Everything the rewriter's correctness theorem relies on without a proof. Keep this
list current: `scripts/check-hygiene.sh` fails on any `unsafe`, `@[extern]` or
`implemented_by` in a file not named below.

## The specification

These define what the theorem *means*. A mistake here makes the theorem true of
the wrong thing, so review them as specifications, not as code.

- The Logos specification: the term datatype (`Cpc/LogosTerm.lean`), the
  translation `__eo_to_smt` (`Cpc/SmtTranslate.lean`), the SMT type checker
  `__smtx_typeof` (`Cpc/SmtTyping.lean`) and the model semantics
  (`Cpc/SmtModel.lean`, `Cpc/Spec.lean`). Logos commit pinned in `lakefile.toml`.
  The Eunoia programs compiled from `Cpc.eo` (`Cpc/Logos.lean`: the rules, the
  checker, `__eo_typeof`, `__eo_nil`) are not part of it; Logos proves the
  checker sound against this specification.
- `Telos/Core/Node/ToEo.lean`: the translation of `Node` to Logos terms. It assigns
  every node its meaning, so it must match how cvc5 prints that node in CPC. The
  per-operator part is a table (`Kind.eoShape`, `indexedEoShape`, `nodeEoShape`)
  giving each operator's CPC head symbol and arity. A declared constant
  (`Node.var`) is a `Term.UConst`, numbered by its name (`constId`, injective),
  and a bound variable a `Term.Var`. A skolem (`Node.skolem id cacheVals`, with
`SkolemId` in `Telos/Core/Node/SkolemId.lean`) is the CPC term cvc5 prints for
it, its identifier's operator applied to its cache values (`SkolemId.eoShape`):
`(@purify t)`, or `@int_div_by_zero`, which is a function, applied with
`APPLY_UF`. The nil terminator of
  `+`, `*`, the bit-vector operators, `str.++` and `distinct` depends on the type
  of the elements; it is a hand-written table (`typedNilOfType`) over the SMT
  type of the first element, given by `__smtx_typeof`. Datatype types
  (`TypeNode.datatype`, with its block `DtDecl`) mirror Logos's
  `Term.DatatypeType` constructor by constructor; constructors and selectors are
  the constants `Const.dtCons` and `Const.dtSel` (`Term.DtCons`, `Term.DtSel`),
  applied as spines (`nodeEoShape`). Their names are only printed, and are not
  part of the specification. `ToEo.lean` does not
  import `Cpc/Logos.lean` (`scripts/check-hygiene.sh` checks this for every
  specification file).
- `verification/TelosProofs/Core/Spec.lean`: the definition of `Node.Equiv`.

## Not trusted

The rewriting logic itself is outside the trusted base: every rewrite is a CPC
step checked by Logos's checker, whose soundness Logos proves
(`Certified.equiv`). A bug in any of the following can make telos miss a
rewrite or differ from cvc5, but not return a non-equivalent node:

- the theory strategies (`Telos/Rewriter/Theory/`) and the driver's control flow;
- the generated rule table (`Telos/Rewriter/Rules/Generated.lean`), its generator
  (`scripts/gen-rules.py`) and the matcher (`Telos/Rewriter/Rules/Match.lean`);
- `Node.ofEo` (`Telos/Core/Node/OfEo.lean`), the term order (`Telos/Core/Node/Order.lean`)
  and the printer (`Telos/Core/Node/Print.lean`).

The theorem is about `Node`s. The following turn text into nodes and nodes into
text, and are not covered by it:

- the SMT-LIB front end (`Telos/Frontend/Simplify.lean`) and Logos's parser, which is
  unverified. A parsing bug can make telos rewrite a different term than the one
  written; the result is still equivalent to the term telos read.
- proof output (`Telos/Core/Proof/`, `Telos/Core/RuleNames.lean`,
  `Telos/Preprocess/ProofExt.lean`, `Telos/Solver/EqProofCpc.lean`). A rewriter
  proof is checked by Logos's checker before it is printed; a preprocessing
  proof only with `--check-proof`; a refutation of the theory engine never.
  Each is meant to be checked by its reader (Ethos or Logos).

The theory engine (`Telos/Solver/`: the equality engine, UF, the engine, and
the builder of certificates `EqBuild.lean`) is not trusted either. An `unsat`
answer stands only if its conflict is certified:
- by the verified explanation (`Telos/Solver/Explain.lean`), whose reasons
  must be closed input literals. Its soundness is proven
  (`EE.explainLitV_sound`) whatever the state of the equality engine, since it
  checks what it uses as it goes;
- or else by a certificate (`Telos/Solver/EqProof.lean`) whose assumptions are
  input literals and which the proven checker accepts.

Either way the answer is correct (`Telos.solve_unsat_correct`). A bug in the engine can make it answer `unknown`,
or differ from cvc5, but not answer `unsat` on a satisfiable input.

A `sat` answer stands only if its model (`Telos/Solver/Model.lean`), built
from the equality engine, satisfies the input assertions: telos evaluates them
in it. The model builder is not trusted; the evaluation is proven to be
Logos's, in a well-formed Logos model of the model (`Solver.satisfies_sound`),
so the answer is correct (`Telos.solve_sat_correct`). A bug in the engine or
the builder can make telos answer `unknown`, but not `sat` on an
unsatisfiable input.

## Tools

- The Lean 4 kernel, compiler and runtime (`leanprover/lean4:v4.34.0`).

## `unsafe` / `@[extern]` / `implemented_by` in this repository

- `Telos/Core/Profile.lean`: the profiling probe `Profile.time cat key f`, whose
  definition is `f ()`, is `implemented_by` an `unsafe` function that also reads
  the clock and records the time in a global table (`unsafeBaseIO`). The
  theorem is about the definition; the compiled rewriter runs the
  implementation, so this is trusted to return `f ()` on every path, which it
  does in four lines. Probes sit in untrusted code only (the checker call
  `applyCmds`, the driver, the matcher and the arithmetic strategy), never in
  the specification files above.

## Axioms

No `sorry` and no declared `axiom`. `Telos.rewrite_correct` is proved in
`verification/TelosFull/Main.lean` (`lake -d verification build TelosFull`). The
default build, which CI runs, proves `Telos.rewrite_correct_of_logos`, which
takes the Logos theorems it uses as the hypothesis `[LogosFacts]`
(`verification/TelosProofs/Core/LogosFacts.lean`); `TelosFull` proves the instance
from Logos's proofs. Both builds fail if the theorem they prove uses any axiom
other than:

- `propext`, `Classical.choice` and `Quot.sound`; and
- the auxiliary axioms created by `native_decide` (43 at present). Each asserts
  that a decision procedure, run as compiled code, returned `true`, so they trust
  the **Lean compiler** in addition to the kernel. They come from Logos's proofs,
  which use `native_decide` throughout (577 uses, including its checker core),
  and enter through Logos's checker soundness proof (every CPC rule) and the
  congruence lemmas reused from `Cpc/Proofs/RuleSupport/Cong/`, so only into
  `Telos.rewrite_correct` (`TelosFull`): `rewrite_correct_of_logos` uses none.
  Trusting them was decided on 2026-11-12.
