# Trusted base

Everything the rewriter's correctness theorem relies on without a proof. Keep this
list current: `scripts/check-hygiene.sh` fails on any `unsafe`, `@[extern]` or
`implemented_by` in a file not named below.

## The specification

These define what the theorem *means*. A mistake here makes the theorem true of
the wrong thing, so review them as specifications, not as code.

- The Logos/CPC definitions: `Cpc.eo` compiled to `Cpc/Logos.lean` by
  `ethos-eoc`, the translation `__eo_to_smt` (`Cpc/SmtTranslate.lean`), the SMT
  type checker `__smtx_typeof` (`Cpc/SmtTyping.lean`) and the model semantics
  (`Cpc/SmtModel.lean`, `Cpc/Spec.lean`). Logos commit pinned in `lakefile.toml`.
- `Telos/Node/ToEo.lean`: the translation of `Node` to Logos terms. It assigns
  every node its meaning, so it must match how cvc5 prints that node in CPC.
- `verification/TelosProofs/Spec.lean`: the definition of `Node.Equiv`.

## Tools

- The Lean 4 kernel, compiler and runtime (`leanprover/lean4:v4.34.0`).

## `unsafe` / `@[extern]` / `implemented_by` in this repository

None.

## Axioms

No `sorry` and no new `axiom`. `verification/TelosProofs/Axioms.lean` fails the
build if `Telos.rewrite_correct` uses any axiom other than `propext`,
`Classical.choice` and `Quot.sound`.
