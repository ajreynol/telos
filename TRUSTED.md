# Trusted base

Everything the solver's soundness guarantee relies on without a proof. Keep this
list current: `scripts/check-hygiene.sh` fails on any `unsafe`, `@[extern]` or
`implemented_by` in a file not named below.

## Always trusted

- The Lean 4 kernel, compiler and runtime (`leanprover/lean4:v4.34.0`).
- The Logos/CPC definitions as the **specification**: `Cpc.eo` compiled to
  `Cpc/Logos.lean` by `ethos-eoc`, and the SMT-LIB model semantics in
  `Cpc/SmtModel.lean` (Logos commit pinned in `lakefile.toml`).
- The Logos s-expression reader and SMT-LIB parser (unverified in Logos). The
  solver and the proof it emits must go through the same parser.

## Temporary (until proven)

- The proof printer (`Solver/Print/`), until `parse (print log) = log` is proven
  (milestone M2). Not written yet.

## `unsafe` / `@[extern]` / `implemented_by` in the solver

None.

## Axioms

No `sorry` and no new `axiom`. `#print axioms` on the end-to-end theorems must
show only `propext`, `Classical.choice` and `Quot.sound` (checked in CI once
those theorems exist).
