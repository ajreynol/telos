# telos

A statically verified, proof-producing SMT solver written in Lean 4, built on
[Logos](https://github.com/ajreynol/logos), the CPC proof checker. See
[`docs/verified-solver-plan.md`](docs/verified-solver-plan.md) for the design and
milestones, and [`TRUSTED.md`](TRUSTED.md) for the trusted base.

## Layout

Two Lake projects, so the solver binary builds without Mathlib:

- `.` (package `Solver`): the solver and the `telos` executable. Requires Logos's
  root package `Cpc` (checker and parser).
- `verification/` (package `SolverVerification`): correctness proofs. Requires
  `Solver`, Logos's `LogosVerification` (model semantics, rule proofs) and Mathlib.

## Building

```sh
lake build                              # solver
lake -d verification exe cache get      # Mathlib binaries (once)
lake -d verification build              # proofs
bash scripts/check-hygiene.sh           # no sorry/axiom; trusted code is listed
```

## Updating Logos

Logos is pinned to one commit in **both** `lakefile.toml` (`Cpc`) and
`verification/lakefile.toml` (`LogosVerification`). Change both `rev`s together,
then run `lake update Cpc` and `lake -d verification update`.

To develop against a local Logos checkout, temporarily replace the `git`/`rev`
lines with `path = "../logos"` (and `path = "../../logos/verification"`), and do
not commit that change.
