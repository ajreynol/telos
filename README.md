# telos

A **verified rewriter for SMT**, written in Lean 4. It is a port of
[cvc5](https://github.com/cvc5/cvc5)'s rewriter, with a machine-checked proof that
every rewrite preserves equivalence. The semantics come from
[Logos](https://github.com/ajreynol/logos), the CPC proof checker, so "equivalent"
means the same thing that a CPC proof of `(= t (rewrite t))` would establish.

Every rewrite step is an instance of a CPC rule (a RARE rewrite or a theory
rewrite), found by a matcher generated from the Eunoia signature and checked by
Logos's verified rule programs. The choice of which rule to apply follows cvc5's
theory rewriters and is tested against cvc5 by differential fuzzing.

```lean
theorem Telos.rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t)
```

See [`docs/design.md`](docs/design.md) for the architecture and roadmap, and
[`TRUSTED.md`](TRUSTED.md) for what the theorem relies on.

## Layout

Two Lake projects, so the rewriter builds without Mathlib:

- `.` (package `Telos`): `Node`, its translation to Logos terms, the rewriter and
  the `telos` executable. Requires Logos's root package `Cpc`.
- `verification/` (package `TelosVerification`): the specification `Node.Equiv`
  and the correctness proofs. Requires `Telos`, Logos's `LogosVerification` and
  Mathlib.

## Building

```sh
lake build                              # rewriter
lake -d verification exe cache get      # Mathlib binaries (once)
lake -d verification build              # proofs (also builds part of Logos's proofs)
bash scripts/check-hygiene.sh           # no sorry/axiom; trusted code is listed
```

## Updating Logos

Logos is pinned to one commit in **both** `lakefile.toml` (`Cpc`) and
`verification/lakefile.toml` (`LogosVerification`). Change both `rev`s together,
then run `lake update Cpc` and `lake -d verification update`.

To develop against a local Logos checkout, temporarily replace the `git`/`rev`
lines with `path = "../logos"` (and `path = "../../logos/verification"`), and do
not commit that change.
