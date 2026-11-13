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

## Usage

```sh
lake build telos
.lake/build/bin/telos test/examples/bool.smt2            # rewritten terms
.lake/build/bin/telos --proof test/examples/bool.smt2    # ... each with a CPC proof
```

The input is an SMT-LIB script of `declare-const`, `declare-fun`, `declare-sort`
and `(simplify t)` commands, read by Logos's parser. For each `t`, telos prints
its rewrite, as cvc5 does. Only some theories are ported so far: Booleans, linear
and nonlinear arithmetic over `+`, `-`, `*`, `/` by constants, `to_real` and the
comparisons, and equality, UF and quantifiers as far as they are Boolean. Terms
with other operators are reported as unsupported, and rewriting of the supported
ones is incomplete.

With `--proof` (or `--proof-dir DIR`, one file per query), each result comes with
a CPC proof of `(= t result)`, as a refutation of `(not (= t result))`. telos
prints only proofs that Logos's checker accepts. Check them with
`ethos --include=.lake/packages/Cpc/install/defs/Cpc.cached.eo FILE`, or run
`python3 scripts/check-proofs.py --fuzz 500`.

See [`docs/design.md`](docs/design.md) for the architecture and roadmap, and
[`TRUSTED.md`](TRUSTED.md) for what the theorem relies on.

## Layout

Two Lake projects, so the rewriter builds without Mathlib:

- `.` (package `Telos`): `Node`, its translation to Logos terms, the rewriter,
  the SMT-LIB front end, proof output and the `telos` executable. Requires Logos's root package `Cpc`. `TelosTests/`
  holds tests checked at build time.
- `verification/` (package `TelosVerification`): the specification `Node.Equiv`
  and the correctness proofs. Requires `Telos`, Logos's `LogosVerification` and
  Mathlib.

## Building

```sh
lake build                              # rewriter
lake -d verification exe cache get      # Mathlib binaries (once)
lake -d verification build              # proofs (also builds part of Logos's proofs)
bash scripts/check-hygiene.sh           # no sorry/axiom; trusted code is listed
python3 scripts/gen-rules.py            # regenerate Telos/Rules/Generated.lean
lake build telos-fuzz && python3 scripts/fuzz.py --cvc5 PATH   # compare with cvc5
python3 scripts/check-proofs.py --fuzz 500                      # proofs, with Ethos
```

The rule table `Telos/Rules/Generated.lean` is generated from the CPC signature in
the pinned Logos checkout. After changing the Logos `rev`, regenerate it; CI
fails when it is out of date (`--check`).

## Updating Logos

Logos is pinned to one commit in **both** `lakefile.toml` (`Cpc`) and
`verification/lakefile.toml` (`LogosVerification`). Change both `rev`s together,
then run `lake update Cpc` and `lake -d verification update`.

To develop against a local Logos checkout, temporarily replace the `git`/`rev`
lines with `path = "../logos"` (and `path = "../../logos/verification"`), and do
not commit that change.
