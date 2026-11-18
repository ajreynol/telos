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

## The name

*Telos* is Greek for "end" or "goal". A verified SMT solver is the end goal of
the verification and Eunoia efforts this project builds on; the verified rewriter
is a step toward it.

## Usage

```sh
lake build telos
.lake/build/bin/telos test/examples/bool.smt2            # rewritten terms
.lake/build/bin/telos --proof test/examples/bool.smt2    # ... each with a CPC proof
.lake/build/bin/telos --post-asserts test/preprocess/basic.smt2   # preprocessed assertions
```

The input is an SMT-LIB script of `declare-const`, `declare-fun`, `declare-sort`
and `(simplify t)` commands, read by Logos's parser. For each `t`, telos prints
its rewrite, as cvc5 does. Only some theories are ported so far: Booleans,
arithmetic (`+`, `-`, `*`, `/`, `div`, `mod`, `abs`, `to_real`, `to_int`,
`is_int` and the comparisons), equality over uninterpreted sorts and
`distinct` (cvc5's UF rewriter), bit-vectors, arrays (`select`, `store`),
strings (partly), finite sets (the operators of cvc5's safe mode: no
`set.card` or relations), inductive datatypes (`declare-datatypes`, also
parametric) and tuples, and quantifiers as far as they are Boolean.
Terms
with other operators are reported as unsupported, and rewriting of the supported
ones is incomplete.

With `--proof` (or `--proof-dir DIR`, one file per query), each result comes with
a CPC proof of `(= t result)`, as a refutation of `(not (= t result))`, in
parentheses as cvc5's `get-proof` prints it. telos prints only proofs that
Logos's checker accepts. To check one with Ethos, drop the outer parentheses and
run `ethos --include=.lake/packages/Cpc/install/defs/Cpc.cached.eo FILE`, or run
`python3 scripts/check-proofs.py --fuzz 500`, which does both.

See [`docs/design.md`](docs/design.md) for the architecture and roadmap,
[`docs/theory-rewriters.md`](docs/theory-rewriters.md) for how to port another theory,
[`docs/solver-plan.md`](docs/solver-plan.md) for the original, broader plan for a
verified solver, and [`TRUSTED.md`](TRUSTED.md) for what the theorem relies on.

With `--post-asserts`, the input is a benchmark (declarations, `define-fun`s,
assertions and `check-sat`), and telos prints its assertions after
preprocessing, as cvc5 does with `-o post-asserts`, with the theorem
`Telos.preprocess_correct`: the conjunction of the output is equivalent to that
of the input. The preprocessor is at its second stage (`docs/preprocessor-plan.md`):
top-level conjunctions are split, the assertions rewritten, `ite`s and
Boolean terms inside terms purified, and `div`, `mod`, `/`, `to_int`, `is_int`
and `abs` eliminated, with skolem lemmas; `define-fun`s are macros. `python3 scripts/fuzz-pp.py --cvc5 PATH` compares it with cvc5.

## Layout

Two Lake projects, so the rewriter builds without Mathlib:

- `.` (package `Telos`), requiring Logos's root package `Cpc`, in layers, each
  a library that imports only the ones above it (`scripts/check-hygiene.sh`
  checks this):
  - `Telos/Core/` (`TelosCore`): `Node` and its translation to Logos terms
    (`Node/`), certified rewrites (`Certified.lean`, `Static.lean`,
    `PolyNorm.lean`), and CPC proof output (`Proof/`);
  - `Telos/Rewriter/` (`TelosRewriter`): the rewriter: the driver, the
    generated rule table (`Rules/`) and the theory rewriters (`Theory/`,
    `Strings/`);
  - `Telos/Frontend/` (`TelosFrontend`): SMT-LIB scripts (`Script.lean`) and
    `simplify` queries (`Simplify.lean`);
  - `Main.lean`: the `telos` executable. `TelosTests/` holds tests checked at
    build time.
- `verification/` (package `TelosVerification`): the specification `Node.Equiv`
  and the correctness proofs, in the same layers (`TelosProofs/Core/`,
  `TelosProofs/Rewriter/`). Requires `Telos`, Logos's `LogosVerification` and
  Mathlib.

The verified preprocessor (`docs/preprocessor-plan.md`) will be a further layer,
`Telos/Preprocess/`, between the rewriter and the front end.

## Building

```sh
lake build                              # rewriter
lake -d verification exe cache get      # Mathlib binaries (once)
lake -d verification build              # proofs, with the Logos theorems they use as a hypothesis (CI)
lake -d verification build TelosFull    # also Logos's proofs: the unconditional theorem
bash scripts/check-hygiene.sh           # no sorry/axiom; trusted code is listed
python3 scripts/gen-rules.py            # regenerate Telos/Rewriter/Rules/Generated.lean
python3 scripts/gen-term-order.py       # regenerate the generated part of TelosProofs/Core/TermOrder.lean
lake build telos-fuzz && python3 scripts/fuzz.py --cvc5 PATH   # compare with cvc5
python3 scripts/check-proofs.py --fuzz 500                      # proofs, with Ethos
python3 scripts/loc-summary.py                                  # lines: spec, rewriter, proofs
bash scripts/profile.sh                                         # where rewriting time goes
```

The rule table `Telos/Rewriter/Rules/Generated.lean` is generated from the CPC signature in
the pinned Logos checkout. After changing the Logos `rev`, regenerate it; CI
fails when it is out of date (`--check`).

## Updating Logos

Logos is pinned to one commit in **both** `lakefile.toml` (`Cpc`) and
`verification/lakefile.toml` (`LogosVerification`). Change both `rev`s together,
then run `lake update Cpc` and `lake -d verification update`.

To develop against a local Logos checkout, temporarily replace the `git`/`rev`
lines with `path = "../logos"` (and `path = "../../logos/verification"`), and do
not commit that change.

## How this repository is maintained

This repository is part of the **Eunoia ecosystem** and follows its
[shared repository policy](https://github.com/ajreynol/kanon/blob/main/docs/policy.md).
CI checks it against policy contract `1`.

The work is written by a human maintainer together with AI coding agents working
under the maintainer's direction; the maintainer reviews changes before they are
committed. That review does not re-check proofs by hand: correctness rests on
Lean's kernel and the trusted base listed in [`TRUSTED.md`](TRUSTED.md), and
agreement with cvc5's choice of rewrites is tested by differential fuzzing, not
proved.
