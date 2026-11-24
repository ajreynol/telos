# telos

A **verified SMT solver in progress**, written in Lean 4: a port of
[cvc5](https://github.com/cvc5/cvc5)'s rewriter, preprocessing passes and
theory engine (with its SAT solver) in which every answer is machine-checked.
Four theorems, checked by Lean's kernel, state what telos guarantees:

- **`unsat` is correct**: the input assertions have no model (`Telos.solve_unsat_correct`);
- **`sat` is correct**: the input assertions have a model (`Telos.solve_sat_correct`);
- **rewriting preserves meaning** (`Telos.rewrite_correct`);
- **preprocessing preserves meaning** (`Telos.preprocess_correct`).

Meaning is that of [Logos](https://github.com/ajreynol/logos), the verified
checker of cvc5's proof format CPC. The search (the SAT solver, the theory
solvers, the model builder) is not trusted: an `unsat` stands only if a
certificate of the refutation passes a checker proved sound, and a `sat` only
if the input assertions evaluate to true in the model, by an evaluator proved
to compute Logos's evaluation. A bug in the search can make telos answer
`unknown`, never wrongly. telos does not claim to be complete, and every
`unknown` says why (see *When telos answers `unknown`*). Which inference to
make, and when, follows cvc5's code and is tested against cvc5 by differential
fuzzing; that part needs no proof.

The theorems rely on Logos's semantics, telos's translation of its terms into
Logos's, and Lean ([`TRUSTED.md`](TRUSTED.md)); parsing and printing are not
verified. See [`verification/README.md`](verification/README.md) for the
precise statements, how answers are certified, and what the theorems do and
do not cover.

## The name

*Telos* is Greek for "end" or "goal". A verified SMT solver is the end goal of
the verification and Eunoia efforts this project builds on.

## Usage

```sh
lake build telos
.lake/build/bin/telos test/solve/models.smt2                       # runs the script, as cvc5 does: sat, (get-model), (get-value …)
.lake/build/bin/telos --dump-models test/solve/dump-models.smt2    # ... with the model after each sat
.lake/build/bin/telos --dump-proofs test/solve/proof-lra.smt2      # ... with the full CPC proof after each unsat
.lake/build/bin/telos test/rewriter/bool.smt2                      # rewritten terms
.lake/build/bin/telos --proof test/rewriter/bool.smt2              # ... each with a CPC proof
.lake/build/bin/telos --post-asserts test/preprocess/basic.smt2    # preprocessed assertions
.lake/build/bin/telos --post-asserts --proof test/preprocess/basic.smt2   # ... with a CPC proof
.lake/build/bin/telos --solve test/theory-events/sat-bool.smt2             # sat / unsat / unknown
.lake/build/bin/telos --theory-events test/theory-events/uf-literals.smt2  # theory-engine events, as cvc5 prints them
```

**As an SMT solver**, `telos FILE` runs the script's commands in order and
prints what cvc5 prints: the answer of each `check-sat`, models (`get-model`,
`get-value`, with `--produce-models` or `(set-option :produce-models true)`),
proofs (`get-proof`, with `--produce-proofs`), `echo`, `get-info
:reason-unknown`; errors as `(error "…")`. `--dump-models` and `--dump-proofs`
print the model after each `sat` and the proof after each `unsat`, as cvc5's
options do. Why an answer is `unknown` is printed on standard error. A **full
proof** of `unsat` is a CPC refutation from the input assertions: it connects
the proof of preprocessing, the CNF translation (CPC's `cnf_*` and elimination
rules), the theory conflicts and lemmas (the equality engine's certificates,
and linear arithmetic's Farkas combinations, splits and cuts), and resolution
(`chain_m_resolution`, from the SAT certificate's unit propagation)
([`Telos/Frontend/FullProof.lean`](Telos/Frontend/FullProof.lean)).
`python3 scripts/check-full-proofs.py FILE…` checks them with Ethos.

`--proof` (or `--proof-dir DIR`, one file per query) prints CPC proofs for
external auditing; the theorems do not rely on them. To check one with Ethos,
drop the outer parentheses and run
`ethos --include=.lake/packages/Cpc/install/defs/Cpc.cached.eo FILE`, or run
`python3 scripts/check-proofs.py --fuzz 500`.

**The rewriter.** For each `(simplify t)` in an SMT-LIB script, telos prints
the rewrite of `t`, as cvc5 does. Ported so far, in part: Booleans,
arithmetic, equality and `distinct` over uninterpreted sorts, bit-vectors,
arrays, strings, finite sets (cvc5's safe mode: no `set.card` or relations),
inductive datatypes and tuples, and quantifiers as far as they are Boolean.
Other operators are reported as unsupported. See
[`docs/theory-rewriters.md`](docs/theory-rewriters.md) to port another theory.

**The preprocessor.** With `--post-asserts`, telos prints a benchmark's
assertions after preprocessing, as cvc5 does with `-o post-asserts`; the output
is equivalent to the input. Ported so far: the assertion pipeline, `rewrite`,
`non-clausal-simp` (solved variables printed as `define-fun`s),
`static-learning`, `repeat-simp`, `static-rewrite` in part, and
`theory-preprocess` (purification skolems, cvc5's `OperatorElim`, datatype
updaters, bit-vector overflow predicates). See
[`docs/preprocessor-plan.md`](docs/preprocessor-plan.md).

**The theory engine (in progress).** `--solve` runs preprocessing, then a port
of cvc5's theory engine (`Telos/Solver/`) with its MiniSat and justification
heuristic. Ported so far: the equality engine, UF, datatypes, linear arithmetic
(simplex, branch and bound, the Diophantine solver; not yet with other
theories) and, in part, cvc5's nonlinear extension, sets, strings and
quantifiers. In other logics the answer is `unknown` as soon as a
theory gets a literal; bit-vectors and arrays a logic enables but the input does
not use are inert, as in cvc5. `--theory-events` prints the events at the
theory solvers' interface, as cvc5 does with `-o theory-events` (with the patch
`cvc5-theory-events.patch`), and `--replay TRACE` feeds the theories a cvc5
trace, SAT decisions included. See
[`docs/theory-engine-plan.md`](docs/theory-engine-plan.md).

### When telos answers `unknown`

Every `unknown` of `telos --solve` says why, with a code (`Telos/Solver/Unknown.lean`):

- `intentional`: a theory declared the model incomplete where cvc5 does
  (cvc5's `IncompleteId`s, such as nonlinear arithmetic's `ARITH_NL`);
- `not-ported`: a part of cvc5 that telos does not port, on which cvc5 would
  decide;
- `cert-sat/model-false` (a bug), `cert-sat/not-evaluated` (a gap): the model
  does not make the input true;
- `cert-unsat/missing-proof` (a lemma the refutation needs has no certificate
  yet), `cert-unsat/bad-justification`, `cert-unsat/broken` (bugs);
- `unsupported`, `internal`.

The goal is that only `intentional` remains on the inputs telos supports.

## Layout

Two Lake projects, so the solver builds without Mathlib:

- `.` (package `Telos`, requiring Logos's `Cpc`), in layers that each import
  only the ones above (`scripts/check-hygiene.sh` checks this):
  `Telos/Core/` (terms, their translation to Logos, certified steps, proof
  output), `Telos/Rewriter/`, `Telos/Preprocess/`, `Telos/Solver/` (the theory
  engine, the theories, the CNF stream and the SAT solver), `Telos/Frontend/`,
  and `Main.lean`, the `telos` executable. `TelosTests/` holds tests checked at
  build time.
- `test/`: inputs and expected outputs, by part: `rewriter/`, `preprocess/`,
  `theory-events/`, `replay/`, `solve/` ([`test/README.md`](test/README.md)).
- `verification/` (package `TelosVerification`): the specification and the
  correctness proofs, in the same layers. Requires `Telos`, Logos's
  `LogosVerification` and Mathlib.

Further documentation: [`docs/design.md`](docs/design.md) (architecture and
roadmap), [`docs/solver-plan.md`](docs/solver-plan.md) (the original, broader
plan for a verified solver), and the pages linked above.

## Building

```sh
lake build                              # the solver
lake -d verification exe cache get      # Mathlib binaries (once)
lake -d verification build              # proofs, with the Logos theorems they use as a hypothesis (CI)
lake -d verification build TelosFull    # also Logos's proofs: the unconditional theorems
bash scripts/check-hygiene.sh           # no sorry/axiom; trusted code is listed
python3 scripts/gen-rules.py            # regenerate Telos/Rewriter/Rules/Generated.lean
python3 scripts/gen-term-order.py       # regenerate the generated part of TelosProofs/Core/TermOrder.lean
lake build telos-fuzz && python3 scripts/fuzz.py --cvc5 PATH   # compare the rewriter with cvc5
python3 scripts/fuzz-pp.py --cvc5 PATH [--proofs]               # compare the preprocessor with cvc5 (and check its proofs)
python3 scripts/fuzz-solve.py --cvc5 PATH                       # compare the theory events with cvc5
python3 scripts/fuzz-lemmas.py --cvc5 PATH [--solver PATH]       # compare the rewriter with cvc5 on its solver's lemmas (-t im)
python3 scripts/check-proofs.py --fuzz 500                      # proofs, with Ethos
python3 scripts/check-full-proofs.py test/solve/*.smt2 test/theory-events/*.smt2   # full proofs of unsat, with Ethos
python3 scripts/testbed.py run                                  # how many cvc5 regressions telos solves (test/testbed)
python3 scripts/loc-summary.py                                  # TCB/spec, solver code, verification proofs
python3 scripts/logos-runtime.py                                # runtime references to Logos
bash scripts/profile.sh                                         # where rewriting time goes
```

The two inventory scripts describe their counts and options in their
docstrings (`--help`). The rule table `Telos/Rewriter/Rules/Generated.lean` is
generated from the CPC signature in the pinned Logos checkout; regenerate it
after changing the Logos `rev` (CI fails when it is out of date).

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
agreement with cvc5's choice of rewrites and preprocessing steps is tested by
differential fuzzing, not proved.
