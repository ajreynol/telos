# telos

A **verified rewriter and preprocessor for SMT**, written in Lean 4. Both are
ports of [cvc5](https://github.com/cvc5/cvc5), each with a machine-checked proof
that it preserves meaning:

- the **rewriter**, cvc5's `Rewriter` and its theory rewriters: every rewrite is
  equivalent to its input;
- the **preprocessor**, cvc5's preprocessing passes (`ProcessAssertions`): the
  preprocessed assertions are equivalent to the input ones.

```lean
theorem Telos.rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t)
theorem Telos.preprocess_correct (as : List Node) (h : (Preprocess.inputNode as).WellTyped) :
    (Preprocess.inputNode as).Equiv (Preprocess.preprocessCert as).1
```

`inputNode as` is the conjunction of the input assertions, and
`preprocessCert as` the conjunction of the preprocessed ones, as certified
rewrites of it.

### How it is verified

**CPC is the basis.** The semantics come from
[Logos](https://github.com/ajreynol/logos), the verified CPC proof checker, so
"equivalent" means what a CPC proof of `(= t s)` would establish: the same value
in every model. The rules of CPC (RARE rewrites, theory rewrites, preprocessing
rules such as `skolem_intro` or `arith_reduction`) are the vocabulary in which
each step is justified, and Logos proves each of them sound.

**Proof checking is the baseline algorithm, not the only one.** The simplest
way to justify a step is to build its CPC proof and run Logos's checker on it;
one theorem about checked steps then covers every rewrite and every pass, with
no proof of its own. telos does this where it is cheap: a rewrite rule applied
to one term. But checking re-does, in Logos's tree-recursive programs, work that
telos has already done, and on large or highly shared terms it is far too slow.
So the rewriter and the preprocessor use faster methods wherever it matters,
and each such method comes with a Lean proof, done once, that it is equivalent to
what a checked proof would establish:

- *static* steps (`Telos/Core/Static.lean`): a cheap side condition, with a
  theorem that the checker would accept the step (arithmetic normalization);
- *semantic* steps (`Telos/Core/Semantic.lean`): a side condition decided on
  telos's own terms, with a theorem that it implies equivalence (reorganizing the
  pipeline's conjunction, with substitution and Boolean propagation to follow).

Terms are always shared as DAGs: nodes carry their hash, compare in constant
time when they are the same in memory, and the fast methods never traverse
shared terms as trees.

**Proof production is for external auditing.** Printing CPC proofs
(`--proof`, checked by Ethos) lets anyone audit a result without trusting telos
or Lean. It is not the mechanism of verification, and it costs nothing when no
proof is asked for: a result is computed the same way either way (proven:
`simplify_output`, `postAssertsFull_output`), and the proof is built afterwards
from its certificate. The rewriter and the preprocessor both print proofs. The
steps justified by a Lean theorem (static, semantic and substitution steps)
are turned into CPC proofs from the data their side conditions checked
(`Telos/Preprocess/ProofExt.lean`), and large proofs are printed with shared
terms defined once (`Telos/Core/Proof/Shared.lean`).

Which rule to apply, and when, follows cvc5's C++ and is tested against cvc5 by
differential fuzzing; that part needs no proof, since every step is justified
either way.

## The name

*Telos* is Greek for "end" or "goal". A verified SMT solver is the end goal of
the verification and Eunoia efforts this project builds on; the verified rewriter
and preprocessor are steps toward it.

## Usage

```sh
lake build telos
.lake/build/bin/telos test/examples/bool.smt2                      # rewritten terms
.lake/build/bin/telos --proof test/examples/bool.smt2              # ... each with a CPC proof
.lake/build/bin/telos --post-asserts test/preprocess/basic.smt2    # preprocessed assertions
.lake/build/bin/telos --post-asserts --proof test/preprocess/basic.smt2   # ... with a CPC proof
.lake/build/bin/telos --theory-events test/solve/uf-literals.smt2  # theory-engine events (in progress)
.lake/build/bin/telos --theory-events test/solve/sat-bool.smt2     # ... with the SAT solver
```

### The rewriter

The input is an SMT-LIB script of `declare-const`, `declare-fun`, `declare-sort`
and `(simplify t)` commands, read by Logos's parser. For each `t`, telos prints
its rewrite, as cvc5 does. Only some theories are ported so far: Booleans,
arithmetic (`+`, `-`, `*`, `/`, `div`, `mod`, `abs`, `to_real`, `to_int`,
`is_int` and the comparisons), equality over uninterpreted sorts and
`distinct` (cvc5's UF rewriter), bit-vectors, arrays (`select`, `store`),
strings (partly), finite sets (the operators of cvc5's safe mode: no
`set.card` or relations), inductive datatypes (`declare-datatypes`, also
parametric) and tuples, and quantifiers as far as they are Boolean. Terms
with other operators are reported as unsupported, and rewriting of the supported
ones is incomplete.

With `--proof` (or `--proof-dir DIR`, one file per query), each result comes with
a CPC proof of `(= t result)`, for external auditing (see *How it is
verified*), as a refutation of `(not (= t result))`, in parentheses as cvc5's
`get-proof` prints it. telos prints only proofs that Logos's checker accepts. To check one with Ethos, drop the outer parentheses and
run `ethos --include=.lake/packages/Cpc/install/defs/Cpc.cached.eo FILE`, or run
`python3 scripts/check-proofs.py --fuzz 500`, which does both.

### The preprocessor

With `--post-asserts`, the input is a benchmark (declarations, `define-fun`s,
assertions and `check-sat`), and telos prints its assertions after
preprocessing, as cvc5 does with `-o post-asserts`. The output is equivalent to
the input (`Telos.preprocess_correct`), so it is satisfiable exactly when the
input is, in the same models. Ported so far (`docs/preprocessor-plan.md`):

- the assertion pipeline: top-level conjunctions split, conflicts detected;
- `rewrite`: each assertion rewritten by the verified rewriter;
- `non-clausal-simp`: literals learned by Boolean propagation, solved into
  substitutions `x := t` (printed as `define-fun`s, as cvc5 prints its
  top-level substitutions) or used as constant propagations, and applied to the
  assertions (`--simplification=none` turns it off);
- `static-learning` (UF's diamonds, arithmetic's `ite` lemmas) and `repeat-simp`;
- `static-rewrite`, in part: arithmetic, datatype, bit-vector and string
  equalities, `distinct`;
- `theory-preprocess`: non-Boolean `ite`s and Boolean terms inside terms
  replaced by purification skolems, and the theories' `ppRewrite`: `div`,
  `mod`, `/`, `to_int`, `is_int` and `abs` eliminated (cvc5's `OperatorElim`),
  datatype and tuple updaters expanded, the bit-vector overflow predicates eliminated,
  and `str.from_code` purified, with their skolem lemmas. Skolems are printed as cvc5 prints them
  (`@purify_1`, `@int_div_by_zero_2`).

`define-fun`s are macros. cvc5's `quantifiers-preprocess` pass does nothing
with its defaults and proofs (its prenexing is the rewriter's, ported there). The theorem relates the input to the preprocessed assertions together
with the definitions of the solved variables. With `--proof` (or `--proof-dir
DIR`), the output is followed by a CPC proof that the conjunction of the input
assertions equals that of the output and the definitions (skolems as their CPC
terms, `(@purify t)` for `@purify_k`); telos does not check it unless
`--check-proof` is given (by Logos, slow on large proofs); Ethos checks it.
`python3 scripts/fuzz-pp.py --cvc5 PATH`
compares the output with cvc5's, with the passes not yet ported switched off.

### The theory engine (in progress)

With `--theory-events`, the input is a benchmark whose preprocessed assertions
are a conjunction of literals. telos asserts them one at a time to its port of
cvc5's theory engine (`Telos/Solver/`), and prints the events at the interface
of the theory solvers, as cvc5 prints them with `-o theory-events`, then the
answer. That cvc5 output needs the patch `cvc5-theory-events.patch`.

So far the engine and UF are ported: cvc5's equality engine, used as the central
one, and UF. They cover logics in which UF is the only theory (QF_UF). In other
logics the theories' checks do nothing, and the answer is `unknown` as soon as
a theory gets a literal.

An `unsat` answer is certified. Its conflict is explained by a verified
explanation (`Telos/Solver/Explain.lean`), which computes the equality engine's
explanation as cvc5 does, with a theorem that its reasons imply the conflict.
Where it does not apply, it is certified by an equality proof instead
(`Telos/Solver/EqProof.lean`), whose datatypes reasoning is by CPC rule
instances that Logos's checker accepts. The answer is then correct: the input
assertions are unsatisfiable (`Telos.solve_unsat_correct`).
With `--proof` (or `--proof-dir DIR`), the CPC refutation follows, which Ethos
checks. A `sat` answer is certified too: telos builds a model from the
equality engine's classes of the relevant terms (`Telos/Solver/Model.lean`)
and evaluates the input assertions in it, answering `unknown` if one is not
true. The answer is then correct: the assertions are true in a well-formed
model (`Telos.solve_sat_correct`).
`scripts/fuzz-solve.py --cvc5 PATH` compares the events with cvc5's: with
`--cvc5-pp --ee`, on cvc5's own preprocessed assertions and with the equality
engine's notifications.

With `--replay TRACE`, telos gives its theories the inputs of a trace of cvc5's
(on cvc5's preprocessed benchmark), including the SAT solver's decisions and
backtracking, and prints its events. So the theories are tested on inputs with
SAT structure without a SAT solver (`scripts/fuzz-solve.py --replay`,
`test/replay/`). See
[`docs/theory-engine-plan.md`](docs/theory-engine-plan.md).

See [`docs/design.md`](docs/design.md) for the architecture and roadmap,
[`docs/theory-rewriters.md`](docs/theory-rewriters.md) for how to port another theory,
[`docs/preprocessor-plan.md`](docs/preprocessor-plan.md) for the preprocessor,
[`docs/solver-plan.md`](docs/solver-plan.md) for the original, broader plan for a
verified solver, and [`TRUSTED.md`](TRUSTED.md) for what the theorems rely on.

## Layout

Two Lake projects, so the rewriter and preprocessor build without Mathlib:

- `.` (package `Telos`), requiring Logos's root package `Cpc`, in layers, each
  a library that imports only the ones above it (`scripts/check-hygiene.sh`
  checks this):
  - `Telos/Core/` (`TelosCore`): `Node` (with skolems, `SkolemId`) and its
    translation to Logos terms (`Node/`), certified rewrites (`Certified.lean`:
    checked CPC steps, static steps `Static.lean`, `PolyNorm.lean`, and
    semantic steps `Semantic.lean`), and CPC proof output (`Proof/`);
  - `Telos/Rewriter/` (`TelosRewriter`): the rewriter: the driver, the
    generated rule table (`Rules/`) and the theory rewriters (`Theory/`,
    `Strings/`);
  - `Telos/Preprocess/` (`TelosPreprocess`): the preprocessor: the assertion
    pipeline (`Pipeline.lean`), the passes (`Passes/`), the theories'
    preprocessing (`Theory/`), and the certified steps that introduce skolems
    and reorganize conjunctions;
  - `Telos/Solver/` (`TelosSolver`): the theory engine: its events
    (`Event.lean`), the equality engine (`EqualityEngine.lean`), the theories
    (`Theory/`), the engine (`Engine.lean`), and the SAT side: the CNF stream
    (`Cnf.lean`), the prop engine and theory proxy (`Prop.lean`), and the SAT
    solver, a port of cvc5's MiniSat, which knows no terms (`Sat/`);
  - `Telos/Frontend/` (`TelosFrontend`): SMT-LIB scripts (`Script.lean`),
    `simplify` queries (`Simplify.lean`), `-o post-asserts`
    (`PostAsserts.lean`) and `--theory-events` (`Solve.lean`);
  - `Main.lean`: the `telos` executable. `TelosTests/` holds tests checked at
    build time.
- `verification/` (package `TelosVerification`): the specification `Node.Equiv`
  and the correctness proofs, in the same layers (`TelosProofs/Core/`,
  `TelosProofs/Rewriter/`, `TelosProofs/Preprocess/`). Requires `Telos`,
  Logos's `LogosVerification` and Mathlib.

## Building

```sh
lake build                              # rewriter and preprocessor
lake -d verification exe cache get      # Mathlib binaries (once)
lake -d verification build              # proofs, with the Logos theorems they use as a hypothesis (CI)
lake -d verification build TelosFull    # also Logos's proofs: the unconditional theorem
bash scripts/check-hygiene.sh           # no sorry/axiom; trusted code is listed
python3 scripts/gen-rules.py            # regenerate Telos/Rewriter/Rules/Generated.lean
python3 scripts/gen-term-order.py       # regenerate the generated part of TelosProofs/Core/TermOrder.lean
lake build telos-fuzz && python3 scripts/fuzz.py --cvc5 PATH   # compare the rewriter with cvc5
python3 scripts/fuzz-pp.py --cvc5 PATH [--proofs]               # compare the preprocessor with cvc5 (and check its proofs)
python3 scripts/fuzz-lemmas.py --cvc5 PATH [--solver PATH]       # compare the rewriter with cvc5 on its solver's lemmas (-t im)
python3 scripts/check-proofs.py --fuzz 500                      # proofs, with Ethos
python3 scripts/loc-summary.py                                  # lines: spec, core, rewriter, preprocessor, proofs
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
agreement with cvc5's choice of rewrites and preprocessing steps is tested by
differential fuzzing, not proved.
