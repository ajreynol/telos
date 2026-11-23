# telos

A **verified SMT solver in progress**, written in Lean 4: a port of
[cvc5](https://github.com/cvc5/cvc5) (its rewriter, its preprocessing passes,
and its theory engine with its SAT solver) in which every answer is
machine-checked to be correct. Four theorems state what telos guarantees:

- **`unsat` is correct**: if telos answers `unsat`, the input assertions have
  no model (`Telos.solve_unsat_correct`);
- **`sat` is correct**: if telos answers `sat`, the input assertions have a
  model (`Telos.solve_sat_correct`);
- **rewriting preserves meaning** (`Telos.rewrite_correct`);
- **preprocessing preserves meaning** (`Telos.preprocess_correct`).

The meaning of a formula is that of [Logos](https://github.com/ajreynol/logos),
the verified checker of cvc5's proof format CPC; the proofs are checked by
Lean's kernel. telos does not claim to be complete: it may answer `unknown`
(and says why, see *When telos answers `unknown`*), but its `sat` and `unsat`
are never wrong. Which inference to make, and when, follows cvc5's code and is
compared with cvc5 by differential testing; that part needs no proof.

## What is proved

The theorems are in `verification/TelosFull/Main.lean`
(`lake -d verification build TelosFull`); the default verification build,
which CI runs, proves them with the Logos theorems they use as a hypothesis
(`[LogosFacts]`, `verification/TelosProofs/Core/LogosFacts.lean`), and
`TelosFull` discharges it from Logos's proofs.

### The solver

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
`false` in every well-formed model. `sat`: it evaluates to `true` in one.
This is the semantics in which Logos proves its checker sound, so the answer
means what a CPC refutation of the same term, checked by Logos, would
establish.

**How the proofs compose with Logos's.** Logos's correctness theorem is the
soundness of its checker (`proven_from_empty_valid`): a CPC proof that the
checker accepts proves a formula that is true in every well-formed model.
telos uses it for every step it justifies by a CPC rule (in the rewriter, the
preprocessor and the theories' certificates), through the class `LogosFacts`
(`verification/TelosProofs/Core/LogosFacts.lean`), which restates the Logos
theorems telos uses: the checker's soundness, congruence, and facts about the
evaluation (a Boolean term evaluates to a Boolean, the operations on maps and
sets). The default verification build proves telos's theorems from
`LogosFacts`, without Logos's proofs (`Telos.Frontend.solve_unsat` and
`solve_sat`); `TelosFull` proves `LogosFacts` from Logos's theorems, each field
from the theorem it restates, and so the unconditional theorems above. telos's
own proofs cover the rest: the certificate checkers (unit propagation, Farkas
combinations, equality proofs), the verified explanation, the model evaluator,
and the step from "not true in any model" to Logos's "false in every model".

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

Both are about the input assertions as read, not about the preprocessed ones.
The `sat` theorem does not depend on preprocessing at all, since it checks the
model against the input. The `unsat` theorem uses that preprocessing preserves
models (a skolem is the term it purifies, in Logos's semantics).

**How an `unsat` is certified.** The search itself (the SAT solver, cvc5's
MiniSat port, and the theory solvers) is not trusted. An `unsat` stands only if
a certificate of the refutation checks, and the checkers are proved sound:
- with the SAT solver (`Telos/Solver/SatProof.lean`,
  `SatProof.Cert.check_sound`), the clauses the solver used, each with its
  justification:
  - a clause of the CNF of an input formula, or a definition of a
    connective's literal (Tseitin);
  - a theory conflict, certified by an equality proof (`EqProof.check_sound`)
    whose theory steps are CPC rules run through Logos's checker;
  - an arithmetic conflict, certified by a Farkas combination
    (`Telos/Solver/LinCert.lean`);
  - a theory lemma, with a proof that it is valid, by CPC rules (the
    datatypes, sets, strings, quantifiers and nonlinear arithmetic lemmas).
    A lemma whose proof telos lacks (some of the strings lemmas, so far) is
    left out of the certificate, so a refutation that needs it is `unknown`,
    never an unchecked `unsat`.

  The clauses the solver learned, and finally the empty clause, are rechecked
  by unit propagation (reverse unit propagation). Every check is recomputed
  from the clauses, not taken from the solver;
- for a conjunction of literals without the SAT solver, the equality engine's
  explanation of the conflict, recomputed by a proved explanation
  (`EE.explainLitV_sound`), or an equality proof.

**How a `sat` is certified.** telos builds a model from the equality engine
and the theories' values (`Telos/Solver/Model.lean`), and evaluates the input
assertions in it. The model builder is not trusted; the evaluator is proved to
compute Logos's evaluation, in a well-formed Logos model built from the model
(`Solver.satisfies_sound`). So a `sat` holds whatever the solver did.

**What this means in practice.** A bug in the search, the theory solvers, the
model builder or the certificate builders cannot make telos answer wrongly. It
can make telos answer `unknown`, which it then explains: a certificate that
did not check is reported as such (`cert-unsat/…`, `cert-sat/…`), not hidden.

### The rewriter and the preprocessor

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

### What the theorems rest on

- **The specification** (`TRUSTED.md`): Logos's semantics of CPC (its terms,
  the SMT translation, the type checker and the model semantics, at the pinned
  commit), telos's translation of its nodes to Logos terms
  (`Telos/Core/Node/ToEo.lean`), and the definitions of `Node.Equiv` and
  `Script.satisfiability`. A mistake
  there makes the theorems true of the wrong thing, so they are reviewed as
  specifications.
- **Axioms**: Lean's `propext`, `Classical.choice` and `Quot.sound`, and the
  axioms that `native_decide` introduces in Logos's proofs (which trust the Lean
  compiler). No `sorry`, no declared axiom; `#assert_axioms` fails the build
  otherwise (`verification/TelosProofs/Axioms.lean`).
- **Lean**: the kernel, the compiler and the runtime.

### What they do not cover

- **Parsing and printing.** The theorems are about the parsed script.
  Logos's SMT-LIB parser and telos's front end are not verified, nor is the
  printing of the answer; a parsing bug could make telos solve a different
  problem than the one written.
- **Completeness.** Nothing says telos answers `sat` or `unsat`; `unknown` is
  always allowed.
- **Agreement with cvc5.** That telos makes cvc5's inferences, in cvc5's
  order, is tested (by differential fuzzing on cvc5's traces), not proved.
- **Proofs printed for others.** The CPC proofs telos prints (`--proof`) are
  for external auditing, by Ethos or Logos; they are not what the theorems
  rely on.

## How it is verified

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

So far the engine, UF, datatypes, cvc5's MiniSat with its decision engine (the
justification heuristic) and linear arithmetic are ported: cvc5's equality engine, used as the central one, UF and datatypes
over it, and linear arithmetic (`Telos/Solver/Theory/Arith/`: the simplex,
branch and bound and the Diophantine solver; not yet with other theories), with
cvc5's nonlinear extension in part (`Telos/Solver/Theory/Arith/Nl/`: model-based
refinement by sign, magnitude, bound, tangent plane, factoring and flattening
lemmas, each certified by CPC rules, `Telos/Solver/NlLemma.lean`). In
other logics the theories' checks do nothing, and the answer is `unknown` as
soon as a theory gets a literal. Bit-vectors and arrays that a logic enables
(`ALL`, say) but the input does not use are inert, as in cvc5: their checks do
nothing, and the other theories are solved.

An `unsat` answer is certified. With SAT structure, the SAT solver's
refutation comes with a clausal certificate (`Telos/Solver/SatProof.lean`):
its clauses justified by the CNF translation, the definitions of connectives,
certificates of theory conflicts and of theory lemmas (for arithmetic,
Farkas combinations, `Telos/Solver/LinCert.lean`), its learned clauses by
unit propagation;
the checker is proved sound. For a conjunction of literals, its conflict is
explained by a verified
explanation (`Telos/Solver/Explain.lean`), which computes the equality engine's
explanation as cvc5 does, with a theorem that its reasons imply the conflict.
Where it does not apply, it is certified by an equality proof instead
(`Telos/Solver/EqProof.lean`), whose datatypes reasoning is by CPC rule
instances that Logos's checker accepts. The answer is then correct: the input
assertions are unsatisfiable (`Telos.solve_unsat_correct`).
With `--proof` (or `--proof-dir DIR`), the CPC refutation follows, which Ethos
checks. A `sat` answer is certified too: telos builds a model, datatype
values included, from the equality engine's classes of the relevant terms
(`Telos/Solver/Model.lean`)
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

### When telos answers `unknown`

Every `unknown` of `telos --solve` says why, with a code (`Telos/Solver/Unknown.lean`):
- `intentional`: a theory declared the model incomplete with one of cvc5's
  own `IncompleteId`s, where cvc5 does (nonlinear arithmetic's `ARITH_NL`,
  the quantifiers engine's);
- `not-ported`: a part of cvc5 that telos does not port (a theory or a stage of
  one, an operator the engine treats as uninterpreted), on which cvc5 would
  decide;
- `cert-sat/model-false`, `cert-sat/not-evaluated`: a `sat` whose model makes
  the input false (a bug), or that the evaluator cannot evaluate (a gap);
- `cert-unsat/missing-proof` (with the theories and inferences of the lemmas
  without a certificate that the refutation needs), `cert-unsat/bad-justification`,
  `cert-unsat/broken` (bugs);
- `unsupported`, `internal`.

The goal is that only `intentional` remains on the inputs telos supports.

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
python3 scripts/loc-summary.py                                  # TCB/spec, solver code, verification proofs
python3 scripts/logos-runtime.py                                # build + inventory runtime references to Logos
python3 scripts/logos-runtime.py --symbols --files               # targets/forms and caller files
python3 scripts/logos-runtime.py --sites --check-no-spec         # dependency paths; fails while solver calls spec
bash scripts/profile.sh                                         # where rewriting time goes
```

The LOC report separates (1) TCB/spec, including the trusted profiling module,
(2) solver code, including the rewriter, preprocessor, checkers, front end and
proof output, and (3) verification proofs. Standalone theorems/lemmas in solver
files count as proofs; inline proof terms and termination proofs stay with
their definitions. Specification files count whole. Tests, fuzzing and audit
tools are reported separately, as is the pinned Logos specification. `--files`
shows each file's contribution. The shared classification is in
`scripts/lean_inventory.py`.

The runtime inventory reads the pinned Lean compiler's saved base LCNF after
proof erasure and early simplification/specialization. It counts static
application/reference sites, including implicit instances, function arguments
and generated helpers. These are compiler-level counts, not source-token or
execution counts: inlining can remove calls and specialization can duplicate
them. Unused compiled definitions are included; theorem bodies, types and
constructor allocations are excluded. `--scope all` includes TCB/spec callers;
the default covers solver callers. `--json` exports sites and dependency paths.
Locations identify the containing declaration (line 0 means unavailable).

`--check-no-spec` exits 1 when solver references reach functions in Telos's
TCB/spec files or the Logos specification import closure, directly or through
Logos helpers. Shared datatype constructors are allowed, but functions in
those files (including equality/hash helpers and profiling) are reported.
The check currently fails: this is an inventory for removing dependencies,
not a completed separation. It follows named references; it does not resolve
dynamic calls through variables or certify source-level independence. The
script builds all production Lean modules first, without verification/Mathlib;
`--no-build` explicitly assumes the existing artifacts are current. Run
`python3 scripts/test-inventory.py` for the report regression checks.

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
