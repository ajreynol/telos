> **Note (2026-11-12):** this is the original, broader plan for a verified SMT
> *solver*. The project is now scoped to a verified *rewriter*; see
> [`design.md`](design.md). This plan is kept for the longer-term direction (proof
> production, the CDCL core) and for its notes on Logos.
>
> **Update (2026-11-20):** the solver work now happens inside telos; see
> [`theory-engine-plan.md`](theory-engine-plan.md).

# Setting up a statically verified, proof-producing SMT solver

This document briefs an agent on setting up a new SMT solver in a **new, separate
repository**. The solver is written in Lean 4 and depends on Logos
(this repository) as a library. Read the whole document before creating files.

## 1. Goal

Build an SMT solver with three properties:

1. **Memory safety.** It is written in Lean 4, with no `unsafe`, `@[extern]` or
   `implemented_by` in the solver except where listed and justified in
   `TRUSTED.md` (see §6).
2. **Static soundness.** There is a Lean theorem, checked when the solver is
   compiled, saying that an `unsat` answer means the input is unsatisfiable and a
   `sat` answer means it is satisfiable. No proof checker runs at runtime to get
   this guarantee.
3. **Proof production.** In proof mode the solver emits a CPC proof (the calculus
   cvc5 emits, checked by Ethos and Logos). A Lean theorem says the emitted proof
   is **always** accepted by the Logos checker.

Non-goals for now: termination, completeness, and matching cvc5's performance.
Answering `unknown` is always allowed.

## 2. The central idea: proofs about data, not proof objects

Search heuristics are unconstrained, unverified code. Only *derived facts*
(clauses, lemmas, rewrites) carry evidence, and the evidence is about CPC: "a
valid CPC derivation of this fact from the input assumptions exists".

```lean
inductive Mode | noProof | proof

structure Derived (m : Mode) (F : Assumptions) where
  c   : Term                 -- the derived fact (a Logos `Eo.Term`)
  pf  : m.ProofData          -- noProof: Unit; proof: an id of a step in the proof log
  ok  : m.Valid F pf c       -- noProof: Provable F c  (a Prop, erased at compile time)
                             -- proof:   log entry `pf` checks with conclusion c
```

- Each CPC rule gets **one combinator, written once and generic over `Mode`**.
  It takes premises of type `Derived m F`, argument terms, and any runtime-checked
  side conditions, and returns `Option (Derived m F)`, or `Derived m F` when the side
  condition is proven statically.
- **No-proof mode:** `ok` is erased, so nothing is built at runtime.
- **Proof mode:** the combinator also appends one `step` to a linear proof log and
  stores its id. The log has the shape of Logos's `CCmdList` (`assume_push`, `step`,
  `step_pop`), so sharing comes for free.
- **Side conditions:** if the rule's Eunoia program has a side condition the engine
  cannot prove statically, check it at runtime
  (`if h : cond then some (mk … h) else none`). The guarantee stays static: an
  `unsat` answer is always correct.
- **Decisions and assumptions** use CPC scoping (`assume_push`/`step_pop`, the
  `scope` rule). Facts derived under assumptions are tracked as such until the
  scope is closed.
- **SAT answers** are checked at runtime by a model evaluator verified against
  Logos's `SmtModel` semantics. Answer `unknown` whenever the model cannot be
  checked: quantifiers, unsupported real algebraic numbers, and so on.

### Verified macros (coarse steps)

Fine-grained CPC can be too slow inside the engine; rewriting is the main case. For
those cases the engine may use a **macro step**, with:

- a theorem `∀ args, Provable F (macroConclusion args)`, proven once; and
- a **verified elaborator** used in proof mode, which expands the macro into real
  CPC steps, with a theorem that its output checks.

This is the static version of cvc5's macro rules that are elaborated during
proof post-processing.

## 3. Logos facts the agent needs

Toolchain: `leanprover/lean4:v4.34.0` (see `lean-toolchain`); Mathlib `v4.34.0`.

The project is split into two Lake projects, and the split matters:

- The **root package `Cpc`** (`lakefile.toml`) contains the checker, generated
  from `Cpc.eo` by `ethos-eoc`, and the parser. It has no Mathlib dependency.
- **`verification/`** (package `LogosVerification`) contains the SMT-LIB model
  semantics and all correctness proofs, and depends on Mathlib. Its libraries
  include `CpcVerification` (globs `Cpc.Proofs.+`, `Cpc.SmtModel`, …).

The new solver needs both: the executable side imports `Cpc`, and the proof side
imports `LogosVerification`. Keep the same split in the new repo (§4) so the solver
binary builds without Mathlib.

Definitions to build on (generated code is in `Cpc/Logos.lean`, `Cpc/LogosTerm.lean`):

| Name | Where | Role |
|---|---|---|
| `Eo.Term`, `Eo.Proof` | `Cpc/LogosTerm.lean`, `Cpc/Logos.lean` | Terms; `Term.Stuck` signals a failed program. |
| `CRule`, `CArgList`, `CIndexList` | `Cpc/Logos.lean` | Rule names, rule arguments, premise indices. |
| `CCmd`, `CCmdList` | `Cpc/Logos.lean` | Proof commands: `assume_push`, `check_proven`, `step`, `step_pop`. |
| `CState`, `__eo_cmd_step_proven` | `Cpc/Logos.lean` | Checker state; the conclusion of a step, or `Stuck`. |
| `__eo_prog_<rule>` | `Cpc/Logos.lean` | The Eunoia program for each rule. |
| `eo_is_refutation F pf` | `Cpc/Logos.lean` (inductive `Prop`) | "The checker accepts `pf` as a refutation of `F`". |
| `correct___eo_is_refutation` | `Cpc/Proofs/Checker.lean` | Main soundness theorem: refutation ⇒ `eo_satisfiability (argListAssumes F) false`. |
| `correct___logos_check_proof` | `Cpc/ApiCorrect.lean` | The same, stated about a proof file's text. |
| `cmd_step_<rule>_properties` | `Cpc/Proofs/Rules/<Rule>.lean` | Per-rule soundness, stated as `StepRuleProperties M (premiseTermList s premises) (__eo_cmd_step_proven s CRule.<rule> args premises)`. |
| `SmtModel`, `model_wf`, `eo_interprets` | `Cpc/SmtModel.lean`, `Cpc/Spec.lean` | Model semantics; the spec for the SAT-side evaluator. |

Caveats documented in `Cpc/ApiCorrect.lean`:

- The s-expression reader and parser have **no correctness proof**.
- `logos` does **not** compare a proof's assumptions with an original input problem.

So the new solver's end-to-end theorem must be stated over the parsed assumptions.
It must also use the **same** parser for the problem the solver solves and the
problem the proof refutes; never let the engine parse independently.

## 4. Repository layout

```
<new-repo>/
  lakefile.toml            -- package `Solver`: requires Cpc (Logos root) only
  lean-toolchain           -- same as Logos
  Solver/
    Kernel/                -- Mode, Derived, Provable, proof log, rule combinators
    Kernel/Macros/         -- macro steps + elaborators
    Sat/                   -- CDCL core (clause DB of Derived clauses, trail, watches)
    Theory/                -- UF first; then LIA, BV
    Rewrite/               -- rewriter as macros
    Model/                 -- model construction + evaluator (runtime check)
    Frontend/              -- reuses the Logos parser; SMT-LIB driver
    Print/                 -- proof log → Eunoia text
    Main.lean
  verification/
    lakefile.toml          -- requires Solver + LogosVerification (+ Mathlib)
    Solver/Proofs/         -- proofs of combinator obligations, end-to-end theorems
  TRUSTED.md               -- trusted base inventory (see §6)
  test/                    -- SMT-LIB benchmarks; proofs cross-checked with Ethos and logos
```

Proof obligations that only need definitions from `Cpc` can sit next to the code.
Anything that needs `SmtModel`, real numbers or Logos rule proofs goes under
`verification/`. If `Derived.ok` has to mention semantic notions, find out first
whether `Provable` (§5, milestone 1) can be stated with `Cpc` definitions alone;
it should be, since it is about checker acceptance.

## 5. Milestones

Do them in order. Each has an acceptance criterion; do not start the next one until
it is met.

### M0: Skeleton
- Create the repo, the two Lake projects, pinned toolchain, CI that builds both.
- Build Logos as a dependency (path or git dependency on this repo).
- **Done when:** `lake build` works in both projects and a trivial `Solver` module
  can `import Cpc` and mention `CRule.resolution`.

### M1: `Provable` and composition (highest risk; do this first)
- Define `Provable F c`: there exists a command list that, run from the state
  built by assuming `F`, yields a state in which `c` is proven. Use Logos's own
  state-transition functions (`__eo_invoke_assume_list`, `__eo_invoke_cmd_list`,
  `CState`).
- **Risk:** CPC premises are positional indices into the checker state
  (`CIndexList`). Combining two existential derivations needs a
  concatenation/reindexing lemma: if `pf₁` proves `a` and `pf₂` proves `b`, then
  some list proves both, with known indices. Prove that lemma first. If it is too
  painful, choose a different `Provable` (for example one indexed by an explicit
  log) and record why.
- Write combinators for three rules: `refl`, `resolution` (or `chain_resolution`),
  and one RARE rewrite rule such as `bv_ashr_zero`. Discharge each `Provable`
  obligation **by reusing** the existing `cmd_step_<rule>_properties` and
  `correct___eo_is_refutation` machinery, not by reproving rule soundness.
- Prove `Provable F false → eo_satisfiability (argListAssumes F) false` (plus the
  translation side conditions that `correct___eo_is_refutation` requires).
- **Done when:** these build with no `sorry`. Write a short report for the user
  covering whether the Logos statements plugged in directly or needed restating,
  and which lemmas would be worth adding upstream to Logos.

### M2: Proof mode and log
- Implement `Mode.proof`: an append-only log of `CCmd`, with `Derived.pf` as a step id.
- Theorem: in proof mode, `Derived` invariant ⇒ the log prefix up to `pf` checks
  with conclusion `c`. Final log for `false` ⇒ `eo_is_refutation F log`.
- Printer from `CCmdList` to Eunoia text. Prove the round-trip lemma
  `parse (print log) = log` against the Logos parser, or add it to `TRUSTED.md`
  until it is proven.
- **Done when:** a hand-built refutation in proof mode prints a file that
  `logos` and Ethos both accept, and the theorems have no `sorry`.

### M3: Propositional solver
- CDCL over `Derived` clauses: clause DB, trail, two-watched literals,
  first-UIP conflict analysis producing a `chain_resolution` combinator call.
- Tseitin/CNF via the CPC `cnf_*` rules.
- Performance experiment: compare against CaDiCaL (time only) on a small SAT
  benchmark set. Report the slowdown factor and the profile. This decides whether the
  SAT core stays in Lean (see §7).
- **Done when:** the solver answers QF propositional SMT-LIB benchmarks correctly,
  proof mode output is accepted by `logos` and Ethos, and the end-to-end
  theorem for `unsat` holds.

### M4: SAT answers
- Model construction plus a runtime evaluator verified against `SmtModel`
  (`eo_interprets`). Theorem: evaluator returns true ⇒ the model satisfies the
  input, and therefore `sat` is correct.
- **Done when:** the full end-to-end theorem covers both `sat` and `unsat`.

### M5: Theories
- QF_UF (congruence closure, emitting `cong`/`trans`/`symm` steps), then QF_LIA,
  then QF_BV. Theory lemmas are `Derived` facts and go into the SAT core.
- Rewriter as verified macros (§2).
- **Use only rules that have a proof in `Cpc/Proofs/Rules/`.** At the start of
  this milestone, write a script that lists `CRule` constructors without a
  `cmd_step_<rule>_properties` theorem, and keep that list in the repo.

## 6. Trusted base (`TRUSTED.md`)

Keep an explicit, current list. Start with:

- Lean kernel, compiler, and runtime.
- The Logos/CPC definitions as the **specification** (`Cpc.eo` compiled by
  `ethos-eoc`), and the model semantics `Cpc/SmtModel.lean`.
- The s-expression reader and parser (unverified in Logos).
- The proof printer, until the round-trip lemma is proven.
- Every `implemented_by`, `@[extern]` or `unsafe` in the solver, each with a reason.

No `sorry` and no new `axiom` is allowed on `main`. CI must fail on either
(`#print axioms` on the end-to-end theorems must show only `propext`,
`Classical.choice` and `Quot.sound`).

## 7. Open decisions (report back; do not decide alone)

- **Is the SAT core fast enough in Lean?** This is decided by the M3 experiment. The fallback is
  an external Rust SAT core that *proposes* conflict clauses and resolution chains,
  which the Lean kernel re-derives through `Derived` combinators. Each learned
  clause is then checked once, but never stored as a proof.
- **The exact form of `Provable`** (M1).
- **Upstream changes to Logos:** lemmas useful for `Derived` composition should
  probably live in Logos. Propose them to the user rather than forking.

## 8. Related Logos work (not in the new repo)

Logos does not memoize, and `native_teq` (`Cpc/LogosTerm.lean`) is structural
`DecidableEq` with no pointer-equality fast path. That makes checking slow on
heavily shared proofs. The solver's guarantee does not depend on running Logos,
but proof consumers do, so the solver's proof output should use sharing (as the
`step` log does by design). The planned Logos-side fixes are:

1. a pointer-equality fast path for `native_teq` via `implemented_by`;
2. hash-consing or `ShareCommon` on parsed proofs;
3. memoized generated programs, preferably verified through a generic
   `memoFix F = fix F` theorem.

These are tracked separately in Logos.

## 9. Working conventions

- Small commits; every commit builds both projects.
- Never weaken a theorem statement to make it pass. If an obligation fails,
  stop and report.
- When a Logos statement is awkward to use, write an adapter lemma in the new
  repo and note it as an upstream candidate; do not edit Logos from the new repo.
