# Porting cvc5's theory engine: notes

Status: sketch (2026-11-20). This replaces the solver part of
[`solver-plan.md`](solver-plan.md), which planned a separate repository. The
work now happens in telos and reuses its certificates, its rewriter and its
preprocessor.

## Scope

- **Target configuration:** `cvc5 --safe-mode=safe --ee-mode=central
  --produce-proofs`.
  - cvc5 accepts this combination. `ee-mode` is a *regular* option, and safe
    mode allows at most one regular option, so we can't add any other regular
    option.
  - We match cvc5 *with* proofs on, as for preprocessing. Proofs change cvc5's
    behaviour: with proofs, propagations are explained as lemmas
    (`:source EXPLAINED_PROPAGATION` under `-o lemmas`).
- **What safe mode implies:**
  - sep, bags, ff and fp are off, and so are the experimental extensions
    (`arithExp`, `datatypesExp`, `ufHoExp`, …), the UF symmetry breaker and
    `nlCov`.
  - **`--arith-eq-solver` is an expert option**, so it is unavailable. That means
    **arithmetic does not use the central equality engine** even in central
    mode: it keeps its own reasoning and talks to the others through shared
    terms and theory combination (care graphs).
  - **The BV solver is `bitblast-internal`**: BV atoms are bit-blasted into
    clauses for the main SAT solver. Without a SAT solver, BV gets no further
    than what the equality engine does.
- **Which theories use the central EE** (`EqEngineManagerCentral::usesCentralEqualityEngine`):
  builtin, UF, datatypes, sets, strings, arrays and BV (bags, fp and sep are
  off). For quantified logics, the master EE is the central EE.
- **No SAT solver yet; inputs are conjunctions of literals.** All the literals
  are asserted at decision level 0, and the theories run `check` to a fixpoint.
  This reaches only part of the problem, because theory lemmas are often
  disjunctions: splits, datatype and string case splits, arithmetic branching.
  See [Replay](#replay-decoupling-the-sat-solver) for how to get past that
  without writing a SAT solver.

## Differential testing by events

The preprocessor is tested by comparing its output with cvc5's
`-o post-asserts`. For the solver, the comparable output is the **sequence of
events** at the boundary of each theory solver.

### Events

Implemented as a cvc5 patch, `cvc5-theory-events.patch` (2026-11-20), which
adds two output tags. Every event is one line, an s-expression whose first
argument `k` is the **SAT context level** when the event happens. Pushes are
implicit, in the level going up; pops are explicit. `T` is a `TheoryId`
(`THEORY_UF`, …), `id` an `InferenceId`, and terms print as in `-o lemmas` (with
`let`s).

The trace is split into **inputs**, which the theory engine and the SAT side
hand to a theory, and **outputs**, which a theory produces.

`-o theory-events`:

| Kind | Event | cvc5 location |
|---|---|---|
| input | `(prereg k t)`: an atom registered with the theory engine | `TheoryEngine::preRegister` |
| input | `(assert k T lit)`: a literal given to theory T, from the SAT solver or from theory combination | `Theory::assertFact` |
| input | `(check k T effort)`: a `check` call (`EFFORT_STANDARD`, `EFFORT_FULL`, `EFFORT_LAST_CALL`) | `Theory::check`, at entry, before the early exit |
| input | `(pop k)`: the SAT context was popped, and is now at level k | a `ContextNotifyObj` on the SAT context |
| output | `(fact k T id lit exp)`: an internal fact asserted to the EE | `TheoryInferenceManager::processInternalFact` |
| output | `(lemma k T id φ)` | `TheoryEngine::lemma` (so it includes combination lemmas) |
| output | `(conflict k T id conj)`: the conflicting conjunction | `TheoryEngine::conflict` |
| output | `(propagate k T lit)` | `TheoryEngine::propagate` |
| output | `(explain k lit exp)`: a propagation's explanation, when the SAT solver asks for it | `TheoryEngine::getExplanation` |
| output | `(phase k lit pol)` | `OutputChannel::preferPhase` |
| output | `(model-unsound k T id)`, `(refutation-unsound k T id)` | `TheoryEngine::setModelUnsound` / `setRefutationUnsound` |

`-o theory-events-ee`, the central EE's notifications to the theories, used to
localize where the two sides diverge:

| Event | cvc5 location |
|---|---|
| `(ee-new-class k t)` | `EqEngineManagerCentral::CentralNotifyClass::eqNotifyNewClass` |
| `(ee-merge k t₁ t₂)` | `…::eqNotifyMerge` |
| `(ee-diseq k t₁ t₂ reason)` | `…::eqNotifyDisequal` |

What the first runs show:

- **A conflict is often a SAT conflict, not a theory one.** The theory
  propagates a literal that the SAT solver already has false, and the
  explanation is the `explain` event. The QF_UF example in the patch's
  regression ends that way: there is no `conflict` event.
- **Solving starts at level 1, not 0.**
- **In central mode, propagations from the central EE are under
  `THEORY_BUILTIN`.**
- **The same literal can be propagated twice in a row** (via the shared-terms
  path). That is real cvc5 behaviour, which the comparison has to allow for or
  reproduce.
- **The volume is large.** 300 regress0 benchmarks gave 2.1M `assert` events
  and 370k `check` events, so the comparator must stream.

Not yet covered:

- the quantifiers engine (`QuantifiersEngine::check` is not `Theory::check`);
- decision-strategy literals (`DecisionManager`);
- the EE internals of the non-central EEs (arithmetic's).

The patch was checked as follows:

- answers are unchanged with the tags on, across 400 regress0 benchmarks;
- every event line is a balanced s-expression;
- the printer regressions pass, including the new
  `regress0/printer/theory-events.smt2`.

### The cvc5 side

- **An output tag, not `Trace`.** Release builds have tracing off. Output tags
  work there and cost one bit test per hook when off, like `-o lemmas`.
- **Terms use the default printer,** the same one as `-o post-asserts`, so the
  comparator can reuse `fuzz-pp.py`'s normalization: alpha-renaming,
  definitions and skolem names.
- **It could go upstream as a debugging aid** (see `upstream-requests.md`).

### The telos side

- **An `Event` type, and a theory monad that logs it.** The inference-manager
  operations (`lemma`, `conflict`, `assertInternalFact`, `propagate`) are the
  only way a theory changes global state, and each appends an event.
- **The log is not on the proof path.** Like proof output, it is post-hoc and
  must not change results; the
  proof output policy (`README.md`, "The preprocessor") carries over.

### Comparing

- **Rounds:** the log is cut into rounds at input events.
- **Within a round, outputs are compared as multisets.** cvc5 iterates over
  hash maps keyed by node ids, so the order of events inside a round is not
  meaningful. The preprocessor fuzzing already ran into node-id ordering.
- **The rounds themselves are compared in order.**
- **On a mismatch, report the first round that differs,** with both multisets,
  then switch on the EE-internals level to localize it.
- **Conflicts and lemmas get two levels of agreement:**
  - *exact*: the same term after normalization;
  - *same literals*: the same set of literals, which allows a different
    explanation path in the EE.

  Expect to pass "same literals" well before "exact".

## Replay: decoupling the SAT solver

Running on conjunctions alone stalls at the first disjunctive lemma. A
**replay mode** removes the SAT solver from the comparison entirely:

- **telos reads cvc5's input events** (`prereg`, `assert`, `check`, `push`/`pop`,
  EE notifications) and feeds them to its own theories.
- **telos produces its own outputs,** and the comparator checks them round by
  round.
- **cvc5's SAT decisions become just more inputs:** the literals asserted after
  a disjunctive lemma, the backtracks, the next `check`. telos needs no SAT
  solver and no decision heuristic to follow cvc5 into the search.
- **Stop at the first divergence.** After it, cvc5's next inputs no longer
  follow from telos's outputs.

Replay is exactly "conjunctions" in general form. A conjunction is the special
case with one `push`, all the `assert`s, and `check(full)` until quiescence.
There are then two modes:

- **Standalone (S):** telos asserts the conjunction itself and runs `check` to a
  fixpoint. It answers `unsat` on a conflict, and `unknown` on any lemma that
  is not a unit. This mode is end-to-end and carries the soundness theorem.
- **Replay (R):** cvc5 drives. This mode is only for differential testing.

Replay needs backtrackable theory state from the start, the analogue of cvc5's
`context::CDO`/`CDList`. That is a real design decision for Lean:

- *Persistent structures plus snapshots:* simple, but keeping old versions
  defeats in-place updates, the same array-copy trap as `Proof.push`.
- *Trail-based undo on uniquely owned arrays:* cvc5's own approach, and the one
  to use for the EE.

## Soundness and proofs

Each output event carries a certificate, in the style of `Certified`:

- **lemma φ:** φ is valid;
- **conflict φ:** the asserted literals entail `false`, with `φ` their negated
  conjunction;
- **fact and propagation:** the explanation entails the literal.

Mode S then gets the theorem "`unsat` ⇒ the input is unsatisfiable", composed
with `Telos.preprocess_correct`.

The certificates are checked when they are made; the end goal is to check
them without Logos at run time (`docs/design.md`, Roadmap).

The CPC proof is emitted afterwards from the EE's proof forest, which uses
`trans`, `cong`, `symm`, `true_intro`/`false_intro` and so on, as cvc5's
`ProofEqEngine` does, and through `Proof.emitChainWith`. As for preprocessing,
results are the same with and without proofs.

## Fidelity mode and fast mode

The engine is a port of cvc5, compared with it event by event, so where cvc5's
choices are arbitrary (they follow node ids, hash maps, creation order) telos
imitates them. That imitation is for testing only. The design:
- **Fidelity mode** (the default, used by `--theory-events`, `--replay` and the
  fuzzer) makes the same choices as cvc5 wherever telos can, so that the events
  match.
- **A fast mode** may make other choices, cheaper or simpler, and its events
  may differ from cvc5's. What it must keep is the answers' certificates: an
  `unsat` is certified by its explanation, a `sat` by its model, whatever the
  choices that led to them. So no choice of this kind needs a proof, and the
  correctness theorems hold in both modes (they quantify over the setting).

Only choices that decide the *form* of what is produced belong to this
switch, not the reasoning. Each such imitation is marked and goes under the
switch. Now: `Solver.Config.cvc5Order` (off with `--no-cvc5-order`), which
imitates cvc5's order of nodes to orient the equalities of shared terms and of
lemma atoms, and rewrites lemma atoms as cvc5's preprocessing does.
Candidates as the engine grows: the order of classes in the splits (cvc5's
`std::set<Node>`), the order of explanations, and the replay's emulation of the
SAT solver (replay only).

## Stage 1: conjunctions of literals

The input is an SMT-LIB script. It goes through telos's preprocessor, which
already matches cvc5's `-o post-asserts`. If every remaining assertion is a
literal, the literals are asserted one at a time; otherwise the answer is
`unsupported`. There is no SAT solver, no decision and no backtracking, so
every event is at level 1 and there is no `pop`.

### What cvc5 does on such inputs (observed with `-o theory-events`)

1. `prereg` for each atom, in assertion order, as the CNF stream meets it. cvc5
   first preregisters `true` and `false` at level 0.
2. `assert` for each literal, in assertion order, to `theoryOf` its atom.
3. `check EFFORT_STANDARD`, for each enabled theory that has a check, in
   theory-id order.
4. `propagate`s. In central mode they come from `THEORY_BUILTIN`, including for
   literals that were already asserted.
5. A propagated literal that is false in the assignment is a SAT conflict: the
   SAT solver asks for an `explain`, and the answer is `unsat`. A conflict
   inside a theory is a `conflict` event.
6. Otherwise `check EFFORT_FULL`. If it produces nothing, the answer is `sat`.

### Fuzzing has to get past preprocessing

Preprocessing solves most equalities between variables: the substitution
`a := b`, and `a := (f b)` when it isn't cyclic. A random conjunction is
usually decided, or reduced to almost nothing, before the theory engine sees
it. The generator has to produce literals that survive: disequalities,
predicates, cyclic equalities such as `(= b (f (f b)))`, and equalities between
applications. Then it should keep only the benchmarks whose post-asserts are
all literals.

### Components

- **`Telos/Solver/Event.lean`:** the events, printed exactly as cvc5 prints them
  (the `let` printer of `-o post-asserts`), plus `TheoryId`, `InferenceId` (the
  ones used so far) and `Effort`.
- **`Telos/Solver/Assignment.lean`, a stand-in for the SAT solver:** the values
  of the literals, the queue of propagations, and a conflict when a propagated
  literal is false, which triggers `explain`. On units it behaves like minisat.
  It is also where lemmas will go: a lemma that is a unit is asserted, and on a
  lemma that is not, the engine stops with `unknown`.
- **`Telos/Solver/EqualityEngine.lean`:** a faithful port of
  `uf/equality_engine.cpp`:
  - node ids and curried applications;
  - use lists and the lookup table;
  - the equality graph with reasons;
  - the choice of representative;
  - the pending queue;
  - triggers (term equalities and predicates);
  - disequalities;
  - `explain`.

  It keeps a trail from the start, but undo comes later.
- **`Telos/Solver/Theory/UF.lean`:** `TheoryUF` in central mode. It registers
  terms and triggers, takes facts, and propagates and reports conflicts from the
  EE's notifications (including merges of constants, such as `true` with
  `false`).
- **`Telos/Solver/TheoryEngine.lean`:**
  - `theoryOf` (ported from `Theory::theoryOf`, with the default `theoryof-mode`);
  - `preRegister`, `assertToTheory` and the `check` loop;
  - `propagate`, `getExplanation`, `lemma` and `conflict`;
  - the central EE manager.
- **The `--theory-events` command-line mode:** it prints the events, then the
  answer.
- **`scripts/fuzz-solve.py`:** runs cvc5 with the patch and telos on the same
  input, and compares the events by rounds. It reports agreement at two
  levels: exact, and same literals.
- **`test/solve/`:** inputs with expected traces, run by CI.

### Soundness

An `explain` or a conflict comes with an **equality proof**: a tree of
`assume`, `refl`, `symm`, `trans` and `cong`, like cvc5's `eq::EqProof`, built
by the EE's `explain`.

- **Static soundness:** a small checker on Nodes, which is decidable and
  linear in the size of the DAG, with a semantic theorem in `verification/`. If
  the check returns `(a, b)` and the assumptions hold in M, then `a = b` in M.
  That gives "`unsat` ⇒ the input is unsatisfiable", composed with
  `preprocess_correct`.
- **Cost:** the check runs only on conflicts, so it costs about as much as the
  explanation.
- **Proofs:** the same tree prints as CPC (`trans`, `cong`, `symm`, `true_intro`
  and `false_intro`) for `--proof`.
- **What is not needed:** no invariant of the EE is proven, and Logos is not
  called.

### Preprocessed inputs: fidelity, not soundness

The engine expects preprocessed literals: rewritten atoms, no term `ite`s, and
the operators that theory preprocessing eliminates gone. Today the front end
(`Telos/Frontend/Solve.lean`) runs the preprocessor and passes the result to
`Solver.run`, which takes any `List Node` and assumes nothing about it.

The proposal, pending the user's decision, is to treat this expectation as a
condition for fidelity, not for soundness:

- **Soundness assumes nothing about the input.** The engine's theorems are
  stated over any well-typed literals: `unsat` means the literals are
  unsatisfiable, because every conflict carries a certificate checked on the
  actual nodes; `sat` means they are satisfiable, because the model is evaluated
  on the actual nodes. The front end composes this with
  `preprocess_correct`.
- **Fidelity is checked where the input arrives.** A decidable predicate checks
  that the input is a literal in preprocessed form. Inputs that fail it are
  `unsupported`. Inputs that pass it but break a theory's expectations give
  `unknown`, or a trace that differs from cvc5's, and never a wrong answer.
- **Local structure is parsed, not assumed.** A theory that needs a normal form,
  such as arithmetic's `(>= p c)`, parses the atom into its own
  representation, with a lemma that the parse means the same as the node. A
  parse that fails gives `unsupported` or `unknown`.
- **No proof-carrying "came from the preprocessor" type.** Such a type would
  need proofs that preprocessing establishes the invariants. Some of them,
  idempotence of the rewriter for example, are not true of cvc5, which telos
  matches. Also, cvc5 preprocesses lemmas too (`TheoryPreprocessor`: rewriting,
  `ite` removal, `ppRewrite`), so the invariants would have to be
  re-established inside the engine anyway. The engine will call the rewriter
  and theory preprocessing on its lemmas as a library.

### Milestones

1. **The driver.** *Done (2026-11-20).*
   - check that the post-asserts are all literals;
   - `prereg`, `assert` and `check` events;
   - the stand-in for the SAT solver;
   - a trivial engine with no theories, which reproduces cvc5's event skeleton
     on pure Boolean inputs.

   Status: `Telos/Solver/Event.lean`, `Telos/Solver/Engine.lean`,
   `Telos/Frontend/Solve.lean`, `telos --theory-events`,
   `scripts/fuzz-solve.py` (with `--recorded`) and `test/solve/`.
   - On the fuzzer's random QF_UF conjunctions (300, seed 3), the input events
     (`prereg`, `assert`, `check`) agree with cvc5's on 299. The remaining one
     differs only after a conflict that cvc5 finds by propagation.
   - The events agree completely on 36: those where the UF solver propagates
     nothing.
   - All the other differences are the UF solver's missing propagations,
     explanations and answers.

   Details of the skeleton:
   - The enabled theories are those of the widened logic, with strings
     enabling UF and quantifiers (as observed).
   - The theories outside safe mode are not modelled. cvc5 enables FF, FP,
     SEP and BAGS for `ALL`, and their checks do nothing there; the comparator
     drops their events from cvc5's traces. Logics that require them are
     unsupported.
   - Boolean variables are neither preregistered nor asserted to a theory.
   - The children of a top-level `and` are asserted as units.
   - The answer is `sat` only when no theory got a literal.
2. **The EE and UF on QF_UF:**
   - Target: the events agree exactly with cvc5 on the fuzzed conjunctions.
   - The fidelity points are the order of propagations, the choice of
     representative, and the order of the literals in explanations.

   *Done (2026-11-20).*
   - Files: `Telos/Solver/EqualityEngine.lean` (the port of
     `uf/equality_engine.cpp`), `Telos/Solver/Theory/UF.lean`, and the engine,
     which now has:
     - the preregistration visitor (`PreRegisterVisitor`: post-order,
       children last first, with the theories of each term, its parent and
       its type);
     - UF's fact processing;
     - the central EE's propagations and `EQ_CONSTANT_MERGE` conflicts as
       `THEORY_BUILTIN`'s;
     - the stand-in for the SAT solver's handling of propagated literals
       (false: `explain` and `unsat`; unassigned: asserted).
   - New options: `--theory-events-ee` prints the central EE's notifications;
     `--no-preprocess` gives the assertions to the engine as they are.
   - Results:
     - On cvc5's own preprocessed assertions (`fuzz-solve.py --cvc5-pp --ee`),
       the traces are identical as text, EE notifications included. That
       holds for 1500 random QF_UF conjunctions of up to 25 literals over
       `f`, `g`, `h`, `P` and `Q` (seeds 11, 12, 21–23), about half of them
       unsat.
     - It also holds for a conjunction of 7500 literals: a 60,000-line trace,
       in 0.38s against cvc5's 0.36s.
     - End to end, with telos's own preprocessing, the events agree up to the
       orientation of equalities, which is the preprocessor's known
       difference (cvc5 orients by node id). That changes which class becomes
       the representative, and so the order of later events.
   - Not ported yet: trigger terms and the trigger-term sets of constants (for
     sharing), interpreted kinds, and backtracking.
   - UF runs only when it is the only theory (no sharing, quantifier-free).
   - Observed and ported:
     - Two contradictory unit literals give `unsat` after preregistration,
       with no `assert`.
     - After the theory engine is in conflict, UF asserts no more facts,
       because `markInConflict` notifies every theory.
     - With proofs on, the explanation cache is not symmetric.

3. **Soundness and proofs:** the equality proofs, the checker and its theorem,
   and CPC proof output for `unsat`.

   *Done (2026-11-20).*
   - **Certificate** (`Telos/Solver/EqProof.lean`): `assume`, `symm`, `trans`,
     n-ary `cong`, and `eqTrue`.
     - The congruence rule carries a path from an assumption to the
       application, which makes the application well typed
       (`ChildTyping.children_wellTyped`).
     - The checker is linear on nodes. Its only call into Logos is
       `__eo_is_closed` on the conflict's assumptions, which makes the
       condition stable for congruence.
   - **Builder** (`Telos/Solver/EqBuild.lean`):
     - It follows the equality graph.
     - Curried congruence is reassembled argument by argument along the path
       between the internal nodes.
     - Reflexivity merges become `eqTrue`.
     - A congruence term that occurs in no literal of the explanation is
       reached through the asserted literal it occurs in, which is added to
       the assumptions.
   - **Engine:** every `unsat` comes with a certificate:
     - propagation conflicts (`explain`);
     - `EQ_CONSTANT_MERGE`;
     - contradictory units;
     - `false` from preprocessing.

     `Solver.run` answers `unsat` only if the certificate's assumptions are
     among the literals and it checks (`certifies`), and `unknown` otherwise,
     with a warning on standard error.
   - **Theorems:**
     - `verification/TelosProofs/Solver/EqProof.lean`: `check_sound` and
       `checkConflict_sound`.
     - `verification/TelosProofs/Solver/Solve.lean`: `run_unsat_sound`, and
       `Frontend.solveScript_unsat`. If the engine answers `unsat` on a script
       with Boolean assertions, no well-formed model satisfies the input
       assertions. The proof goes through the literals of the engine's
       assertions (`conjLiterals_sound`) and `preprocess_correct`.
     - `solveScript_unsat` is audited in `TelosProofs/Axioms.lean`, and
       `TelosFull` states the unconditional `Telos.solve_unsat_correct`.
     - To make this provable, the engine now works on the skolems themselves,
       which are renamed `@purify_k` only when printing.
   - **Proofs** (`Telos/Solver/EqProofCpc.lean`): with `--proof` or
     `--proof-dir`, the CPC refutation of the literals.
     - It uses `false_intro`, `true_intro`, `symm`, `trans`, `cong` with
       `refl`, and finally `symm` and `true_elim`.
     - The last step states `false`, so that a checker that accepts the proof
       has checked a refutation.
     - Telos does not check it itself; `fuzz-solve.py --proofs` has Ethos
       check it.
   - **Results:**
     - Every `unsat` of the fuzzing is certified: about 1,000 over seeds 31–35,
       41, 42, 51 and 52.
     - Ethos accepts every refutation: 193 over seeds 51 and 52, plus the 5 of
       `test/solve`.
     - A 4,000-literal transitivity conflict takes 0.39s, against cvc5's 0.45s.
       Its 13,000-line proof is accepted by Ethos in 0.1s.
   - **Not covered:**
     - `sat` answers (they need a model, and its check, which is milestone 4
       of `solver-plan.md`);
     - disequalities explained by several reasons (rare; the builder fails,
       and the answer is `unknown`).
     - The subset check of `certifies` is quadratic, which is fine at these
       sizes.
4. **A second theory in the central EE:** arrays, then datatypes. These bring
   the first lemmas. The unit ones go through the stand-in; the first lemma
   that is not a unit ends the run with `unknown`, and also ends the
   comparison.
5. **Arithmetic and theory combination,** and with them, replay or the SAT
   solver.

## Stage 2: backtracking and replay

*Done (2026-11-20).*

### Backtracking

The equality engine is context dependent, as cvc5's is
(`Telos/Solver/EqualityEngine.lean`, "Context levels"):
- **Push** saves its counters, which are cvc5's `CDO`s: nodes, merges, lookups,
  triggers, deduced disequalities and their reasons, the log of the propagated
  disequalities, and `done`.
- **Pop** restores them and undoes what came after, in cvc5's order
  (`backtrack`, `undoMerge`):
  - merges, by swapping the rings back and resetting finds and trigger
    classes;
  - graph edges;
  - triggers;
  - lookups;
  - nodes, with their use lists;
  - disequality reasons;
  - the propagated-disequality map.

The engine's own context-dependent state is saved likewise (`Saved`, `pushLevel`,
`popTo`):
- the SAT assignment (a trail);
- the preregistration cache (a log);
- UF's facts and how many it has processed;
- `factsAsserted`;
- the conflict flags;
- the propagated and asserted literals.

The equality engine's notion of "the theory engine is in conflict" is copied
from the engine's at each call, so that it is restored on pop as well.

### Replay

With `telos --replay TRACE FILE` (`Telos/Frontend/Replay.lean`, `Solver.replay`):
- **Inputs:** telos reads cvc5's trace and gives its theories the inputs, in
  order:
  - `prereg`, `assert` and `check`, at their levels (pushes are implicit);
  - `pop`;
  - requests for explanations (`explain`): telos computes its own, which are
    compared.
- **Terms:** the trace's terms are read as `simplify` queries of `FILE`, which
  is cvc5's `-o post-asserts` output, so the skolems are its `@purify_k`
  symbols.
- **Comparison:** `fuzz-solve.py --replay` runs cvc5, splits its output into
  the preprocessed benchmark and the trace, replays it, and compares. The
  random benchmarks then have disjunctions.

### Results

- **Random benchmarks:**
  - 900 random QF_UF benchmarks with clauses (seeds 61–63, up to 20
    assertions, 320 of them with backtracking): 897 traces identical to
    cvc5's as text, EE notifications included.
  - 200 larger ones (seed 64, up to 50 assertions): 194 identical.
- **The other cases** differ only in explanations that cvc5 minimized:
  - With proofs, cvc5 shrinks an explanation to the assumptions its proof uses
    (`ProofNodeManager::mkScope`), and the proof may reuse facts proven
    before.
  - So some of cvc5's explanations are strict subsets of the equality engine's,
    in hash-set order.
  - Without `--produce-proofs`, cvc5's explanations are exactly telos's.
  - The comparator counts these separately ("up to cvc5's minimized
    explanations").
- **cvc5's regressions:** all 25 QF_UF regressions that cvc5 accepts and telos
  supports agree, 2 of them only up to minimized explanations.
- **Boolean term skolems:** the regressions showed that cvc5 treats Boolean
  term skolems as theory atoms of UF (`Env::isBooleanTermSkolem`, `CnfStream`).
  These are the purification skolems of Boolean terms in term positions; telos
  now does too (`isBooleanTermSkolem`).
- **Speed:** a 600-clause benchmark with a 31,600-line trace and 1,688 pops
  replays in 0.96s, against cvc5's 0.37s. Reading the trace's terms is part of
  that.
- **Tests:** `test/replay/` holds recorded traces, which CI replays.

### Not covered

- `unsat` answers in replay: the answer is the SAT solver's. Conflicts are
  still compared as events.
- The minimization of explanations by cvc5's proofs: it would need its proof
  equality engine and proof cache.

## Stage 3: verified explanations

*Done (2026-11-20).*

The equality engine's explanations are proven sound, so conflicts need no
separate certificate (`Telos/Solver/Explain.lean`, and its proofs in
`verification/TelosProofs/Solver/Explain.lean`).

### The explanation

`EE.qFull`/`EE.qArgs`, with `EE.explainLitV` for literals, is the explanation,
computed as cvc5's `getExplanation` computes it:
- the same breadth-first path (`findPath`), from its end back;
- the reasons in cvc5's order;
- a cache of completed queries.

cvc5 also caches queries in progress. That differs only on cyclic queries,
which cannot happen in its forest.

Each step checks what its soundness needs, at a constant cost, or a cost in
the number of arguments:
- **asserted edge:** its reason relates the edge's terms;
- **congruence edge:**
  - the application is reached from a root, an input literal, through
    operators whose children are well typed;
  - its arguments are those the explanations of the arguments found
    (`argsMatch`);
  - curried prefixes are explained position by position (`Rel`);
- **reflexivity edge:** `(= a b)` is reached from a root and is that of the
  edge;
- **path:** a chain from the start to the end (`chainOk`).

Recursion is bounded by fuel. If any check fails, or the fuel runs out, the
explanation fails, and the engine falls back to the certificate.

### The theorem

`queries_sound`, and from it `explainLitV_sound`: if the explanation succeeds,
then in every well-formed model of its reasons, the literal is true.
- **Hypotheses:** the reasons are Boolean and closed, and the roots are well
  typed.
- **No invariant of the engine:** the theorem rests only on the checks, so it
  holds whatever the engine's state.
- **Proof:** by induction on fuel, in layers. The queries at fuel `n` give the
  edges and steps at `n`, which give the queries at `n + 1`.

### Use

In `Solver.run`, the conflict's explanation is the last event. It is now
computed once, at the end, by `certifyV`:
- the roots are the input literals;
- the reasons must be among them, and closed;
- for a propagation conflict, the negated literal must be among them too.

`run_unsat_sound` covers both routes, `certifyV_sound` and the certificate. The
certificate builder (`EqBuild`) runs only as a fallback, and for `--proof`.

In replay, the explanations are the verified ones, with the registered atoms as
roots (`addRoot`), and the old explanation only as a fallback. All 337
explanations of the 600-clause trace are verified ones, with the same events
as before.

### Results

- **Events:** identical to cvc5's on cvc5's preprocessed inputs (seeds 81, 82
  and 91).
- **Answers:** every `unsat` was certified by the verified explanation, with no
  fallback to the certificate.
- **Proofs:** Ethos accepts all the refutations.
- **Two in-place update bugs.** In both, an update was computed from a field
  while the old state still held it, so Lean copied the whole map on every
  call:
  - the preregistration log (`setVisited`);
  - the log of propagated disequalities (`storePropagatedDiseq`).

  With these fixed:
  - the 4,000-literal chain takes 0.22s, against 3.5s with the bugs;
  - the large `unsat` takes 0.52s, against 0.39s with the old certificate,
    the difference being the quadratic subset check, 53ms;
  - the 600-clause replay takes 0.70s.

### Still dynamic

- **The checks themselves.** They become unnecessary once the engine's
  invariants are proven: that its edges match its nodes, and that its terms
  are subterms of registered atoms. That needs the engine rewritten as total
  code.
- **The closedness of the reasons**, checked through Logos once per answer.
- **The subset check of the reasons**, which is quadratic.

## Stage 4: certified `sat`

A `sat` answer is certified by a model, checked by **evaluation**, not by the
rewriter: the model is a substitution (values for the free constants, finite
tables for the functions), and the input assertions must evaluate to `true`
under it. Evaluation is complete for ground terms over the model's values, and
it is cheap and simple to prove; the rewriter would add nothing.

### The model

`Telos/Solver/Model.lean`:
- **Values** (`MVal`): Booleans, the elements of uninterpreted sorts
  (numbered), and functions, given by tables with a default, curried as in
  Logos.
- **The builder** (`buildModel`), as cvc5's `TheoryEngineModelBuilder` does
  for UF:
  - each class of an uninterpreted sort is an element of its own;
  - each relevant application gives an entry of its function's table;
  - then the definitions of the variables solved by preprocessing are
    evaluated, and the other constants get defaults.
- **The relevant terms** (`relevantTerms`): the subterms of the asserted
  literals, as `Theory::computeRelevantTerms`. Only these are considered, so
  terms of the central equality engine that are not relevant (from atoms that
  were registered but never asserted) give no table entries.
- **The check** (`Model.satisfies`): the tables and constants are well typed,
  and every input assertion evaluates to `true`. The evaluator is memoized on
  nodes, so it is linear in the DAG. It covers the Boolean connectives,
  equality, `distinct`, `ite`, constants, and applications of declared
  functions; anything else evaluates to nothing, and the answer is `unknown`.
  For `distinct`, the elements must have one Logos type, as Logos's
  translation requires (checked with Logos's own typing).

### The theorem

`verification/TelosProofs/Solver/Model.lean`:
- `toSmtModel M`, the Logos model of a model, interprets the constants by
  their values, the function identifiers by the tables, and every other
  symbol by the default of its type.
- `toSmtModel_wf`: it is well formed, given the well-typedness that
  `satisfies` checks. This uses one new `LogosFacts` field, the typing and
  canonicity of `__smtx_type_default`
  (`type_default_typed_canonical_of_type_wf`).
- `ev_sound`: by induction on the fuel, with a memo invariant, every value
  `Model.ev` gives is the value of the node in `toSmtModel M`.
- `satisfies_sound`, then `Frontend.solveScript_sat` and
  `Telos.solve_sat_correct`: a `sat` answer means the input assertions are
  true in a well-formed model.

### Results

All the `sat` answers of the fuzzer are certified (seeds 101 to 107), and the
events are unchanged.

### Several theories: the model equality engine

cvc5 builds models in a separate *model equality engine*, filled by each
theory (`collectModelInfo`) with its relevant terms only. It is a filtering of
the central engine: irrelevant terms must not constrain the model.

For UF alone, the classes of the relevant terms in the central engine are the
same, so the builder filters the central engine instead. The plan for when a
second theory arrives (arrays, datatypes, arithmetic):
- port `TheoryModel` with its own equality engine, filled per theory from its
  relevant terms;
- port `TheoryEngineModelBuilder` (the assignment of values to classes, by
  type, with the theories' fixed values first);
- keep the check unchanged: the builder stays untrusted, and the evaluator
  grows with the theories' operators.

## Stage 5: datatypes (in progress)

Safe mode excludes codatatypes and sygus; with proofs, shared selectors are
off. The other options keep their defaults: no binary splits, one split lemma
per check, cycle checks, and an instantiation is a lemma only when the
constructor has a finite argument of another type (`dtPoliteOptimize`; an
uninterpreted sort counts, being "interpreted one").

### Design

- `Telos/Solver/Theory/DtType.lean`: cardinality classes, and the terms the
  theory builds (`getInstCons`, testers, splits, `checkClash`).
- `Telos/Solver/Theory/DtState.lean`: the theory's state as data, with a trail
  for its context-dependent parts.
- `Telos/Solver/Theory/Datatypes.lean`: the port of `theory_datatypes.cpp` and
  its inference manager.
- **Synchronous notifications.** The theory reacts to the central engine's
  new classes and merges while the engine propagates, reading representatives
  as they are then, and may raise a conflict in the middle. Its state is a
  field of the engine (`EqualityEngine.dt`), and the engine calls a hook
  (`Ctx.onNote`) at each notification. The theory's facts, lemmas and conflicts
  are notes, turned into events in order.
- **Explanations.** An internal fact is asserted with its explanation as its
  reason (`ProofEqEngine::assertFact`), so the theory's conflicts stop at
  those explanations. The explanation of a propagation for the SAT solver
  expands them further (`TheoryEngine::getExplanation`).
- **Testers' operators** are their own nodes in the engine (cvc5's `is_C`):
  otherwise `(is_C x)` would be the partial application `(C x)`.
- **Soundness is unchanged.** A conflict of the theory, or one whose
  explanation uses an inferred edge (which the verified explanation's checks
  reject), stands only if its certificate checks (see "Certified `unsat`"
  below). In `solve`, a lemma (a split, say) needs the SAT solver, so the
  answer is `unknown`. Replay is the main test.

### Sharing

With two theories (UF is always on), cvc5 enables theory combination. Ported:
- **Trigger terms** in the equality engine (`addTriggerTerm`, the trigger sets
  of classes, their merges and disequalities, `eqNotifyTriggerTermEquality`).
  The central engine makes constants trigger terms of every theory (cvc5's 14
  tags, the unmodelled ones included).
- **Preregistration** by `SharedTermsVisitor`: a traversal per atom, a
  context-dependent cache of preregistrations, and the shared terms of each
  atom.
- **The shared terms database**: its trigger predicate for each equality atom,
  and the notification of shared terms when their atom is asserted
  (`Theory::addSharedTerm`).
- **Propagation with sharing**: only SAT literals go to the SAT solver, once
  per context. Shared equalities are asserted to datatypes as the engine
  produces them.
- **Lemmas**: their atoms are preregistered as the CNF stream meets them, which
  can process the theory's pending facts; datatypes' full-effort loop therefore
  runs at the engine level. An atom is registered again after a backtrack.

### Replay

- The purification skolems of the theories are mapped from the trace's
  `DATATYPES_PURIFY` lemmas to telos's skolems, and printed with cvc5's names.
- Inputs produced in the middle of a check (the shared equalities, the
  preregistration of a lemma's atoms) are produced by telos itself, and the
  trace's copies skipped. The comparator does not cut rounds at `prereg`.
- A replayed `assert` keeps the theory the trace gives it (a shared equality
  goes to the theory that asked for it, not to the theory of its atom).

- After a call of `TheoryEngine::check`, the SAT solver takes the propagated
  literals, each followed by its Boolean propagation. With sharing, asserting
  a literal that a theory already has prints nothing, but notifies the shared
  terms of its atom. The replay asserts the pending propagated literals in
  order, interleaved with the trace's asserts (the Boolean propagations). A
  round continues the call if facts were asserted, with no conflict and no
  lemma.
- A theory is given a literal once (`markPropagation`), by the SAT solver or
  the shared solver; equalities are compared up to symmetry.

### Results

Replay, random benchmarks with clauses: about 55% identical; UF unchanged
(identical). On longer searches (5,000 to 13,000 events) the first difference
is typically after 60 to 90 rounds. The remaining differences come from node
order:
- the order of `checkSplit`, and its consequences (which pending facts are
  processed);
- the orientation of equalities, which decides the direction of merges in the
  equality engine.

0.27 s for a 13,000-event trace.

### Node order

cvc5 makes some choices by node id, which telos cannot reproduce:
- `checkSplit` takes the classes in a `std::set<Node>`;
- `TheoryEngine::getExplanation` collects the explanation in a
  `std::set<TNode>`;
- the rewriter orients equalities by id (telos approximates "newer on the
  right" by the order in which the equality engine met the terms);
- the arithmetic rewriter orders the monomials of a sum by id
  (`LeafNodeComparator`), which also decides the sign of a normalized
  inequality (its leading coefficient) and the variable an equality is solved
  for.

**`NodeOrder`** (`Telos/Core/Node/NodeOrder.lean`) approximates the ids as
cvc5 creates them:
- the declared constants in order of declaration, then the subterms of the
  input assertions in order of first occurrence (children first, left to
  right), as the parser creates them (`Frontend.inputOrder`). The rewriter
  uses this order during preprocessing (the arithmetic rewriter's `monoLt`:
  the monomials of a sum, so the sign of a normalized inequality and the
  variable an equality is solved for);
- then the nodes that preprocessing creates, in the order its certificate
  creates them (`certNodes`: the result of each step; below an operator, the
  children's nodes, then the rebuilt application), for the engine: its
  rewriting of lemmas and atoms, and the linear solver (`proveOr`, the order of
  the disjuncts of unate lemmas, which falls back to the solver's own order of
  first occurrence for nodes created later; `normalizedVariablePart`; the
  Diophantine solver's order). One run of the preprocessor gives both the
  assertions and this order (`Frontend.preprocessed`);
- a term not in the table comes after those in it, and two such terms are in
  the structural order (`Node.lt`).

cvc5's arithmetic is mixed: its rewriter writes an integral constant of a real
term as an integer, so its `(>= s 2)` is not the parser's (or a pass's)
`(>= s 2.0)`, which telos cannot tell apart. A node is looked up by the node
cvc5's rewriter builds for it (`cvx`), numbered when a step's result or a
rewritten child has an arithmetic shape. So in QF_LRA, where `static-rewrite`
splits `(= s 2.0)` into `(and (<= s 2.0) (>= s 2.0))`, the rewritten
`(>= (- s) -2)` comes before `(>= s 2)`, which the rewriter builds later from
`(>= s 2.0)`; in QF_LIA the split's `(>= s 4)` is already cvc5's node, and
comes before the `(not (>= s 5))` of `(<= s 4)` (both checked on cvc5 with
variants). An input atom the rewriter leaves unchanged keeps its id of the
input (cvc5 builds its node in the first `rewrite` pass, a little later).

It is untrusted: `StaticProc.arithNorm` carries the order, and its proof
(`arithNorm_provesEq`) holds for every order, since sorting is a permutation.
The certificates' own rewrites (`EqProof.rw`) keep the structural order: they
relate two terms through a common normal form. It costs a pass over the input
and one over the preprocessing certificate (35 ms on 2,500-assertion inputs,
of 350 ms), and a hash lookup per comparison.

On the fuzz sets (`fuzz-solve.py --sat`), the events agree with cvc5's on: uf
150/150, lra 149/150, lia 150/150 (from 134), uflra 197/200 (from 166), uflia
199/200 and 195/200 (seeds 1 and 9, from 164 and 165), dtlia 198/200 and
192/200 (seed 9 with size 8, from 186 and 184); dt 141/150 and dt `--bool`
77/100 are unchanged (their differences are not arithmetic). The preprocessor
agrees with cvc5's on 8 more of 300 `fuzz-pp.py --mixed` benchmarks.

### Certified `unsat`

A conflict of the theory of datatypes, and a propagation whose explanation goes
through its internal facts, are certified by the same certificates as UF's
(`EqProof`), with five more steps:
- `valid F cs`: a formula `F` proven by a CPC proof `cs` that Logos's checker
  accepts from the empty state. It is valid (`LogosFacts.checker_sound`).
  CPC's datatypes rules take their conclusion as their argument, so telos
  builds the conclusion it wants, and Logos checks it with one step:
  `dt-cons-eq`, `dt-cons-eq-clash`, `dt-inst`, `dt_split`, `dt-cycle`,
  `dt-collapse-selector`, `dt-collapse-tester`,
  `dt-collapse-tester-singleton`;
- `fromTrue`, `andElim`, `orElim`: Boolean reasoning on such formulas;
- `congAt`: congruence on a term that no asserted literal has (one the theory
  built), whose typing is checked instead.

The theory records how each internal fact was inferred, with its explanation.
The builder (`EqBuild`) proves an edge whose reason is not an input literal
from its inference, and the premises from the engine's paths, down to input
literals:
- unification: `dt-cons-eq`, then `and` elimination;
- selector collapse: congruence, then `dt-collapse-selector`;
- instantiation from a tester: `dt-inst`;
- the split of a datatype with one constructor:
  `dt-collapse-tester-singleton`;
- label exhaustion: `dt_split`, then `or` elimination with the other testers
  false;
- an equality of distinct constructor constants (merged with `false` by the
  engine): `dt-cons-eq-clash`.

And the conflicts:
- clash: `dt-cons-eq-clash`;
- a tester against a constructor: congruence, then `dt-collapse-tester`;
- two testers of a class: the same constructor with both values, or
  different constructors, by `dt-inst` and `dt-collapse-tester`;
- cycle: the term equal to a constructor term in which it occurs, built along
  the cycle by congruence, then `dt-cycle`.

The checker's soundness proof covers the new steps (`check_sound`); the
correctness theorem is unchanged. Not certified: an internal fact that
instantiates a constructor term (it uses a purification skolem), and anything
that needs a lemma, which needs the SAT solver (whose lemmas are certified, see
Stage 6).

Results: on 3,000 random conjunctions, every conflict found by the theory
engine (59) is certified, agrees with cvc5, and its CPC proof is accepted by
Ethos. Most `unsat`s of random conjunctions are decided by preprocessing.
`test/solve/dt-*.smt2` has a clash, a cycle and a tester conflict.

## Stage 6: the SAT solver (in progress: milestones 1 to 4 done)

Without a SAT solver, telos solves conjunctions of literals and replays cvc5's
search. Theories with lemmas (datatypes' splits and forced instantiations) need
one to be complete.

### Decision

- **Port cvc5's MiniSat** (`src/prop/minisat`, cvc5's modified MiniSat) and
  the layer around it, faithfully, so that the search, and so the events, are
  cvc5's.
- **Performance is not a concern yet.** Eventually telos should depend on a
  *verified* CDCL(T) solver in Lean. The port is the first implementation of a
  boundary that such a solver replaces.
- **Fidelity configuration.** With proofs, cvc5's default SAT solver is now
  CaDiCaL (through its IPASIR-UP propagator, `src/prop/cadical`). The fuzzer
  will run cvc5 with `--sat-solver=minisat`, a common option, allowed in safe
  mode. The decision mode is MiniSat's own (`--decision=internal`) for
  QF_UF and QF_UFDT, and cvc5's justification heuristic
  (`--decision=justification`, `src/decision/`) for `ALL`, strings,
  quantifiers and a few combinations: it is the other key module of this
  stage, ported with the SAT solver.

### Modules (cvc5's boundaries)

1. **The CNF stream** (`cnf_stream.cpp`, and `proof_cnf_stream.cpp` for its
   proofs): the Tseitin conversion of assertions and lemmas, which registers
   their atoms (preregistration). Replay already emulates its atom order.
2. **The theory proxy** (`theory_proxy.cpp`): what the SAT solver asks of the
   theories: `theoryCheck`, `theoryPropagate`, `explainPropagation`,
   `enqueueTheoryLiteral` (an assertion), lemmas as new clauses, decisions and
   phases requested by the theories, backtracking. Telos's engine already does
   most of this; replay drives it from a trace.
3. **The CDCL(T) SAT solver interface** (`sat_solver.h`, `CDCLTSatSolver`):
   `newVar`, `addClause` (with removable clauses), `solve`, `value`, push and
   pop, `preferPhase`, with the theory proxy as its callbacks.
4. **MiniSat** (`minisat/core/Solver.cc`, about 2,200 lines, and
   `minisat.cpp`): implements the interface. cvc5's changes to MiniSat are kept:
   theory propagation and conflicts inside `propagate`, lemmas, removable
   clauses, assertion levels, phase preferences, and proof hooks.
5. **The decision engine** (`decision/`, about 1,000 lines:
   `justification_strategy.cpp`, `justify_stack.cpp`, `justify_cache.cpp`,
   `assertion_list.cpp`): the justification heuristic, which chooses decisions
   from the structure of the assertions (the next unjustified literal of the
   next unjustified assertion), with cvc5's options (`stoponly`, its skolem
   policy). The SAT solver asks it for decisions through the theory proxy
   (`getNextDecisionRequest`), before its own.
6. **The propositional engine** (`prop_engine.cpp`): assertions, `solve`, the
   model.

The swap point is (3) against (2). **IPASIR-UP** shapes it: CaDiCaL's
external-propagator interface is what a modern CDCL(T) solver offers, and cvc5's
`cdclt_propagator.cpp` adapts the theory proxy to it:
- `notify_assignment` asserts literals;
- `notify_new_decision_level` and `notify_backtrack` push and pop;
- `cb_propagate` and `cb_add_reason_clause_lit` give propagations and their
  explanations;
- `cb_check_found_model` runs the full check;
- `cb_has_external_clause` and `cb_add_external_clause_lit` give lemmas and
  conflicts;
- `cb_decide` gives the decisions of the theories and of the decision
  engine.

So the theory proxy keeps operations that this adapter can call. A verified
CDCL(T) solver in Lean (or CaDiCaL) then plugs in through a port of that
adapter, without touching the theories.

### Certification

- `sat`: the model check, as now, with the SAT assignment for the Boolean
  variables.
- `unsat`: a refutation of the clauses:
  - the input clauses from the CNF conversion, justified by the CPC steps of
    the proof CNF stream (`cnf_and_pos`, ...), run through Logos's checker;
  - theory lemmas, valid by their CPC steps;
  - theory conflicts, by the certificates (`EqProof`);
  - the SAT search's resolution proof (MiniSat's chains, as cvc5's
    `SatProofManager` gives them), checked by a small verified resolution
    checker (or as LRAT by Lean's verified LRAT checker).

  Until that is in place, an `unsat` from the search answers `unknown`.

### Milestones

1. The SAT solver interface and MiniSat's core, on pure propositional input.
2. The CNF stream and the theory proxy, with the engine: QF_UF and QF_UFDT with
   clauses, the events compared with cvc5's (`--sat-solver=minisat`),
   decisions included. Replay stays for the other configurations.
3. The decision engine (justification): `ALL` and the other logics that use
   it, the events compared with cvc5's (`--sat-solver=minisat`, default
   decision mode).
4. The resolution proof and its verified checker: certified `unsat` with
   lemmas.
5. Later: the IPASIR-UP adapter, and the dependency on a verified CDCL(T)
   solver.

### Status

**Milestones 1 and 2 are done.**

- `Telos/Solver/Sat/` is the SAT layer, term-free (the hygiene check enforces
  that it imports only itself): MiniSat's types, sort and heap (`Basic.lean`),
  and the solver (`Minisat.lean`), generic in its host's monad, which it reaches
  through `TheoryProxy`, the swap point. `--dimacs FILE` runs it alone with no
  theories (`Dimacs.lean`), for `scripts/fuzz-sat.py`, until the SAT path is
  fuzzed through SMT-LIB only.
- `Telos/Solver/Cnf.lean` is the CNF stream (the proof CNF stream's clause
  order). It knows terms and SAT literals, not the SAT solver: it queues its
  requests (`SatOp`, new variables and clauses) for the host to apply in order,
  predicting the variables' indices. That is exact, because it never reads the
  assignment, and during the search MiniSat only queues clauses as lemmas.
- `Telos/Solver/Prop.lean` is the prop engine and the theory proxy:
  - eager preregistration, repeated after a backtrack (`TheoryPreregistrar`);
  - the assigned literals queued until the next check;
  - lemmas and explained conflicts as clauses;
  - context level 1 for `check-sat`, decision levels above it.
- In the engine (`Config.satMode`), lemmas and conflicts go to the CNF stream
  (`flushLemmas`, `satLemma`). `TheoryEngine::check`'s `d_lemmasAdded` and
  `d_outputChannelUsed` are reset per check, and are what `theoryNeedCheck`
  reads. A shared literal that rewrites to `true` is asserted, one that
  rewrites to `false` is a conflict (`CONFLICT_REWRITE_LIT`), as in cvc5's
  `assertToTheory`.
- The front end sends anything that is not a conjunction of literals to the SAT
  solver (`--via-sat` forces it, for fuzzing conjunctions too). A `sat` is
  certified by the model check, as before, with the SAT model's values of the
  Boolean variables. An `unsat` answers `unknown` until milestone 4
  (`runSat_ne_unsat`, used by `solveScript_unsat`).

Results, with `scripts/fuzz-solve.py --sat` (cvc5 with
`--sat-solver=minisat`), on cvc5's preprocessed assertions (`--cvc5-pp`):
- **QF_UF:** the same events as cvc5 on all of 300 benchmarks with nested
  connectives (`--bool`), 287 of them identical as text, and on all of 100
  with clauses. That covers decisions, BCP, conflicts, learned clauses,
  backtracking, restarts and lazy explanations.
- **QF_UFDT:** the same events on about a third. The first differences are
  the datatypes solver's order:
  - which term `checkSplit` splits on first (the node-id order that
    `cvc5-deterministic-order.patch` addresses);
  - a few preregistrations of lemma atoms.

  Datatypes `sat` answers are certified: the model builder builds datatype
  values (cvc5's `TheoryDatatypes::collectModelInfo`, `Telos/Solver/Model.lean`),
  and the evaluator, whose soundness is proved, evaluates constructors, testers
  and selectors (with Logos's functions for selectors applied to the wrong
  constructor). On 816 random QF_UFDT benchmarks, every one of the 522 that
  cvc5 answers `sat` is a certified `sat`, and there are no wrong answers.
  A conjunction on which a theory sends a lemma goes to the SAT solver (the
  engine alone gives up there).
- On telos's own preprocessing, the remaining differences are preprocessing's,
  not the search's.

**Milestone 4 (certified `unsat`) is done.** An
`unsat` of the SAT solver comes with a certificate
(`Telos/Solver/SatProof.lean`), checked, and proved to refute the input
(`verification/TelosProofs/Solver/SatProof.lean`, `Cert.check_sound`; the
front end's `solveScript_unsat`, `TelosProofs/Solver/Frontend.lean`). The
certificate is a clausal proof over literals of terms, not SAT variables:
- **input clauses**: they contain a clause of the CNF translation of an input
  formula, recomputed by `inputClauses` (cvc5's `convertAndAssert`);
- **definitions**: they contain a Tseitin clause of a connective
  (`defClauses`, the CNF stream's `handle*`);
- **theory clauses** (conflicts, and explanations of propagations): they
  contain the negation of each assumption of an equality proof of `false`
  (`EqProof`), built from the clause's literals only, when the clause is made
  (the engine's state is then that of the conflict);
- **lemma clauses**: they contain a clause of the CNF translation of a theory
  lemma `F`, as given to the CNF stream (rewritten and oriented), with an
  `EqProof` of `(F, true)` from no assumptions (`Just.lemma`), so `F` is valid;
- **learned clauses**, and finally the empty clause: each follows from the
  clauses before it by unit propagation (RUP).

The CNF stream and MiniSat are not trusted: the checker recomputes what it
checks. Theory propagations at level 0 that MiniSat never asked to explain are
explained after the search (post hoc: nothing is printed), as their reasons
still hold at level 0.

The datatypes lemmas are proved by `Telos/Solver/DtLemma.lean`, by their CPC
rules: `dt_split` for splits, `skolem_intro` for purification, `dt-inst` for an
instantiation from a tester, and `skolem_intro`, congruence and
`dt-collapse-selector` for the instantiation of a constructor term. An
implication (an instantiation from a tester, a selector collapse sent as a
lemma) is a CPC proof under its hypothesis, closed by `scope`, which
`EqProof.valid` checks with Logos's checker. The SAT solver gets the lemma
rewritten (and oriented as cvc5's node ids would): the `EqProof` step `rw t`,
`(t, rewrite t)` for a well-typed `t`, justified by the rewriter's correctness
(`rewrite_correct`), relates the two when they have the same rewrite. The same
step lets a disequality be proved from the reason of the other orientation
(`proveDiseq`).

On 4,000 random QF_UFDT benchmarks with clauses (`--via-sat`, telos's own
preprocessing), every one of the 946 `unsat`s is certified, as is every `unsat`
of QF_UF. Some theory clauses still have no certificate and are left out, which
these refutations did not need: about 60 conflicts whose explanation goes
through a literal that the SAT solver got by theory propagation, which
`explainAll` replaces by its own explanation, so it is not among the clause's
literals ("a reason is not an assumption"), and a few disequalities with
several reasons. Next: a CPC proof of the refutation for Ethos (`rw` is printed
as the rewriter's CPC proof, `Proof.emitChain`, which fails on its semantic
steps).

**The decision engine (milestone 3) is done** (`Telos/Solver/Decision.lean`):
a port of cvc5's `JustificationStrategy`, with its assertion lists, justify
cache and stack, their context-dependent parts restored at the SAT solver's
pops. The mode is the logic's (`decisionModeOf`, `setDefaultDecisionMode`):
justification for `ALL`, quantifiers, strings and a few combinations; stop-only
(MiniSat decides, the heuristic stops the search once the assertions are
justified) for QF_LRA and QF_AUFLIA; MiniSat's own decisions otherwise (QF_UF,
QF_UFDT, QF_LIA). `--decision=MODE`, or `(set-option :decision MODE)` in the
script, overrides it. The input formulas go to the heuristic before their
conversion (`notifyInputFormulas`), every lemma after its own (conflicts
included, as `(not (and …))`); skolem definitions of term formula removal wait
until an asserted literal has their skolem (`jh-skolem-rlv=ASSERT`,
`SkolemDefManager`), which makes a full check a standard one and asks for
another check. A skolem definition is recognized by its form
(`skolemOfDefinition`), so that it is one also in a script of cvc5's
preprocessed assertions (`--cvc5-pp`).

On cvc5's preprocessed assertions (`--cvc5-pp`), justification agrees with
cvc5 exactly as often as MiniSat's own decisions do: on 200 of 200 QF_UF
benchmarks with nested connectives, 174 of 200 QF_LRA ones, the same on
QF_LIA with clauses; on QF_UFDT, but for 3 with purification skolems of the
datatypes' `ppRewrite` (whose definitions are not recognized). With telos's
own preprocessing, the differences that only justification shows (5 to 7 of
200) come from the order of the children of Boolean equalities, by node id,
which the heuristic follows; the same order, and the order of preregistration,
make about a quarter of the benchmarks with nested connectives differ under
MiniSat's decisions too. Stop-only adds no difference on QF_LRA with `ite`
terms (`--ite`), where skolem definitions become relevant during the search;
without their activation, half the benchmarks would differ.

Not yet:
- decision requests of the theories (none of the ported theories makes any);
- the relevance order of the heuristic (`--jh-rlv-order`, off by default);
- the skolem definitions of lemmas (`ppLemmas` of the theory preprocessor) and
  of the theories' `ppRewrite`s other than term formula removal.

Two Lean pitfalls caused bugs here, worth knowing:
- `if a && !(← x)` runs `x` whatever `a` is: a nested action is lifted before
  the statement;
- `return` inside a `match` arm's `do` returns from the enclosing function.

## Stage 7: linear arithmetic (in progress: milestones 1 to 4 done)

### Scope

With `--safe-mode=safe --produce-proofs`, cvc5's arithmetic is the linear
solver (`src/theory/arith/linear/`) with its defaults: the dual simplex only
(`useFC`, `useSOI` and `useApprox` are off), bound propagation
(`arithPropagationMode=BOTH_PROP`), the congruence manager (arithmetic's own
equality engine: `--arith-eq-solver` is an expert option), and for integers
the Diophantine solver, branch and bound and cuts. Static learning is
preprocessing, already ported. Nonlinear arithmetic (`nl-ext`) comes later;
`nl-cov` is off in safe mode.

The port is faithful, as MiniSat's: the events are compared with cvc5's. The
core is about 13k lines of C++: `theory_arith_private.cpp` (6k),
`constraint.cpp` (2.8k), `linear_equality.cpp` (1.6k), `matrix.h` and
`tableau.cpp` (1.3k), `partial_model.cpp` (0.8k), the simplex (0.6k),
`theory_arith.cpp` (0.7k).

### Milestones

1. **QF_LRA**, the events compared with cvc5's: delta-rationals, the variable
   map, the tableau, the partial model, the constraint database, the error
   set, the dual simplex with cvc5's pivot rules, conflicts and propagations.
   Conjunctions first, then with the SAT solver. A `sat` is certified by the
   model check.
2. **Certified `unsat` by Farkas certificates.** cvc5 explains a conflict by a
   Farkas combination of bounds. Telos checks the combination with a small
   checker proved sound in Lean, not by running Logos's `arith_poly_norm` at
   run time (a statically verified algorithm). It plugs into `EqProof` and
   `SatProof` as the datatypes rules do. The CPC proof for Ethos uses the
   scaled sum of bounds and `arith_poly_norm`.
3. **QF_LIA**: branch and bound, the Diophantine solver, cuts, with certified
   lemmas (splits are valid; cuts are Farkas-like).
4. **Combination with UF and datatypes** (done): care graphs
   and `combineTheories`; UFLRA, UFLIA. Done so far: arithmetic in the central
   equality engine (its shared terms are trigger terms, the equalities of
   their classes are asserted to it, apart from the UF record of what was
   asserted: `markKey`); the care graph (`combineTheories`, at full effort
   when every fact was processed and nothing was sent), of UF only, since
   arithmetic is not parametric: UF's pairs of applications whose arguments
   may be equal, pruned by `getEqualityStatus` (the central engine for shared
   terms, else arithmetic's model), each a `COMBINATION_SPLIT` lemma (cached
   by the builtin theory) whose equality is a SAT literal with the preferred
   phase `true`; `Theory::addSharedTerm` before `markNotified`, which notify
   the trigger terms twice, as cvc5 does; combined models (an arithmetic
   class has the value of a numeral or term in it, or a fresh one). cvc5's
   node ids for the declared constants are their order of declaration
   (`declOrder`). On QF_UFLRA (`fuzz-solve.py --theory uflra`) every answer
   agrees with cvc5's, and the events of 98% of the benchmarks.
   There is no congruence manager: with the central equality engine cvc5
   turns on `arith-eq-solver` (`set_defaults.cpp`, also in safe mode, since
   cvc5 sets it, not the user), which disables it (`d_cmEnabled`).
   Arithmetic's equality literals are asserted to the central engine as well
   as to the linear solver, and equalities that only the bounds imply (`x ≤ y`,
   `y ≤ x`) reach the other theories by the care graph's splits, not by
   propagation. Datatypes' care graph (`TheoryDatatypes::computeCareGraph`)
   is UF's with the default `areCareDisequal`, over its function terms (the
   constructor applications with arguments and the selector applications, by
   operator and type). Its full-effort split waits while `needCheck` holds
   (the output channel used or a lemma added in this `check`, by any
   theory), and arithmetic's lemmas are preregistered before the next
   theory's check. An equality that rewrites to a constant, given to
   arithmetic as a shared (dis)equality, is ignored if true and a black-box
   conflict if false (`constraintFromFactQueue`). Combined models follow the
   model builder: arithmetic applications (not leaves) are evaluated from
   their arguments before the other classes get fresh values, a datatype
   class with selector terms but no constructor term is a constructor
   applied to them (`getInstCons`), and integer and real fields count as
   infinite for fresh datatype values. QF_UFLIA (`--theory uflia`) and
   datatypes with integer fields (`--theory dtlia`): with cvc5's node ids
   approximated (`NodeOrder`, "Node order" in Stage 5), the events of 96–99%
   of the benchmarks agree, and every answer. A fresh datatype value is
   chosen so that it makes no two classes equal that were not, counting the
   classes whose values depend on it (`(icons x (itl l))` for a fresh
   `(itl l)`): before, `m` could get the value of `(icons x (itl l))`
   although they are disequal, and the model check answered `unknown`. cvc5's record of the literals given to the theories
   (`markPropagation`) is keyed by the literal; telos also takes the flipped
   equality as given, while the orientation is approximate.
5. Later: nonlinear arithmetic (`nl-ext`).

### Port notes (cvc5's linear solver, `src/theory/arith/linear/`)

**Options decided by the logic** (`SetDefaults`, `set_defaults.cpp:817-861`):
- `arithHeuristicPivots` is 0 for quantifier-free real arithmetic alone, the
  number of variables plus one for difference logic, and 5 otherwise (QF_LIA,
  mixed logics).
- `arithStandardCheckVarOrderPivots` is 200 for pure quantifier-free
  arithmetic, and -1 otherwise, which makes even standard-effort simplex run
  to completion.
- `arithRewriteEq` is on for pure linear quantifier-free arithmetic.
- Other defaults: `newProp`, `arithPivotThreshold=2`, error selection
  `MINIMUM_AMOUNT`, `arithSimplexCheckPeriod=200`, `arithPropagateMaxLength=16`,
  `arithPropAsLemmaLength=8`, `arithUnateLemmaMode=ALL`, `dioSolverTurns=10`,
  `rrTurns=3`.

**Structure:**
- `TheoryArith` owns `TheoryArithPrivate` through `LinearSolver`.
- Arithmetic's own equality engine is written only by the congruence manager.
- These persist across backtracking: the tableau's basis, the assignments, and
  the round-robin integer variable. Events therefore depend on the whole
  history, not only on the current context.
- These are context dependent: the bounds (revert lists in `ArithVariables`),
  the constraints' proofs, preregistration and assertion order (watches in the
  constraint database), the conflicts, the disequality queue and the learned
  bounds.

**Preregistration** (`setupAtom`, `setupPolynomial`):
- Each atom's constant-free normalized polynomial gets a variable.
- A sum gets a slack variable and a tableau row.
- Arith variables are numbered in order: the polynomial's variables, then the
  slack, in preregistration order.
- The constraint and its negation go into the variable's map, sorted by
  delta-rational value.

**`postCheck`, in order:**
1. learned bounds;
2. conflicts;
3. the simplex (`dualFindModel`): the heuristic pivots, then variable-order
   pivots;
4. unate propagation of the bounds asserted;
5. at full effort, disequality splits, then for integers the Diophantine
   solver, cuts, and branch and bound.

**The simplex's choices:**
- Leaving variable: the error set's heap, smallest violation first, then
  smallest variable.
- Entering variable: by `minBoundAndColLength`, unless the leaving variable
  already left twice in this `findModel` call, in which case by Bland's rule.
- Signals are processed last in, first out.
- Conflicts come from `minimallyWeakConflict` (`ARITH_CONF_SIMPLEX`), with
  Farkas coefficients.

**Propagation** runs after a `sat` relaxation, from the rows of updated
bounds:
- A row of length at most 8 that implies a bound is sent as a lemma
  (`ARITH_ROW_IMPL`); otherwise the bound is propagated.
- **cvc5 skips rows of length 16 or more at random** (`propagateCandidateRow`),
  which a port cannot reproduce.
- At presolve, `ARITH_UNATE` lemmas relate the atoms of each variable.

**Order dependence:**
- The order of variables in monomials is by node id (`VariableNodeCmp`), which
  fixes the arith-variable numbering. With `--cvc5-pp` telos gets cvc5's
  normalized atoms.
- `proveOr` orders a unate lemma's disjuncts by node id.
- The rest follows from the matrix's lists and the dense maps (ported
  exactly).

### Status

`Telos/Solver/Theory/Arith/`:
- `DeltaRational.lean`: `c + k·δ` (`delta_rational.h`);
- `DenseMap.lean`: `DenseMap`, `DenseSet`, `DenseMultiset`
  (`util/dense_map.h`), whose key order, which `remove` changes, decides
  iteration orders;
- `Matrix.lean`: the sparse matrix and the tableau (`matrix.h`,
  `tableau.cpp`), its entries in one array with doubly linked rows and columns,
  new entries at the heads, freed ones reused first in, first out, so that
  traversals are in cvc5's order. `TelosTests/ArithTableau.lean` checks random
  pivots against the original equations.

- `Basic.lean`, `State.lean`: bound counts, constraints, value collections,
  constraint rules, the variables' information; the solver's state as one
  structure (the partial model, the tableau, the constraint database, the
  error set, the simplex's and `TheoryArithPrivate`'s fields), its
  context-dependent lists truncated at a pop with cvc5's cleanups;
- `Poly.lean`: what the solver reads of a normal-form atom (`Comparison`):
  its constraint type, its normalized variable part (which keys its arith
  variable) and its delta-rational bound;
- `Simplex.lean`: the error set, the linear equality module (updates,
  pivots, the rows' bound counts), the Farkas conflict builder
  (`minimallyWeakConflict`), the dual simplex;
- `Solver.lean`: preregistration (`setupAtom`, `setupPolynomial`), the unate
  lemmas of `presolve`, the assertion of facts (`assertionCases`,
  `Assert*`), `postCheck` (learned bounds, the simplex, unate propagation,
  disequality splits), row bound propagation (`propagateCandidatesNew`, its
  row-implication lemmas), the propagations, and the explanations.

The engine runs arithmetic through the SAT solver (its unate lemmas need it),
and gives it its facts, checks, propagations and explanations as cvc5's
`TheoryEngine` does; each conflict of arithmetic is an event and a clause.

The front end reads a numeral in a position of type `Real` as a real
(`cvc5Numerals`), as SMT-LIB does: CPC types it as an integer, so `(>= x 1)`
for a real `x` is ill typed, and inside a connective Logos's parser makes it
`Stuck`. Reading cvc5's output (`--no-preprocess`, replay), it also reads
cvc5's constants as the literals they denote: `(- 1)`, and `(/ a b)` for a
rational. The comparator writes both sides' constants alike.

**`sat` is certified** by the model check, with the arithmetic solver's values
of its variables (`modelValues`: `collectModelValues`, with `δ` from
`deltaValueForTotalOrder`). The model's evaluator has integers and rationals,
and evaluates `+`, `*` (with their typed neutral elements, as `Node.toEo`
translates them), `-`, unary `-`, the comparisons and `to_real` as Logos
does; its soundness proof covers them (`combine_sound_in`, `ev_sound`,
`verification/TelosProofs/Solver/Model.lean`).

**`unsat` is certified** (milestone 2) by the certificate of the SAT solver's
refutation, in which a conflict of arithmetic, the clause of one of its
lemmas, and the explanation of one of its propagations are justified by a
refutation of literals (`SatProof.Just.arith`, `Telos/Solver/LinCert.lean`):
the conflict's literals, or the negations of the clause's. A refutation is a
Farkas combination of the literals (each bounds the difference of its sides,
by `≥ 0`, `> 0` or `= 0`), checked by summing the scaled differences and
letting the verified rewriter rewrite the sum's comparison with `0` to
`false`; a split of a disequality `(not (= a b))` into `(< a b)` and
`(> a b)`; or a cut on a literal. The solver builds the certificates from
its constraints' proofs, as cvc5's proof production reads them
(`Telos/Solver/Theory/Arith/Cert.lean`): an explanation's assumptions are
its leaves, a Farkas rule is a combination with cvc5's coefficients (scaled
to each literal's sides), a trichotomy rule a split, and a derived
antecedent a cut on its literal whose other side refutes the constraint's
negation. Nothing there is trusted. `LinCert.check` is proved sound
(`verification/TelosProofs/Solver/LinCert.lean`, `linCert_sound` and
`arith_sat` in `.../SatProof.lean`), from the rewriter's correctness and one
more Logos fact (a real term evaluates to a real, `LogosFacts.eval_real`).
The CPC proof for Ethos is not done (as for the SAT solver's refutations in
general).

Results (`scripts/fuzz-solve.py --theory lra --sat --cvc5-pp`, cvc5 with
`--decision=internal` then, before the decision engine of Stage 6): the input events agree on all of 300
random conjunctions and 300 with clauses. All the events (lemmas, conflicts,
propagations, backtracking) and the answer agree on 283 of 300 larger
conjunctions (96 `unsat`) and 291 of 300 with clauses; with telos's own
preprocessing, on 272 of 300 conjunctions and 274 to 297 of 300 with
clauses. Every answer agrees, the `sat`s certified by the model check and
every `unsat` by its certificate (over 500 `unsat`s in all). The
differences are the order of the two disjuncts of unate lemmas, by node id
(`proveOr`), which telos approximates by first occurrence in the input; cvc5's
ids come from its preprocessing, which `--cvc5-pp` does not show.
`test/solve/sat-lra-*.smt2` have row implications, unate lemmas and simplex
conflicts; `sat-lra-unsat*` are certified `unsat`s.

In QF_LRA, disequalities do not reach the solver (`arithRewriteEq` makes
equalities pairs of inequalities), so the certificates of the trichotomy
rules and of the disequality splits (`ARITH_SPLIT_DEQ`) are not exercised
yet: they come with the logics that combine arithmetic with other theories
(milestone 4). The certificates of propagations are, by rows longer than
`arithPropAsLemmaLength`, but those are rare in the random benchmarks.

**QF_LIA** (milestone 3). The options that the logic decides are cvc5's
(`Arith.Options.ofLogic`, from `SetDefaults`): for QF_LIA, 5 heuristic pivots;
200 variable-order pivots for pure quantifier-free arithmetic;
`arithRewriteEq`. At full effort, when an integer input variable has a value
that is not integral (`hasIntegerModel`, round robin from
`d_nextIntegerCheckVar`):
- the **Diophantine solver** (`Telos/Solver/Theory/Arith/Dio.lean`, a port of
  `dio_solver.cpp` and its `DioLinearForm`s, with GMP's `mpz_gcdext` choice of
  Bézout coefficients, which the cuts depend on) gets the equations of the
  integer variables whose bounds became equal (`callDioSolver`), and a
  conflict is a black-box conflict (`ARITH_BLACK_BOX`); then, if there was
  work since the last cut and the round robin of resources allows
  (`getDioCuttingResource`: 10 turns of cuts, 3 of branches), the equations
  of the variables at a bound are added in a speculative scope
  (`dioCutting`), whose pop cvc5 prints, and a plane is a cut
  (`ARITH_DIO_CUT`);
- otherwise **branch and bound** (`branchIntegerVariable` with `--arith-brab`):
  `(or (= x n) (or (<= x (- n 1)) (>= x (+ n 1))))` for the nearest integer
  `n`, its equality preprocessed (`ppRewriteEq`) and given a SAT literal at
  once (`ensureLiteral`, which preregisters its atoms) with the preferred phase
  `true` (`preferPhase`, MiniSat's `freezePolarity`, and the `phase` event).
  The arithmetic's lemmas go through the inference manager's cache of sent
  lemmas (`cacheLemma`), so a branch already sent moves the round robin on.

The engine runs the outputs from an ensured literal on after the check
(`flushArithDeferred`), since the CNF stream is defined after the theories.

Their certificates: `LinCert` reads an integer literal's difference through
`to_real`, and strengthens a strict integer bound `d > 0` to `d - 1 ≥ 0`
(which certifies tightening, `intTighten`, and the branches); a branch's
equality is a conjunction, refuted by cases (`LinCert.cases`); a conflict of
the Diophantine solver combines the input equations with the solver's proof
coefficients into `g Q + k = 0`, with `g` not dividing `k`, and is refuted by
a cut on `Q ≥ ⌈-k/g⌉` (`dioConflictCert`).

Results (`--theory lia --sat`, 300 benchmarks each): the events and the
answer agree on 264 of 300 conjunctions, 240 and 258 of larger ones, 175 and
152 with clauses; with `--cvc5-pp`, 245 and 244, and 198 with clauses. Every
answer agrees (over 500 certified `unsat`s, the rest certified `sat`s). The
differences are the order of the disjuncts of unate lemmas, which is more
frequent than in QF_LRA: an integer atom is normalized (tightened) into a new
node, whose id cvc5 gives in the order its preprocessing makes them (an
equality's `(>= s k)` before its `(>= s (+ k 1))`, say), which telos's order
of first occurrence does not follow. One benchmark of branch and bound that
does not converge in cvc5 either (655,000 events in 29 seconds) times out.
`test/solve/sat-lia-*.smt2` cover branches, cuts and the Diophantine
solver's conflicts.

**`ite` terms** (`--ite`): term formula removal's skolems and their
definitions, `(ite c (= k t₁) (= k t₂))`, whose equalities reach the solver as
equalities (they are made after `arithRewriteEq`'s static rewrite). Three
things matter for fidelity there: the engine leaves arithmetic equalities as
the rewriter orients them (by their normal form, not by node id, unlike UF's);
a lemma of the solver goes to the CNF stream as soon as a fact made it (a
disequality's split), so that its atoms are preregistered before the check goes
on, as cvc5's `TheoryEngine::lemma` does; and the Diophantine solver orders two
skolems by node id (approximated by first occurrence), as `VarList::cmp` does.
Certificates use the rewritten lemma's literals, and a disequality split may
be of integers. On 200 benchmarks each (`--sat`), with `NodeOrder`, QF_LRA
with `ite` terms agrees with cvc5 on 164 (139 with clauses) and QF_LIA on 158,
every `unsat` certified. Most of the rest is the order of the disjuncts of the
unate lemmas of a split equality between a purification skolem and a constant
(`(= k 0)`): cvc5's `(>= k 0)` comes before its `(>= (- k) 0)`, unlike for
`(= (+ x y) 2)`, which `NodeOrder` does not explain yet; and the orientation of
such equalities (`(= 0 k)` where cvc5 has `(= k 0)`).

Not yet:
- at a conflict at decision level 0, cvc5's MiniSat finalizes its proof
  (`SatProofManager::finalizeProof`), which explains the theory propagations
  the refutation uses, with `explain` events; telos explains them after the
  fact, silently (`explainLevelZero`). An arithmetic propagation of a long
  row that a level-0 refutation uses shows the difference;
- the random skipping of long rows in propagation;
- the Diophantine solver's decomposition lemmas (`exportDioDecompositions` is
  off) and restarts after `maxCutsInContext` (65535) cuts.

## Stage 8: sets (in progress)

`Telos/Solver/Theory/Sets.lean` and `SetsState.lean` port cvc5's
`TheorySetsPrivate` with its `SolverState`, `TermRegistry` and inference manager,
in safe mode: no cardinality (`setsCardExp`), no relations (`relsExp`), no
universe or complement (`setsExp`), no proxy lemmas. `set.map`, `set.filter`,
`set.fold` and `set.choose` are not ported.

### Design

- **State in the equality engine**, as for datatypes (`EqualityEngine.sets`): the
  theory reacts to `eqNotifyNewClass` (a singleton or the empty set is its
  class's singleton), `eqNotifyMerge` (singletons, `SETS_SINGLETON_EQ` or
  `SETS_EQ_CONFLICT`; members, `SETS_EQ_MEM` or `SETS_EQ_MEM_CONFLICT`) and
  `eqNotifyDisequal`, which the engine now notifies (cvc5 notifies before the
  disequality is asserted). The handlers' facts are asserted to the engine
  while it propagates, and merged by that propagation.
- **Context:** the singleton of a class (`CDO`), the number of valid members
  (`d_members`) and the disequalities (`d_deq`, a `CDHashMap` iterated in
  insertion order) are on a trail; the processed disequalities, the proxies and
  the lemma cache are on the user context; the index of a check
  (`SolverState::reset`) is rebuilt at each full check.
- **The check runs in the theory engine's monad** (`Sets.Ops`, `setsPostCheck`):
  cvc5 preregisters a lemma's atoms when it is sent, and the proxies'
  lemmas (`SETS_PROXY`, `SETS_PROXY_SINGLETON`) are sent in the middle of
  `checkBasic`. In safe mode the strategy is reset, `checkBasic` (registration,
  downward and upward closure), and, if nothing was sent,
  `checkDisequalities` (`SETS_DEQ`, with the skolem `@sets_deq_diff`).
- **Every inference of the check is a lemma** (`assertInference` with
  `inferType` 0); only the notifications assert internal facts.
- **Relevant terms** (`collectAssertedTerms`): the subterms of the theory's
  facts and its shared terms.
- `std::map<Node, _>` iterations (members, the binary-operator index) are sorted
  by the engine's node order (`EE.ageLt`).

Changes outside the theory:
- The equality engine's congruence now covers applications of builtin kinds
  (`set.member`, `set.union`, …), with an internal operator node per kind
  (`kindOperator`, cvc5's `getOperator()`).
- The sets, Boolean and UF rewriters orient equalities and order the arguments
  of `set.union` and `set.inter` by the node order (`NodeOrder`), as the
  arithmetic rewriter does; set equalities in lemmas are not re-oriented by
  `orientEqs`. A lemma's own nodes are numbered before its rewrite
  (`NodeOrder.withLocal`, created before the nodes the rewrite makes). Fuzzing
  the preprocessor (`fuzz-pp.py`, 200 each, identical to cvc5): uf 176 to 193,
  mixed 81 to 93, sets 96 to 121, datatypes 156 to 158; `fuzz-solve.py`: dt
  141 to 143, dt `--bool` 77 to 84, the others unchanged.
- Sets go to the SAT solver (`useSat`), and empty sets print their sort names.

### Models

A set value is `MVal.sempty T` (the empty set of element type `T`) or
`MVal.sins e s` (`s` with `e`): plain constructors, so that `MVal` keeps its
derived instances. Its Logos value is the empty map updated to `true` at each
element in turn, which is canonical (`toVal_props`, `SetMap`); an ill-typed set
is `NotValue`. Values are compared as Logos compares them, `MVal.veq` (sets by
their elements, the rest structurally), in `=`, `distinct` and the tables of
functions, and `veq_iff` proves it is equality of the Logos values (by map
extensionality, `map_ext_of_lookup_eq`). The evaluator computes `set.singleton`,
`set.union`, `set.inter`, `set.minus`, `set.member` and the empty set
(`Model.combine`), each proved against Logos's operation (`union_sound`, ...,
from Logos's lookup lemmas). Nothing applies to an ill-typed set (Logos's
application of anything to `NotValue` is `NotValue`). The builder gives a class
of sets the values of its members' classes (`collectModelValues`, from the
membership atoms that are true). Logos's map and set lemmas are new fields of
`LogosFacts`, proved in `TelosFull/Main.lean`; `solve_sat_correct` still rests
on the standard axioms only.

### Certificates

- **Lemmas** (`Telos/Solver/SetsLemma.lean`, `SetsLemma.prove`, an `EqProof` of
  `(lem, true)` per inference): the proxies by `skolem_intro` (and, for a
  singleton, congruence, `sets-member-singleton` and the rewriter); the upward
  closure by congruence with the proxy's definition, one step of
  `sets-union-member`, `sets-inter-member` or `sets-minus-member`, the
  memberships of the element decided by the literals of the explanation (or by
  congruence through its equalities, `atomProof`), then the rewriter; the
  downward closure by the membership in the set of the explanation and the
  rewrite in the node order (`EqProof.rwAt`, a new step: `t` and its rewrite in
  an order `o`, sound by `rewriteWith_sound` for any order); `SETS_DEQ` by
  `sets_ext` under the assumption of the disequality, closed by `scope`.
- **Internal facts** in the equality engine's explanations (`EE.proveFact`):
  `SETS_SINGLETON_EQ` (`x` is in `{x}`, so in `{y}`, which rewrites to
  `(= x y)`), `SETS_MEM_EQ` and `SETS_EQ_MEM` (a member of a set equal to `{e}`
  is `e`), by congruence and the rewriter.
- **Conflicts** (`EE.conflictOfSets`, `Pending.sets`): a membership true of a set
  equal to one in which the rewriter decides it false (`SETS_EQ_CONFLICT`,
  `SETS_MEM_EQ_CONFLICT`, `SETS_EQ_MEM_CONFLICT`, and `SETS_DOWN_CLOSURE` when the
  closure rewrites to `false`).

Every certificate is checked when it is made (`EqProof.check`, and Logos's
checker for its CPC steps); `solve_unsat_correct` rests on the standard axioms
only.

### Results

`fuzz-solve.py --sat --theory sets`, events and answers both as cvc5's: seed 1
(100) 78, seed 2 (200) 158, seed 3 with clauses (200) 129, seed 4 with nested
connectives (100) 46, with no answer that differs. On 300 more random
benchmarks, telos answers all 213 `sat` and all 87 `unsat`, as cvc5. The event
differences are mostly SAT decisions after a lemma, and the order of
preprocessed equalities (the node order of preprocessing). Recorded tests:
`test/solve/sat-sets-*`.

### To do

- The care graph for sets of sets (`SETS_CG_SPLIT`), `set.choose`.
- The remaining event differences.

## Stage 9: strings (in progress: stage 1, word equations with lengths)

cvc5's theory of strings (`src/theory/strings/`, about 29k lines with its
rewriter, of which telos has the rewriter and the preprocessing reductions) in
safe mode, where it is mostly enabled: lazy preprocessing of extended functions
(`stringLazyPreproc`), the eager solver (`stringEagerSolver`), eager evaluation
of applications to constants in the equality engine (`stringEagerEval`),
model-based reduction at last-call effort (`stringModelBasedReduction`).
Lengths are integer terms shared with arithmetic, so strings come with linear
arithmetic (QF_SLIA) and theory combination.

The strategy (`strategy.cpp`), at full effort: `checkInit`, the constant
classes, the evaluation of extended functions, cycles, flat forms, the eager
reductions and memberships, the normal forms of equalities (propagation, then
equalities), the evaluation again, the normal forms of disequalities, codes,
the lengths of classes, sequence arrays, the reductions of extended functions,
memberships, cardinality; at last call, evaluation, reductions and memberships
again.

Stages, each with its fuzz generator, events, models and certificates:
1. **Word equations with lengths**: `str.++`, `str.len`, constants, equalities
   and disequalities of strings. The equality engine's evaluation of
   interpreted applications to constants (`addFunctionKind` with eager
   evaluation, and the constant edges in the proof builder); the term registry
   (`STRINGS_REGISTER_TERM`, `STRINGS_REGISTER_TERM_ATOMIC`, proxy variables),
   the solver state and `EqcInfo`, the eager solver, the inference manager and
   skolem cache; the base solver (`checkInit`, constant classes, cardinality)
   and the core solver (cycles, flat forms, normal forms of equalities and
   disequalities, lengths of classes).
2. **Extended functions**: `str.substr`, `str.at`, `str.contains`, `str.indexof`,
   `str.replace`, `str.prefixof`, `str.suffixof`, `str.to_int`, `str.from_int`,
   `str.<`, `str.<=`, codes (`extf_solver.cpp`, `strings_entail.cpp`): eager
   evaluation, lazy reductions, model-based reduction at last call.
3. **Regular expressions** (`regexp_solver.cpp`, `regexp_operation.cpp`): the
   unfolding of memberships, intersection and inclusion.
4. **Sequences**: `seq.unit`, `seq.nth`, `seq.update` (`array_solver.cpp`).

**Status of stage 1.** Ported (`Telos/Solver/Theory/Strings.lean`, the term
registry and the eager solver; `StringsSolver.lean`, the full-effort check;
`StringsState.lean`):
- preregistration and registration, with phases, the trigger predicates of
  atoms without a SAT value, and the preregistration queue of the theory
  engine (a lemma sent during a preregistration has its atoms preregistered
  after it);
- the eager solver (constant prefixes and suffixes, arithmetic bounds, pending
  merge conflicts);
- the inference manager: conflicts, facts (asserted with the conjunction of
  their premises as the reason, after registering their terms), lemmas (their
  premises explained by the equality engine but those of `noExplain`;
  skolems registered and phases preferred when sent), splits;
  `stringInferSym`;
- the base solver: `checkInit` (congruence modulo empty components,
  `STRINGS_I_NORM`, `STRINGS_I_NORM_S`, the oldest variable of a class) and
  the constant classes (`STRINGS_I_CONST_MERGE`, `STRINGS_I_CONST_CONFLICT`,
  `STRINGS_I_CYCLE_CONFLICT`);
- the core solver: cycles (`STRINGS_I_CYCLE`, `STRINGS_I_CYCLE_E`), flat forms
  (`STRINGS_F_*`), normal forms (`STRINGS_NORMAL_FORM`, `STRINGS_N_*`, the
  possible inferences `STRINGS_LEN_SPLIT`, `STRINGS_LEN_SPLIT_EMP`,
  `STRINGS_INFER_EMP`, `STRINGS_SSPLIT_CST(_PROP)`, `STRINGS_SSPLIT_VAR(_PROP)`
  ranked as `pickInferInfo` does), disequalities (`STRINGS_DEQ_*`) and length
  normalization (`STRINGS_LEN_NORM`); the skolems as purification skolems of
  their terms (`SkolemCache::normalizeStringSkolem`), each recorded when
  created (a hidden event), so that skolems are numbered as cvc5 numbers them;
- models: a string class is its constant, or, if atomic (its normal form is
  one non-constant component), a string of the arithmetic value of its length
  of its own, or else the concatenation of its normal form's components'
  values; `MVal.str`, with `str.++` and `str.len`, in the model evaluator and
  its soundness proof (`verification/TelosProofs/Solver/Model.lean`; invalid
  characters are clamped in the Logos value, and a literal with one is not
  evaluated).

Not yet, and so the check is incomplete (a `sat` answer is then `unknown`):
looping word equations (`processLoop` needs regular expressions, stage 3),
extended functions and regular expressions (any relevant term of a later
stage). Approximated: `stringCheckEntailLen`'s arithmetic entailment (by the
rewriter only); the cardinality of the alphabet is not checked (it only
matters for more than 196608 classes of one length).

Certificates (an `unsat` that needs an uncertified step is `unknown`):
- the lemmas (`Telos/Solver/StringsLemma.lean`): `STRINGS_REGISTER_TERM`
  (`skolem_intro`, congruence and the rewriter, as cvc5's
  `MACRO_SR_PRED_INTRO`), `STRINGS_REGISTER_TERM_ATOMIC` (`string_length_pos`;
  the lemmas of the skolems of length at least one, or one, have no proof, as
  in cvc5), the splits on a literal (the rewriter), and the core inferences
  sent as lemmas;
- the core inferences, as lemmas, internal facts (on the paths of the proof
  builder, `EqBuild.proveFact`) and conflicts (`EE.conflictOfStrings`, from
  the premises before their explanation): `Telos/Solver/StringsCore.lean`, a
  port of `InferProofCons` for them. The main equality, with the other
  equalities substituted and rewritten, then `concat_eq`, the constants at the
  heads split as the rule needs, and the rule (`concat_csplit`,
  `concat_cprop`, `concat_split`, `concat_lprop`, `concat_unify`), its length
  premise from the length constraint (or `string_length_non_empty`); its
  conclusion is related to the solver's (purification skolems of terms with
  the same rewrite are equal). The other inferences (the base solver's, the
  prefix conflicts) by substitution and rewriting alone. Each conclusion is
  read back from Logos, and the proof is checked when it is made;
- in the proof builder, the merges of applications of constant arguments with
  their values (eager evaluation), and of distinct values (the rewriter).

Theory combination, for all theories: the explanation of a conflict or a
propagation of the SAT solver goes through the literals the other theories
propagated (`explainAllSteps`); each step is a clause of the certificate with
its own justification (the linear solver's certificate of its explanation, or
the proof builder's), and the clause of the conflict follows from them by unit
propagation (it is put first among the learned clauses). A literal is
explained by the theory that propagated it (`d_propagationMap`: the shared
solver's literals asserted to arithmetic are the equality engine's, and a SAT
propagation is explained by its propagator), which fixed explanations that
dropped such literals (and so conflict clauses that did not follow). The
clause of an arithmetic lemma that the engine rewrites (oriented equalities)
follows from the lemma's literals as the certificate has them, by their
rewrites.

Testing: `fuzz-solve.py --theory strings` (QF_SLIA word equations with
lengths). With the SAT solver, 100 benchmarks: 93 the same events as cvc5
(seed 1; 94 with seed 2). The others: nodes cvc5 creates in its entailment
checks during preprocessing (such as the length of a variable, which then
orders a sum of lengths), the orientation of some inequalities, a few
`explain` events; cvc5 times out on 1 (a looping word equation, on which
telos answers `unknown`). The length-based unification
`rewriteViaStrEqLenUnifyPrefix` is ported and certified
(`Telos/Preprocess/Theory/StringsLenUnify.lean`); `rewriteViaStrEqLenUnify` is
not. cvc5's node ids, as the engine approximates them (`NodeOrder`): each
preprocessing pass sees the nodes the passes before it created
(`Pipeline.order`); the arithmetic rewriter numbers the nodes of the term it
rewrites that the order lacks, in their order of occurrence
(`NodeOrder.extend`); the solvers' constants `0` to `8` come after the first
assertion (cvc5 builds its theories when it processes it); shared equalities
between terms of the input or of preprocessing are oriented by these ids
(`EE.ageLt`), and with strings an equality and its flip are distinct facts.
On 300 larger benchmarks (seed 11, half with disjunctions), every answer
agrees with cvc5's and every `unsat` is certified (the prefix conflicts by
`rewriteStrEqualityExt`'s CPC proof).

A literal the shared solver asserted to arithmetic is explained by the
equality engine, even if it became a SAT literal after (cvc5's
`d_propagationMap` keeps its first sender); taking it as a SAT literal gave
reasons assigned after the literal they explain, which broke the SAT solver's
conflict analysis (an index out of bounds, and a refutation of a satisfiable
benchmark that the certificate rejected). One that the SAT solver asserted to
the equality engine is its own explanation there.

Not yet: the deep chains of skolems of some splits are slow (a benchmark that
cvc5 solves in a second times out; the terms are trees whose size doubles with
each skolem, though shared in memory).

## Order of work (all stages)

1. **Equality engine.** Port `theory/uf/equality_engine.cpp` (about 3k lines)
   faithfully, because everything in central mode goes through it:
   - the term table and the congruence (use) lists;
   - the representative choice, including constants and the class-size rule;
   - the pending-merge queue order;
   - trigger terms and predicates;
   - the proof forest and `explain`.

   It is fidelity here that makes conflicts "exact" rather than "same literals".
   Test it in replay on QF_UF conjunctions.
2. **UF** (`theory_uf.cpp`, about 740 lines). It is mostly the EE. Cardinality
   and higher order are disabled by safe mode.
3. **The theory engine skeleton:**
   - `TheoryEngine` dispatch (`assertToTheory`, `check` order by theory id);
   - `TheoryInferenceManager` (about 600 lines);
   - `EqEngineManagerCentral` (about 330 lines).

   With one EE there is no combination yet among the theories in the central EE.
4. **A second theory that lives in the central EE:**
   - *arrays:* small, with read-over-write lemmas;
   - *datatypes:* splits, which need replay.
5. **Arithmetic** (linear simplex) and **theory combination** (care graphs,
   `combination_care_graph.cpp`, the shared solver). Arithmetic is not in the
   central EE, so this is where combination becomes necessary.
6. **Strings and sets,** which are heavy on lemmas and use replay throughout.
7. **The SAT solver.** It is needed for BV, which safe mode bit-blasts.

## Setup checklist

- [x] cvc5 patch with `-o theory-events` and `-o theory-events-ee`
      (`cvc5-theory-events.patch`; see [Events](#events)).
- [x] A generator of **conjunctions of literals** that survive preprocessing
      (QF_UF, in `scripts/fuzz-solve.py`).
- [x] `Telos/Solver/Event.lean`: the event type and its printer. The parser of
      cvc5's traces is in `scripts/fuzz-solve.py`.
- [x] `Telos/Solver/EqualityEngine.lean`: the EE port (backtracking still to do).
- [x] `scripts/fuzz-solve.py`: run both sides and compare by rounds, with
      "exact" and "same literals" agreement.
- [x] CI: a small corpus of recorded cvc5 traces, replayed by telos and compared,
      so that CI doesn't need cvc5.

## Open questions

- **Can the trace be made order-deterministic in cvc5?** For example, sort
  within a round before printing. That would make the comparison exact, but it
  hides real ordering differences that later affect search.
- **Is the EE-notification level enough as input for non-UF theories in central
  mode?** Or do we also need `eqNotifyNewClass` and the trigger notifications?
- **How should skolems introduced during solving be named?** For example, the
  datatype selector purifications and string skolems. The `-o post-asserts`
  conventions may need extending.
