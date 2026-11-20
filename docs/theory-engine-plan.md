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

The CPC proof is emitted afterwards from the EE's proof forest, which uses
`trans`, `cong`, `symm`, `true_intro`/`false_intro` and so on, as cvc5's
`ProofEqEngine` does, and through `Proof.emitChainWith`. As for preprocessing,
results are the same with and without proofs.

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
