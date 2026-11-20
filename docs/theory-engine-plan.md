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

The trace is split into **inputs**, which the theory engine and SAT side hand
to a theory, and **outputs**, which a theory produces through its output channel,
its inference manager, or the central EE. Each event names the theory and, for
outputs, the `InferenceId`.

| Kind | Event | cvc5 location |
|---|---|---|
| input | `(prereg T t)`: register a term or atom | `TheoryEngine::preRegister` |
| input | `(assert T lit)`: a literal given to theory T | `TheoryEngine::assertToTheory` |
| input | `(check T effort)`: start of a `check` call (standard, full, last-call) | `TheoryEngine::check` |
| input | `(push k)` / `(pop k)`: SAT context level | context level changes in `TheoryEngine` |
| input | `(merge T t₁ t₂)` / `(diseq T t₁ t₂)`: central-EE notifications to T | `EqEngineManagerCentral::CentralNotifyClass` |
| output | `(fact T id lit)`: an internal fact asserted to the EE | `TheoryInferenceManager::processInternalFact` (already `Trace("im")`) |
| output | `(lemma T id φ props)` | `TheoryInferenceManager::trustedLemma` (already `Trace("im")`) |
| output | `(conflict T id φ)` | `TheoryInferenceManager::trustedConflict` (already `Trace("im")`) |
| output | `(propagate T lit)` | `TheoryInferenceManager::propagateLit` |
| output | `(phase T lit pol)`, decision-strategy literals | `preferPhase`, `DecisionManager` |
| output | `(incomplete T id)` | `setModelUnsound` / `setRefutationUnsound` |

There is also an optional second level, EE internals: `addTerm`, each merge
with its reason, and each `explain` with its result. That level is verbose, and
is only for finding where the two sides first diverge.

### The cvc5 side

- **Use an output tag, not `Trace`.** Our cvc5 build has tracing off
  (`--show-config`: tracing no), like any release build. A new output tag,
  `-o theory-events`, works in release builds and costs nothing when it is off,
  like `-o lemmas` (`prop/theory_proxy.cpp`).
- **Print terms with the same printer and settings as `-o post-asserts`,** so
  the comparator reuses `fuzz-pp.py`'s normalization (alpha-renaming,
  definitions, skolem names).
- **This is a small cvc5 patch.** It touches about six hook points, mostly next
  to the existing `Trace("im")` lines. It could go upstream as a debugging aid,
  in the same spirit as `-o post-asserts`; track it in `upstream-requests.md`.

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

## Order of work

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

- [ ] cvc5 branch with `-o theory-events` (hooks listed under [Events](#events)).
- [ ] A generator mode in `scripts/fuzz.py` / `fuzz-pp.py` for **conjunctions of
      literals** (QF_UF first). Feed both tools the same post-preprocessing
      assertions: telos's preprocessor already matches cvc5's, or replay cvc5's
      own `prereg`/`assert` events.
- [ ] `Telos/Solver/Event.lean`: the event type, a printer, and a parser for
      cvc5's trace.
- [ ] `Telos/Solver/EqualityEngine.lean`: the EE port, with backtracking.
- [ ] `scripts/fuzz-solve.py`: run both sides and compare by rounds, with
      "exact" and "same literals" agreement.
- [ ] CI: a small corpus of recorded cvc5 traces, replayed by telos and compared,
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
