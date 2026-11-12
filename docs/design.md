# Design: a verified SMT rewriter

telos is a port of cvc5's rewriter to Lean 4, with a proof that every rewrite
preserves equivalence. This document describes the architecture and the plan.
`solver-plan.md` holds the earlier, broader plan for a full solver; its notes on
Logos still apply.

## Goals

1. **Faithful to cvc5.** The data structures (`Node`, `Kind`, `TypeNode`) and the
   rewriter structure (`TheoryRewriter`, `RewriteResponse`, pre/post rewrites)
   mirror cvc5's, with cvc5's names. A cvc5 rewrite should port by transcription.
2. **Verified.** `Telos.rewrite_correct` proves that the rewriter preserves
   equivalence. No `sorry`, no new axioms (`TRUSTED.md`).
3. **Semantics shared with CPC.** "Equivalent" is defined through Logos, so a
   rewrite proven correct here is one that a CPC proof step could justify.

Non-goals for now: matching cvc5's speed, termination proofs (fuel is used), and
emitting CPC proofs (possible later, see Roadmap).

## Architecture

```
Node ──toEo──▶ Eo.Term ──__eo_to_smt──▶ SmtTerm ──__smtx_model_eval──▶ SmtValue
 (telos)        (Logos)                  (Logos)                         (Logos)
```

### `Node` (`Telos/Node/`)

- `Kind`: cvc5's kind names (`EQUAL`, `NOT`, `AND`, …, `CONST_BOOLEAN`, …), and
  `Kind.theoryId` (cvc5's `kindToTheoryId`).
- `TypeNode`: Bool, Int, Real, String, RegLan, `BitVec w`, arrays, sequences,
  sets, function types (curried, as in Logos; `mkFunctionType`/`getArgTypes` give
  cvc5's flat view) and uninterpreted sorts (numbered, as in Logos). Datatypes
  and tuples come later.
- `Const`: constant payloads (cvc5's `getConst<T>()`).
- `Node` and `Op` (mutual), following cvc5's metakinds:

  | cvc5 metakind                  | `Node`                                |
  |--------------------------------|---------------------------------------|
  | `CONSTANT` (`CONST_*`)         | `const c`                             |
  | `VARIABLE`                     | `var name type`                       |
  | `VARIABLE` (`BOUND_VARIABLE`)  | `boundVar name type`                  |
  | `OPERATOR`                     | `app (.kind k) children`              |
  | `PARAMETERIZED`, indexed       | `app (.indexed k indices) children`   |
  | `PARAMETERIZED`, term operator | `app (.node k f) children` (`APPLY_UF`) |

  Binders follow cvc5: `FORALL` has children `[BOUND_VAR_LIST(x₁ … xₙ), body]`,
  plus an optional `INST_PATTERN_LIST`. New theories add `Kind`s and `toEo`
  cases, not `Node` constructors.

Numeric payloads (bit-vector widths and values, operator indices) are `Int`, the
type Logos uses, so `toEo` copies them unchanged. Out-of-range values are not
excluded by the datatype but rejected by `Node.WellTyped`. (cvc5 itself uses an
unsigned width and an arbitrary-precision value.)

Variables are identified by name and type, as in Logos. cvc5 identifies them by
node id, so ported code that creates fresh variables must choose fresh names.

`Node` is a plain tree with structural equality, not hash-consed through a
`NodeManager`. Hash-consing would tie every theorem to invariants of a global
table. Speed will come from a cached hash, physical sharing (`ShareCommon`) and a
rewrite cache keyed on the node. A table-backed `NodeManager` can be added
underneath later without changing the specification.

Equality is structural (`Telos/Node/DecEq.lean`, written by hand because Lean
cannot derive it for nested mutual inductives).

### Semantics (`Telos/Node/ToEo.lean`, `verification/TelosProofs/Spec.lean`)

- `Node.toEo` translates a node to a Logos term, the way cvc5 prints it in CPC and
  Ethos elaborates it. Each operator has an `AppShape`, given by a table
  (`Kind.eoShape`, `indexedEoShape`, `nodeEoShape`):
  - `spine head arity`: `(head x₁ … xₙ)`, curried (most operators, UF
    application, indexed operators);
  - `rightAssocNil op nil`: `and`/`or`, right-nested with nil `true`/`false`;
  - `binderList` and `binder op` for quantifiers; `none` for no CPC counterpart.

  Wrong arities become `Term.Stuck`. This file is part of the specification
  (`TRUSTED.md`).
- `Node.WellTyped t`: the translation has a Logos SMT type. It is decidable, and
  `Node.getType` reads cvc5's `getType()` off Logos's type checker.
- `Node.Equiv t s`: the formula `(= t s)` is well typed, and `(not (= t s))` is
  unsatisfiable (`eo_satisfiability … false`). The typing conjunct matters:
  Logos evaluates `=` to a Boolean even on ill-typed arguments, so without it
  two ill-typed nodes would be "equivalent".

### Rewriter (`Telos/Rewriter/`)

- `RewriteStatus`, `RewriteResponse` and `TheoryRewriter` (`preRewrite`,
  `postRewrite`), as in cvc5.
- `theoryOf`: cvc5's type-based `Theory::theoryOf`. Variables go to the theory of
  their type, `EQUAL` to the theory of its arguments' type, anything else to the
  theory of its kind. `theoryRewriter` maps each theory to its rewriter (all
  trivial so far).
- `rewriteWith`: cvc5's `Rewriter::rewriteTo`. Pre-rewrite until done and in the
  same theory, rewrite the children, post-rewrite. `REWRITE_AGAIN` post-rewrites
  again, while `REWRITE_AGAIN_FULL` or a change of theory rewrites the result from
  the start. It takes fuel and returns its input when the fuel runs out, which
  is sound because the identity is an equivalence. Fuel bounds recursion depth,
  not work. There is no rewrite cache yet.
- Children are rewritten only when each is well typed, a runtime check
  (`decide c.WellTyped`) that stands in for a proof that the children of a
  well-typed node are well typed. Under a quantifier only the body is rewritten.

### Correctness (`verification/TelosProofs/`)

```lean
theorem Telos.rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t)
```

- `Equiv.lean`: `Node.equiv_iff` reduces `Equiv` to semantic equivalence of SMT
  terms (same type, related values in every well-formed model). `Equiv` is
  reflexive, symmetric and transitive.
- `Congruence.lean`: `Node.Equiv.congr` (equivalent children give an equivalent
  node, for every operator whose shape is child-congruent) and
  `Node.Equiv.congr_binder` (quantifiers, in their body). Both reuse Logos's
  soundness proof of the CPC `cong` rule, which is generic over application
  spines, so there is one case per `AppShape` and new kinds need no new proof.
- `Driver.lean`: `rewriteWith_sound`. If every theory rewriter is
  `TheoryRewriter.Correct` (its pre- and post-rewrites return equivalent nodes),
  the driver is sound. This is the obligation each ported theory rewriter meets.
- `Axioms.lean`: the axiom audit (`TRUSTED.md`).

Upstream candidates for Logos: make `CongSupport.congEvidenceSpine_eq_true`
public (copied here as `congEvidenceSpine_eq_true'`); and inversion lemmas
"the arguments of a well-typed application are well typed", which would remove
the driver's runtime check.

## Roadmap

1. ~~Equivalence algebra, congruence, driver.~~ Done, with trivial theory
   rewriters.
2. **Booleans.** Port `TheoryBoolRewriter` (`src/theory/booleans/
   theory_bool_rewriter.cpp`) and the builtin rewriter for `EQUAL`/`ITE`, each
   proven `TheoryRewriter.Correct`.
3. **Arithmetic, then bit-vectors.** Add kinds to the `toEo` tables, then port
   the theory rewriters.
4. **Front end.** Read SMT-LIB through the Logos parser and convert to `Node`;
   print rewritten terms. Differential testing against cvc5's rewriter.
5. **Performance.** Replace the runtime child type check with a proof, and add
   cached hashes, sharing and a rewrite cache.

Later: emit a CPC proof of `(= t (rewrite t))`, through RARE rules or by
elaborating rewriter macros (`solver-plan.md`, §2).

## Working conventions

- Small commits; each commit builds both projects and passes
  `scripts/check-hygiene.sh`.
- Never weaken a theorem statement to make a proof go through. If an obligation
  fails, stop and report.
- When a Logos statement is awkward to use, write an adapter lemma here and note
  it as an upstream candidate; do not edit Logos from this repository.
