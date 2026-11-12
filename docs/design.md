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
- `TypeNode`: `boolean`, `integer`, `real`, `bitVector w` so far.
- `Const`: constant payloads (cvc5's `getConst<T>()`).
- `Op`: the operator of an application, `kind k` or `indexed k indices` for
  parameterized kinds such as `BITVECTOR_EXTRACT` (the form of cvc5's API `Op`).
- `Node`: `const c`, `var name type` (cvc5 `VARIABLE`), and `app op children`
  with n-ary children, as in cvc5's `NodeValue`.

Numeric payloads (bit-vector widths and values, operator indices) are `Int`, the
type Logos uses, so `toEo` copies them unchanged. Out-of-range values are not
excluded by the datatype but rejected by `Node.WellTyped`. (cvc5 itself uses an
unsigned width and an arbitrary-precision value.)

`Node` is a plain tree with structural equality, not hash-consed through a
`NodeManager`. Hash-consing would tie every theorem to invariants of a global
table. Speed will come from a cached hash, physical sharing (`ShareCommon`) and a
rewrite cache keyed on the node. A table-backed `NodeManager` can be added
underneath later without changing the specification.

`APPLY_UF`, whose operator is a function symbol rather than indices, will need
an `Op` constructor holding a `Node` (making `Op` and `Node` mutual).

### Semantics (`Telos/Node/ToEo.lean`, `verification/TelosProofs/Spec.lean`)

- `Node.toEo` translates a node to a Logos term, the way cvc5 prints it in CPC and
  Ethos elaborates it. In particular `and`/`or` become right-nested with nil
  `true`/`false`. Wrong arities become `Term.Stuck`. This function is part of the
  specification (`TRUSTED.md`).
- `Node.WellTyped t`: the translation has a Logos SMT type. It is decidable, so it
  doubles as a runtime type checker.
- `Node.Equiv t s`: the formula `(= t s)` is well typed, and `(not (= t s))` is
  unsatisfiable (`eo_satisfiability … false`). The typing conjunct matters:
  Logos evaluates `=` to a Boolean even on ill-typed arguments, so without it
  two ill-typed nodes would be "equivalent".

### Rewriter (`Telos/Rewriter/`)

- `RewriteStatus` (`REWRITE_DONE`, `REWRITE_AGAIN`, `REWRITE_AGAIN_FULL`),
  `RewriteResponse` and `TheoryRewriter` (`preRewrite`, `postRewrite`), as in
  cvc5.
- `rewrite : Node → Node`: currently a stub (the identity).

The driver will follow cvc5's `Rewriter::rewriteTo`: pre-rewrite top-down,
rewrite the children, post-rewrite bottom-up, repeating on `REWRITE_AGAIN*`,
dispatching on `Kind.theoryId`. It takes fuel and returns its input when the fuel
runs out. That is sound because the identity is an equivalence, and it avoids
`partial def`, which proofs cannot see through.

### Correctness

```lean
theorem Telos.rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t)
```

The statement is final. Proofs are compositional:

- `Node.Equiv` is reflexive (done), symmetric and transitive (needed for the
  driver's repeated steps).
- Congruence: replacing children by equivalent children gives an equivalent node
  (needed for rewriting under operators).
- Each theory rewriter proves that its `preRewrite` and `postRewrite` return
  equivalent nodes. The driver theorem combines these lemmas, so theories are
  proven one at a time.

Proofs reuse Logos's lemmas (`Cpc/Proofs/`) where they exist. Lemmas that would
fit better in Logos are noted as upstream candidates, not forked.

## Roadmap

1. **Equivalence algebra.** Symmetry, transitivity and congruence of
   `Node.Equiv` for the current kinds.
2. **Driver.** The cvc5 fixpoint driver with fuel, proven correct given
   correct theory rewriters.
3. **Booleans.** Port `TheoryBoolRewriter` (`src/theory/booleans/
   theory_bool_rewriter.cpp`) and the builtin rewriter for `EQUAL`/`ITE`.
4. **Arithmetic, then bit-vectors.** Extend `Kind`, `TypeNode` and `toEo`
   together, then port the theory rewriters.
5. **Front end.** Read SMT-LIB through the Logos parser and convert to `Node`;
   print rewritten terms. Differential testing against cvc5's rewriter.
6. **Performance.** Cached hashes, sharing and a rewrite cache.

Later: emit a CPC proof of `(= t (rewrite t))`, through RARE rules or by
elaborating rewriter macros (`solver-plan.md`, §2).

## Working conventions

- Small commits; each commit builds both projects and passes
  `scripts/check-hygiene.sh`.
- Never weaken a theorem statement to make a proof go through. If an obligation
  fails, stop and report.
- When a Logos statement is awkward to use, write an adapter lemma here and note
  it as an upstream candidate; do not edit Logos from this repository.
