# Design: a verified SMT rewriter

telos is a port of cvc5's rewriter to Lean 4, with a proof that every rewrite
preserves equivalence. Each rewrite step is an instance of a CPC proof rule,
checked by Logos's verified rule programs. This document describes the
architecture and the plan. `solver-plan.md` holds the earlier, broader plan for a
full solver; its notes on Logos still apply.

## Goals

1. **Verified.** `Telos.rewrite_correct` proves that the rewriter preserves
   equivalence. No `sorry`, no new axioms (`TRUSTED.md`).
2. **In sync with CPC by construction.** The rewrites are the CPC rules (RARE
   rewrites and theory rewrites) that Logos compiles from the Eunoia signature and
   proves sound. telos adds no rewrite of its own, so every rewrite telos
   performs is one a CPC proof can justify. Every rewrite also produces such a
   proof.
3. **Faithful to cvc5, by testing.** `Node`, `Kind`, `TypeNode`, `TheoryRewriter`
   and `RewriteResponse` mirror cvc5's, with cvc5's names. Which rule to apply,
   and when, mirrors cvc5's C++ theory rewriters. That telos reaches the same
   normal forms as cvc5 is checked by differential fuzzing, not proved. cvc5's
   rewriter has no formal specification to prove it against.

Non-goals for now: matching cvc5's speed, and termination proofs (fuel is used).

## Architecture

```
Node ──toEo──▶ Eo.Term ──__eo_to_smt──▶ SmtTerm ──__smtx_model_eval──▶ SmtValue
 (telos)        (Logos)                  (Logos)                         (Logos)
```

Five layers, from the bottom:

| Layer | Where | Trusted? | Proof cost per rule |
|---|---|---|---|
| `Node` and its semantics (`toEo`) | `Telos/Node/` | specification | — |
| Certified rule step | `Telos/Rewriter/Certified.lean` | verified once | none |
| Rule database | `Telos/Rules/` (generated) | untrusted | none |
| Theory strategies | `Telos/Theory/` (hand-written) | untrusted | none |
| Driver (`rewriteWith`) | `Telos/Rewriter/` | verified once | none |

A wrong rule database or strategy can lose rewrites, or differ from cvc5. It
cannot make telos unsound.

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

`Node.ofEo` (`Telos/Node/OfEo.lean`) is the partial inverse of `toEo`. It turns the right-hand
side of a rule's conclusion, an `Eo.Term`, back into a node. Its correctness is
checked at run time, `(ofEo r).toEo == r`, so it needs no proof and can be
incomplete.

### Semantics (`Telos/Node/ToEo.lean`, `verification/TelosProofs/Spec.lean`)

- `Node.toEo` translates a node to a Logos term, the way cvc5 prints it in CPC and
  Ethos elaborates it. Each operator has an `AppShape`, given by a table
  (`Kind.eoShape`, `indexedEoShape`, `nodeEoShape`):
  - `spine head arity`: `(head x₁ … xₙ)`, curried (most operators, UF
    application, indexed operators);
  - `rightAssocNil op nil`: `and`/`or`/`+`/`*`, right-nested and ending in a
    nil. The nil is constant for `and`/`or` (`true`/`false`) and typed for `+`
    and `*`: `(eo::nil op (eo::typeof x₁))`, which is `0`/`1` or `0/1`/`1/1`,
    computed from the first element as Logos's parser and Eunoia do. The
    congruence proof shows that equivalent first elements give the same nil
    (`typedNil_congr`);
  - `typedList op`: `distinct`, applied to one typed argument list
    `(@@TypedList_cons x₁ … (@@TypedList_nil T))`, its nil typed like that of
    `+`. Its congruence is not proved yet (`isChildCongruent` is false), so the
    children of a `distinct` are not rewritten; the UF rewriter expands one with
    at most 10 children first, as cvc5 does;
  - `binderList` and `binder op` for quantifiers; `none` for no CPC counterpart.

  Wrong arities become `Term.Stuck`. This file is part of the specification
  (`TRUSTED.md`).
- `Node.WellTyped t`: the translation has a Logos SMT type. It is decidable, and
  `Node.getType` reads cvc5's `getType()` off Logos's type checker.
- `Node.Equiv t s`: the formula `(= t s)` is well typed, and `(not (= t s))` is
  unsatisfiable (`eo_satisfiability … false`). The typing conjunct matters:
  Logos evaluates `=` to a Boolean even on ill-typed arguments, so without it
  two ill-typed nodes would be "equivalent".

### Certified rule steps (`Telos/Rewriter/Certified.lean`)

A rule step rewrites a node `n` to `m` by one CPC rule. Logos compiles every
CPC rule into Lean (`Cpc/Logos.lean`). `__eo_prog_ite_true_cond x y` computes
the conclusion `(= (ite true x y) x)`, for example, and `__eo_cmd_step_proven`
dispatches on the rule. Logos proves every rule sound, and its checker soundness
proof (`invoke_cmd_list_preserves_stateInvariant`, `Cpc/Proofs/Checker.lean`)
covers any command list run from the empty state. So telos does not compute
right-hand sides, and does not prove anything per rule. A step:

1. takes a rule and its arguments from a matcher (`Telos/Rules/`);
2. builds a short CPC command list. That is a step for each of the rule's
   premises, if any (`evaluate` by default, or a step the strategy chooses, such
   as `bool-double-not-elim` for `(= (not (not b)) b)`), then the rule itself;
3. runs Logos's checker on it from the empty state. It returns the last proven
   fact;
4. reads `r` off the fact `(= l r)`, sets `m := Node.ofEo r`, and checks that
   the fact is exactly `(= n m)` (`eqFormula n m`), which also checks `l`.

Only steps are run, never assumptions, so the proven facts may contain free
variables. This is what lets rewrites under binders, whose bodies contain the
bound variables, be certified.

If any check fails, the step does not apply. Soundness is stated once. In the
root package (no Mathlib, no proofs):

```lean
/-- `cs` meets Logos's translation side conditions and, run from the empty
state, is closed and its last proven fact is `(= n m)`. -/
def ProvesEq (cs : CCmdList) (n m : Node) : Prop :=
  CmdListTranslationOk cs ∧ __eo_state_is_closed (runFromEmpty cs) = true ∧
    __eo_state_proven_nth (runFromEmpty cs) 0 = eqFormula n m

inductive Certified : Node → Node → Type
  | refl (n : Node) : Certified n n
  | step (cs : CCmdList) : ProvesEq cs n k → Certified k m → Certified n m
  | congrArg (i : Nat) (c' : Node) … :    -- rewrite child i, below a congruent
      …  Certified cs[i] c' → Certified (.app op (cs.set i c')) m →
      Certified (.app op cs) m
  | congr …       -- rewrite every child of a congruent operator
  | congrBody …   -- rewrite the body of a quantifier

abbrev Rw (n : Node) := (m : Node) × Certified n m
```

`Certified` is data, not a proposition: it keeps the command lists, which is
what lets telos print proofs (below). Its proof fields are erased at run time.

`congrArg` lets a strategy rewrite below the top, for example to flip an
equality inside another before applying a rule. The driver uses `congr` and
`congrBody` to rewrite children. The congruence constructors require the
operator to be child-congruent and the children (or the body) to be well typed,
checked at run time, and are justified by `Node.Equiv.congr` and
`Node.Equiv.congr_binder`.

`ProvesEq` is decidable, and is decided by running Logos's checker. In
`verification/` (`TelosProofs/Certified.lean`):

```lean
theorem Certified.equiv : Certified n m → n.WellTyped → n.Equiv m
```

proved from Logos's `proven_from_empty_valid` (`Cpc/Proofs/ProvenFromEmpty.lean`:
the checker's soundness, from the empty state) and `Node.equiv_iff_termEquiv`. A
`RewriteResponse n` carries a `Certified n node`, so every theory rewriter is
correct by construction (`TheoryRewriter.correct`), and strategies need no
proofs. The driver chains the certificates, so it is correct by construction
too.

The certificate depends on all of Logos's rule proofs, since the checker's
soundness does: most of Logos's proof code (888 of the 889 modules telos's
proofs import). So the default build of `verification/` takes that one theorem
as a hypothesis: `LogosCheckerSound` (`TelosProofs/LogosSound.lean`) restates
`proven_from_empty_valid`, and `Certified.equiv`, the driver's theorems and
`Telos.rewrite_correct_of_logos` take it as an argument. That build needs only
Logos's definitions and its support lemmas (62 modules), and runs in CI.
`lake -d verification build TelosFull` imports the rule proofs, proves
`LogosCheckerSound` from `proven_from_empty_valid` (so the restatement cannot
drift from the pinned Logos), and derives the unconditional
`Telos.rewrite_correct`. Run it after changing the Logos pin.

The cost is speed. Every step translates to `Eo.Term` and runs a Logos program.
That is acceptable to start. Later, generated lemmas of the form "for
non-stuck arguments, the program returns the instantiated template" (the shape
Logos's own `prog_eq_of_nonstuck` lemmas take, proved by `cases <;> rfl`) can
replace the run-time check for hot rules.

### Rule database (`Telos/Rules/`, generated)

For each rewrite rule, the database holds what is needed to *find* an
application. That is the rule's `CRule` constructor, its `:args` variables, the
pattern of its left-hand side, and its premise templates. It does not hold the
right-hand side, which Logos's program computes, including list operations such
as `eo::list_singleton_elim`.

It is generated from `install/defs/Cpc.cached.eo` in the pinned Logos checkout,
the same file Logos compiled. So bumping the Logos revision and regenerating
keeps the two in sync. See "The rule extractor" below.

One generic matcher (`Telos/Rules/Match.lean`) interprets the patterns. It
handles:

- variables, constants, and the operator encodings of `AppShape`;
- `:list` variables over right-assoc-nil operators, which match a segment of an
  n-ary node (possibly empty, and possibly ambiguous, so the matcher can
  enumerate);
- implicit parameters (`@n0`, `@T0`). These are not `:args`, and Logos infers
  them from the arguments' types.

Premises are instantiated from their templates and discharged by `evaluate`
(`RuleSpec.apply`). A
premise of the form `(= c v)` holds when Logos evaluates `c` to `v`.
`bv-extract-whole`'s `(= (>= n1 (- (@bvsize x1) 1)) true)` is an example. If the
evaluation does not give `v`, the rule does not apply. As in cvc5, rules with
conditions fire only when the condition is decided by evaluation.

Rewrites that cvc5 performs in C++ and that no RARE rule captures are the
theory rewrites of CPC (`ProofRewriteRule`). Examples are `aci_norm`,
`arith_poly_norm`, `bv_poly_norm`, `distinct_elim`, the `ite` lookahead rules,
quantifier miniscoping and the string rules. Many of them take the whole
equation as an argument and check it. For these, telos computes the right-hand
side with ordinary, unverified code ported from cvc5, and the rule validates
it (`checkBy`, `Telos/Theory/Common.lean`). The interface is the same. For
example, cvc5's `flattenNode` is computed as in C++ and certified by `aci_norm`
(flattening, removing `true`/`false` and duplicates: both sides have the same
sorted normal form) or, when the result is the zero element, by `absorb`.

### Theory strategies (`Telos/Theory/`, hand-written)

A rule says what a rewrite *may* do, not what it *should* do. `eq-symm` proves
`(= (= t s) (= s t))`, so the rule database could flip any equality. cvc5 flips
one only when its children are out of order. The strategies hold that
knowledge. Each is a port of the control flow of a cvc5 theory rewriter
(`TheoryBoolRewriter::preRewrite`/`postRewrite`, …). It decides:

- which rule to try on which kind, in what order;
- pre- or post-rewrite, and the `RewriteStatus` to return (`REWRITE_DONE`,
  `REWRITE_AGAIN`, `REWRITE_AGAIN_FULL`);
- orientation and ordering, through a term order.

**Term order.** cvc5 orders by node id, which depends on creation order and is
not reproducible outside one cvc5 run. telos uses a fixed total order on `Node`
(`Telos/Node/Order.lean`). Its first version is structural: kind, then
operator, then children lexicographically. It is used wherever cvc5 compares
ids: orienting equalities, sorting the children of commutative operators
(`aci_norm`), and choosing between symmetric rewrites. telos's normal forms will
therefore differ from cvc5's up to this order. Fuzzing compares them modulo it
(below).

Strategies are untrusted, so they can follow the C++ line by line with no proof
work. Porting a theory rewriter is pure programming.

### Driver (`Telos/Rewriter/`)

- `RewriteStatus`, `RewriteResponse` and `TheoryRewriter` (`preRewrite`,
  `postRewrite`), as in cvc5.
- `theoryOf`: cvc5's type-based `Theory::theoryOf`. Variables go to the theory of
  their type, `EQUAL` to the theory of its arguments' type, anything else to the
  theory of its kind. `theoryRewriter` (`Telos/Rewrite.lean`) maps each theory
  to its rewriter: `THEORY_BOOL` to the port of `TheoryBoolRewriter`
  (`Telos/Theory/Bool.lean`), the others to the identity so far.
- `rewriteWith`: cvc5's `Rewriter::rewriteTo`, returning a certified rewrite
  (`Rw n`). Pre-rewrite until done and in the
  same theory, rewrite the children, post-rewrite. `REWRITE_AGAIN` post-rewrites
  again, while `REWRITE_AGAIN_FULL` or a change of theory rewrites the result from
  the start. It takes fuel and returns its input when the fuel runs out, which
  is sound because the identity is an equivalence. Fuel bounds recursion depth,
  not work. There is no rewrite cache yet.
- Children are rewritten only when each is well typed, a runtime check
  (`decide c.WellTyped`) that stands in for a proof that the children of a
  well-typed node are well typed. Under a quantifier only the body is rewritten.

### Front end (`Telos/Frontend.lean`, `Main.lean`)

`telos FILE` reads an SMT-LIB script of declarations (`declare-const`,
`declare-fun`, `declare-sort`) and `(simplify t)` commands, and prints the
rewrite of each `t`. Terms are read by Logos's own parser: the script is turned
into Eunoia input in which `(simplify t)` becomes `(assume @sN (= t t))`, and `t`
is taken back from the parsed assumption. Declared constants come back as
Logos's numbered `UConst`s; the front end replays the numbering to make them
named `Node.var`s, and `Node.ofEo` reads the rest. A term with an operator that
has no `Kind` yet is reported as unsupported.

### Proof output (`Telos/Proof/`)

With `--proof` (or `--proof-dir DIR`), each result comes with a CPC proof of
`(= t result)`. `Proof.emitProof` flattens the certificate into one list of
steps: each step's command list as is, `trans` between consecutive steps, and
`cong` (`nary_cong` for `and`/`or`) below an operator, with `refl` for the
children that do not change. The list is run through Logos's checker from the
empty state and must prove `(= t result)`, so telos only prints proofs Logos
accepts. `Eunoia.print` prints terms by inverting the operator table of Logos's
parser, and `ruleName` (generated) names the rules.

The proof is a refutation: the declarations, `(assume @goal (not (= t
result)))`, the steps, and `false` by `contra`, printed in parentheses as
cvc5's `get-proof` prints a proof. Without the parentheses it checks with
`ethos --include=Cpc.cached.eo` and with Logos (telos reads it back with
Logos's parser before printing it). A bound variable outside its
binder (in a step about a quantifier's body) is printed `(@var "x" T)`, the
signature's macro for `eo::var`. `scripts/check-proofs.py` checks proofs with
Ethos, on example scripts or on fuzzed terms.

None of this is trusted. Proof output is for exchanging proofs with other tools;
results are correct with or without it.

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
- `LogosSound.lean`: `LogosCheckerSound`, Logos's checker soundness
  (`proven_from_empty_valid`) as a proposition.
- `Certified.lean`: `Certified.equiv`, from Logos's checker soundness.
- `Driver.lean`: `rewriteWith_sound`, for any theory rewriters: the driver's
  result is certified, so this is an instance of `Certified.equiv`.
- `Rewriter.lean`: `Telos.rewrite_correct_of_logos`, the theorem given
  `LogosCheckerSound`.
- `Axioms.lean`: the axiom audit (`TRUSTED.md`).
- `TelosFull/Main.lean` (`lake build TelosFull`, not a default target): proves
  `LogosCheckerSound` from Logos's theorem, and so `Telos.rewrite_correct`, and
  audits its axioms.

Upstream requests to Logos are collected in `../logos/telos-upstream-requests.md`
(untracked, a brief for an agent working there).

## The rule extractor

telos does **not** maintain a second Eunoia-to-Lean compiler. Logos already
compiles the signature with `ethos-eoc`, and telos reuses that output for
everything that matters to soundness: the rule programs, the checker and their
proofs. What telos needs is narrower, a *rule extractor*:

```
Cpc.cached.eo (pinned Logos) ──scripts/gen-rules.py──▶ Telos/Rules/Generated.lean
                                                        (data: RuleSpec table)
```

- **Input:** the `declare-rule` forms of `Cpc.cached.eo`. It is one flattened
  file, so the extractor needs an S-expression reader, not Eunoia's include and
  elaboration machinery.
- **Output:** Lean *data*, a `List RuleSpec`, interpreted by the generic matcher.
  Not code, and no proofs. Data keeps the generated file simple and its builds
  fast, and lets the strategies name rules.
- **Untrusted.** A mistake loses rewrites or makes a matcher propose arguments
  that the certified step then rejects. To find such mistakes, a generated test
  instantiates each rule's left-hand side with fresh variables and checks that
  the matcher finds it and the step succeeds.
- **Patterns.** Left-hand sides are patterns over kinds (`Pat`): variables,
  `:list` variables of n-ary operators, constants, applications, indexed
  applications whose indices are patterns (`(extract i j x)`, as the signature
  writes it), and bit-vector literals `(@bv v w)`. The signature defines `@bv`
  as `((_ int_to_bv w) v)`, a term, so the matcher first rewrites a matched
  literal to that form (`evaluate` and `symm`, under congruence,
  `toSymbolic`). `eo::define` is inlined.
- **Premises** are evaluated: `(= A v)` by `evaluate`, and `(= x E)` with `x` a
  variable by `evaluate` and `symm`. The matcher evaluates each premise when it
  matches, and the value must match the other side, binding its variables. This
  is how rules define arguments, as in `(= wm (- (@bvsize x) 1))`, and it rejects
  a rule whose premise fails without running the checker.
- **In sync.** The generated file is checked in. CI regenerates it from the
  pinned Logos checkout (`.lake/packages/Cpc/install/defs/Cpc.cached.eo`) and
  fails on a difference, as Logos's own `install-cpc.sh --check` does.

What needs care:

1. **Symbol mapping.** The extractor maps Eunoia symbols to telos `Kind`s (or to
   the `Eo.Term` constructors eoc emits). This is the same table as
   `Kind.eoShape`, read in the other direction. To avoid keeping two copies, the
   extractor reads the symbol names from a single table that `Telos/Node/ToEo.lean`
   also uses (generated, or checked by a test).
2. **Patterns on `Node` or on `Eo.Term`.** Matching on `Eo.Term` is closest to
   the source: patterns are the conclusion's left-hand side as written, and
   right-assoc-nil lists are already in Eunoia's encoding. Matching on `Node`
   avoids translating every candidate. Plan: match on `Node`, with patterns
   stated in telos kinds. Rules whose left-hand side uses a symbol with no `Kind`
   yet are skipped, and listed in a report, which also tracks coverage.
3. **Which rules are rewrites.** A rewrite rule's conclusion is `(= lhs rhs)` and
   its `:args` determine every variable of `lhs`. That covers the RARE rules and
   most theory rewrites. Rules whose arguments include the whole equation (for
   example `arith_poly_norm`, `aci_norm`) are listed separately. Strategies
   reach them by computing the right-hand side themselves.
4. **Language.** Python, like Logos's install and check scripts: S-expressions are
   trivial to read, and the extractor never runs at proof time. If the symbol
   mapping grows hairy, the long-term home is a rule-table backend in
   `ethos-eoc`, which already resolves overloading and the encodings. That would
   be a change in ethos, not here.

## Testing: differential fuzzing against cvc5

Correctness with respect to the CPC semantics is proved. Agreement with cvc5 is
tested:

- **Normal forms.** Random well-typed terms (and terms from SMT-LIB benchmarks)
  are rewritten by telos and by cvc5 (`--rewrite` style via the API). The outputs
  are compared syntactically after normalizing both by telos's term order. The
  report gives the match rate per theory and the most frequent divergences, and
  is how strategy ports are judged.
- **Semantics.** For every pair, cvc5 checks `(distinct telos_out cvc5_out)` is
  unsatisfiable. telos's output is proved equivalent to its input under Logos's
  semantics. So a satisfiable answer means Logos's semantics and cvc5's disagree,
  a bug in the trusted base or in cvc5, which is worth reporting either way.
- **Coverage.** Which rules fire, and which cvc5 rewrites have no rule that
  could justify them.

## Roadmap

1. ~~Equivalence algebra, congruence, driver.~~ Done, with trivial theory
   rewriters.
2. ~~Certified steps.~~ Done: `Node.ofEo`, `ProvesEq`, `Certified`,
   `Certified.equiv`; the driver returns certified rewrites, so it is correct
   by construction.
3. ~~Rule extractor and matcher.~~ Done: `scripts/gen-rules.py` (55 rules: the
   `bool-*`, `ite-*` and `eq-*` rules), `RuleSpec`, the matcher, the self-test
   (`TelosTests/Rules.lean`) and the CI sync check.
4. ~~Booleans.~~ `TheoryBoolRewriter` is ported (`Telos/Theory/Bool.lean`, tests
   in `TelosTests/Bool.lean`).
   - ~~UF.~~ `TheoryUfRewriter` is ported for the kinds telos has
     (`Telos/Theory/UF.lean`, `test/examples/uf.smt2`): equalities over
     uninterpreted sorts and functions (`eq-refl`, orientation by `eq-symm`),
     and `distinct` (the new kind `DISTINCT`: `distinct-card-conflict`,
     `distinct-false`, `distinct-true`, and `distinct-elim` to pairwise
     disequalities). cvc5's builtin rewriter only rewrites `witness` and
     symbolic indexed applications, which telos does not have.
   - Fuzzing (`scripts/fuzz.py --uf`, 3000 terms of depth 4, with equalities of
     `U` terms over `u`, `v`, `w`, `f` and `distinct` over `U`, Booleans and
     integers): 78.9% identical to cvc5, all others identical up to the
     orientation of equalities (cvc5 orients by node id), no semantic
     disagreements. Ethos accepts all proofs (`check-proofs.py --uf`).
   - Deviations: equalities are oriented by telos's term order; the children of
     a `distinct` with more than 10 children are not rewritten (see `typedList`).
   - Open: equality rewriting of the theories not ported yet (strings, bit-vectors,
     arrays, sets), which cvc5 does in their own rewriters.
5. **Front end and fuzzing.** The `telos` executable reads SMT-LIB scripts of
   `(simplify t)` queries through Logos's parser (`Telos/Frontend.lean`).
   `telos-fuzz` (random Boolean terms over three Booleans and two integer
   equalities) and `scripts/fuzz.py` compare with cvc5's `(simplify t)`. On 6000
   terms of depth 4: about 94% identical to cvc5, every other result identical up
   to (or caused by) the orientation of equalities, and no semantic
   disagreements. To do: `define-fun`, and fuzzing in CI.
   - The reference is a recent build of cvc5 (the rates in this document are
     against `bab27e4f17`, 2026-10-06, and, where they say so, against the
     branch of cvc5 PR #13167, `f155e68cee`, which fills the proof holes of
     `test/cvc5-holes/`), passed as `--cvc5 PATH`
     or `CVC5=PATH`; `fuzz.py` prints the version it used. A release is not
     enough: cvc5's rewriter changes, and telos ports the current one.
6. **Arithmetic, then bit-vectors.** Arithmetic is started.
   - Kinds `ADD`, `SUB`, `NEG`, `MULT`, `DIVISION`, `INTS_DIVISION`,
     `INTS_MODULUS`, their total versions, `ABS`, `LT`, `LEQ`, `GT`, `GEQ`,
     `TO_REAL`, `TO_INTEGER` and `IS_INTEGER`, with their congruence proof, and
     36 more generated rules.
   - `Telos/Theory/Arith.lean` ports the core of cvc5's `ArithRewriter`:
     polynomial normal forms of terms (certified by `arith_poly_norm`), the
     normalization of `>=`, `<=`, `>` and `<` to `(>= sum c)` or
     `(not (>= sum c))` with integer tightening (`arith_poly_norm_rel`,
     `arith-elim-*`, `arith-leq-norm`, `arith-int-geq-tighten`), and equalities
     (integer conflicts by `arith-int-eq-conflict`, orientation by `eq-symm`),
     `div`/`mod` by constants to their total versions and the total versions'
     cases (by zero, one, a negative constant, constants, `mod` over `mod`,
     `div` over `mod`), constant `abs`, `to_int` and `is_int`, `to_int` and
     `is_int` of `to_real` (`arith-to-int-elim-to-real`,
     `arith-is-int-elim-to-real`), and the sides of `/` and `/_total` as cvc5
     PR #13167 has them: made real for a non-constant denominator (`(/ x y)` is
     `(/ (to_real x) (to_real y))`, by `arith-div-int-to-real` and
     `arith-div-total-int-to-real`, then `evaluate` for a constant numerator),
     and `to_real` removed from both for a constant one (the same rules read
     right to left), also before the children are rewritten (`preRewrite`), so
     `(/ (to_real 0) (to_real 0))` is `(/ 0 0)`.
   - Fuzzing (`scripts/fuzz.py --arith`, 3000 terms of depth 4, including
     `div`, `mod`, `abs`, `to_int` and `is_int`): 86.9% identical to cvc5,
     96.9% up to the orientation of equalities, 98.4% also up to the order of
     commutative arguments, no semantic disagreements. Against PR #13167:
     87.5%, 97.2% and 98.4%. The other 47 differ in
     which monomial leads a normalized inequality, which cvc5 decides by node
     id (`LeafNodeComparator`), and so in its sign and scaling.
     Equalities are only oriented, not solved, as in cvc5 since PR #12833
     (against an older build that solves them, `97b00835f`, only 73.0% are
     identical).
     Ethos accepts all proofs (`scripts/check-proofs.py --arith`).
   - Arithmetic literals are printed as single tokens (`-3`, `1/2`, `3/1`), as
     Eunoia writes them and as cvc5 prints them with `--print-arith-lit-token`,
     which `scripts/fuzz.py` passes.
   - Deviations: an integer leaf of a real sum keeps its `to_real`, since Logos
     has no mixed arithmetic (cvc5 prints its mixed sums the same way);
     non-variable leaves (products, `abs`, `div`, …) are ordered by telos's term
     order, where cvc5 uses node ids, which also decides the leading term of a
     normalized inequality. cvc5 also removes `to_real` from one side of `/`,
     as in `(/ (to_real x) r)` to `(/ x r)`, a mixed division Logos rejects.
   - To do: the extended operators (`int.log2`, `iand`, transcendentals;
     `int.pow2`, `int.log2` and `int.ispow2` have kinds, for the premises of
     bit-vector rules, but are not rewritten).
   - **Bit-vectors.** Kinds for all of cvc5's bit-vector operators,
     `int_to_bv`, `ubv_to_int` and `sbv_to_int`. The n-ary ones (`concat`,
     `bvand`, `bvor`, `bvxor`, `bvadd`, `bvmul`) have a typed nil, and their
     congruence is proved (`bv_nary_args`, `typedNil_congr_bv`: equivalent
     bit-vector terms have the same Eunoia type, by Logos's
     `eo_typeof_eq_of_smt_type_eq`). The rule table has 141 of the 145
     bit-vector and conversion rules (233 rules in all). `Telos/Theory/BV.lean`
     ports cvc5's `TheoryBVRewriter` kind by kind, with RARE rules for cvc5's
     rewrite rules and `evaluate` for constants. `Telos/Theory/BVNorm.lean`
     ports the rules over whole n-ary terms, computed natively and certified:
     the polynomial ones (`FlattenAssocCommut`, `AddCombineLikeTerms`,
     `MultSimplify`, `MultDistrib*`, `NegIdemp`, `NegSub`, `NegAdd`) by
     `bv_poly_norm`, the bitwise ones (`AndSimplify`, `OrSimplify`,
     `XorSimplify`, `XorZero`) by a short search over `aci_norm`, `absorb`,
     `evaluate` and the RARE `bv-*-simplify-*` rules (as cvc5's
     `MacroRewriteElaborator` proves them), and `ConcatFlatten` by `aci_norm`.
     `RepeatEliminate` and `BitwiseSlicing` use the Logos programs of
     `bv-repeat-elim` and `bv-bitwise-slicing` to compute their results
     (`byProgram`). `UltOnes` with the constant on the left has no CPC rule and
     is derived (`bv-ule-max`, `bv-ule-eliminate`, `true_elim`, `false_intro`).
     The `(@bv v w)` of a rule's right-hand side, which Logos writes
     `((_ int_to_bv w) v)`, is evaluated back to a literal after each rule step
     (`foldIntToBv`).
   - Also: constant `bvcomp` (by `bv-comp-eliminate`, as Logos's `evaluate`
     does not reduce it), `bvumulo` and `bvsmulo` of constants (their
     `:requires` programs are extracted from Logos's compiled code into
     `Telos/Rules/Programs.lean` by `gen-rules.py`), and the comparisons of
     `sign_extend`/`zero_extend` with constants, in cvc5's order. Premises may
     equate two terms (both evaluated), and the `@bv` literals of premises are
     written as the rule writes them, `((_ int_to_bv w) v)`.
   - Fuzzing (`scripts/fuzz.py --bv`, over three `(_ BitVec 4)` variables and
     constants, with all operators including `zero_extend`, `sign_extend`,
     `repeat`, `bvite`, `bvcomp`, `bvredor`, `bvredand` and the overflow
     predicates): at depth 3 (3000 terms), 80.7% identical to cvc5 and 97.0% up
     to the orientation of equalities, 99.7% also up to the order of
     commutative arguments, no semantic disagreements; the other 8 come from
     the order of children too: `AndOrXorConcatPullUp` pulls up the first
     `concat` among the (id-ordered) children. (Before Logos had `bv-ite-const-cond`, a
     constant-condition `bvite` was left as it was, and only 50.1% were
     identical.) Ethos accepts all
     proofs (`check-proofs.py --bv`, depths 3 and 4).
   - Deviations: cvc5 orders the children of `bvand`, `bvor`, `bvxor` and
     `bvmul`, and the terms of a combined sum, by node id; telos uses its term
     order, which accounts for most of the remaining differences. A bitwise
     result for which the search finds no certificate is not used. cvc5's
     `NegMult` never applies (its `applies` tests the wrong child) and is not
     ported.
   - `BvIteConstCond` uses `bv-ite-const-cond-1/2` (added to Logos at our
     request, Logos PR #503; cvc5 itself proves this step with a
     trust step). Not ported: `BvComp`. `IneqElimConversion` (comparisons of `int_to_bv` terms and
     constants as integer comparisons, `uf-int2bv-bvult-equiv`) is ported,
     with the UF rewriter's `rewriteBVToInt` (`uf-int2bv-bv2nat`) and the
     `int_to_bv` of `ubv_to_int` cases of `rewriteIntToBV`, and the evaluation
     of `int.pow2`, `int.log2` and `int.ispow2` of constants.
   - Performance (3000 terms of depth 3, `telos-fuzz ... bv`): 4.65s at first,
     3.73s after indexing rules by name (`ruleTable`), evaluating premises at
     match time with Logos's evaluator directly rather than a checker run, and
     structural bit-vector types in `typeHint`; 2.55s with the rewrite cache;
     2.36s after `childrenTypedOfParent` for the non-indexed bit-vector kinds.
     Outputs are unchanged throughout. The rest is spread out: checker runs,
     comparisons and read-backs about 35%, RARE matching 18%.
   - cvc5 bug found while porting: `RewriteRule<NegMult>::applies` never holds
     (`cvc5-negmult-bug.md`).
7. **Arrays.** `TheoryArraysRewriter` is ported (`Telos/Theory/Arrays.lean`,
   `test/examples/arrays.smt2`) for `select`, `store` and array equalities,
   with the six RARE rules for arrays (`array-read-over-write`,
   `array-read-over-write2`, `array-store-overwrite`, `array-store-self`,
   `array-store-swap`, and `array-read-over-write-split`, generated but not
   used by cvc5's rewriter).
   - cvc5 decides whether two indices are distinct by rewriting their equality
     (`mkEqNode`). telos does the same: the arrays rewriter is given the
     rewriter of the other theories (`theoryRewriter`, `indexFuel`), and the
     premise `(= (= i j) false)` of `array-read-over-write2` and
     `array-store-swap` is proven by the CPC proof of that rewrite
     (`Proof.emitProof`), followed by the rule step; `applyCmds` checks all of
     it. Distinct constant indices are decided by `evaluate`.
   - cvc5 moves a `store` down a chain of `store`s at once; telos swaps once
     and rewrites again (`REWRITE_AGAIN_FULL`), to the same normal form.
   - Fuzzing (`scripts/fuzz.py --arrays`, 3000 terms of depth 3 over two
     `(Array Int Int)` constants, with indices `x`, `y`, `0`, `1`, `2` and
     `(+ x 1)`): 69.0% identical to cvc5, all others identical up to the
     orientation of equalities, no semantic disagreements. Ethos accepts all
     proofs (`check-proofs.py --arrays`).
   - Not ported: constant arrays (`store_all`, which has no counterpart in
     Logos), `eqrange`, an index equality that rewrites to `true` for distinct
     indices, and child typing for `select` and `store` (`Op.childrenTypedOfParent`:
     its proof needs well-formedness of array types, so the driver checks the
     children at run time).
   - **Mixed theories** (`scripts/fuzz.py --mixed`, 3000 terms of depth 3):
     atoms that mix theories (arrays from bit-vectors to integers and over an
     uninterpreted sort, `ite` with branches of each theory, UF applied to
     array reads, `distinct` of arrays, `int_to_bv` comparisons). 47.0%
     identical to cvc5, 97.0% up to the orientation of equalities, no semantic
     disagreements; the 89 differences are the order of `store`s and of
     children. Ethos accepts all proofs.
8. **Strings (stage 1).** Kinds for the string and regular expression
   operators (not sequences yet), with their CPC shapes: `str.++` with a typed
   nil (its congruence is proved like that of the bit-vector operators, with
   Logos's well-formedness of `Seq` types), `re.++`, `re.inter` and `re.union`
   with constant nils (`translation_rest_re`). The rule generator reads the
   signature's `seq.*` aliases, nullary regular expressions and string
   literals: 168 of the 203 string rules. The rule self-test gives variables
   their declared types and accepts rules whose left-hand side matches but
   whose premises do not hold on fresh variables. `Telos/Theory/Strings.lean`
   ports cvc5's `rewriteConcat` (by `aci_norm` and `evaluate`), parts of
   `rewriteLength`, `rewriteEquality`, `rewriteCharAt`, `rewritePrefixSuffix`
   (without arithmetic entailment), the eliminations of `re.opt`, `re.+`,
   `re.diff` and `re.^`, `rewriteRangeRegExp`, and the evaluation of
   operators on constants.
   - Fuzzing (`scripts/fuzz.py --strings`, 3000 terms of depth 3 over two
     string constants `su`, `sv` and small literals): 27.6% identical to cvc5
     (24.1% after the first step), no semantic disagreements; Ethos accepts all
     proofs. The largest gaps are `rewriteSubstr`, `rewriteMembership` and the
     regular expression rewrites, `rewriteReplace` and `rewriteContains`.
   - **Arithmetic entailment** (`Telos/Strings/ArithEntail.lean`): cvc5's
     `ArithEntail` as the strings rewriter uses it by default (no rewriter, no
     recursive approximations, so `rewriteArith` is `rewriteLengthIntro` and
     the polynomial normal form): `checkSimple`, `getArithApproximations`,
     `findApprox`, `check`, `checkEq`, and `StringsEntail::checkLengthOne`. A
     rule's arithmetic premises that evaluation does not discharge are proven
     as cvc5 elaborates `MACRO_ARITH_STRING_PRED_ENTAIL`
     (`ArithEntail.premiseProof`): `arith-elim-leq`, `arith-elim-int-gt` or
     `arith-elim-int-lt` to `>=`, length introduction (`str-len-concat-rec`,
     `evaluate`), `arith_poly_norm_rel` to `(>= n 0)`,
     `arith-string-pred-safe-approx`, `arith_poly_norm_rel`, and
     `arith-string-pred-entail` or `evaluate`; equalities of lengths
     (`checkEq`) by length introduction, `arith_poly_norm` and `true_intro`.
     The matcher takes such a premise prover (`RuleSpec.apply`,
     `rewriteByWith`), and rules may have type arguments (`(Seq @T0)`, the
     type of a variable; `typeArgs`).
   - With it: `rewriteSubstr`, including `rewriteViaMacroSubstrStripSymLength`
     (`StringsEntail::stripSymbolicLength`, for whole components: a constant
     that would be split is left, which cvc5 proves by an encoding transform),
     certified as cvc5 elaborates `MACRO_SUBSTR_STRIP_SYM_LENGTH` (`aci_norm`
     to regroup, then `str-substr-len-include-pre`, `str-substr-full`,
     `str-substr-concat2` or `str-substr-len-include`); the `SUF_PREFIX_EMPTY`
     and `SUF_PREFIX_TO_EQS` cases of `rewritePrefixSuffix`; `LEN_REPL_INV`.
   - Regular expressions: `rewriteAndOrRegExp` without its two macros (a
     search over `aci_norm`, `absorb`, `re-union-all`, `re-inter-all`,
     `re-inter-cstring-neg`), `rewriteStarRegExp`, `rewriteAllRegExp`, and
     `rewriteMembership` (constants by `str-in-re-eval`, since Logos's
     `evaluate` does not reduce `str.in_re`; `re.none`, `re.allchar`,
     `(re.* re.allchar)`, unions, intersections, constant strings, ranges,
     complements, and `RE_CONCAT_TO_CONTAINS`), without simple consumption,
     inclusion, and some star and concatenation cases. Premises are proven by
     `str-in-re-eval` or `ArithEntail` when evaluation does not discharge
     them (`StringsRewriter.premiseProver`).
   - Fuzzing: 43.9% identical to cvc5 (from 27.6%), no semantic
     disagreements; Ethos accepts all proofs. (`fuzz.py` now gives each of
     cvc5's equivalence checks 2 seconds; 2 string checks time out.)
   - **String entailment** (`Telos/Strings/StringsEntail.lean`): cvc5's
     `componentContains` (with remainders), `stripConstantEndpoints`,
     `getMultisetApproximation` and `checkMultisetSubset`, over words as lists
     of code points (`find`, `rfind`, `overlap`, `hasOverlap`).
     `checkContains` rewrites `(str.contains a b)` with the full rewriter, as
     cvc5 does, so the strings rewriter is given one
     (`TheoryRewriter.strings rw`). The recursion is cut by depth
     (`theoryRewriterAt`, `stringsDepth = 3`: at depth 0 the strings rewriter
     has none). A premise that evaluation, `str-in-re-eval` and `ArithEntail`
     do not discharge, such as `(not (str.contains t s))`, is proven by the
     CPC proof of its rewrite to its value (`premiseProver`).
   - With it: `rewriteContains` (all cases but `CTN_NCONST_CTN_CONCAT`),
     `rewriteReplace`, `rewriteReplaceAll`, `rewriteIndexof` (without
     `IDOF_STRIP_SYM_LEN` and `IDOF_NORM_PREFIX`), `rewriteStrReverse`,
     `rewriteStrConvert`, `rewriteStrToInt`, `rewriteStringLeq`, and the
     eliminations of `str.<` and `str.is_digit`. The macros are certified as
     cvc5 elaborates them: `MACRO_STR_COMPONENT_CTN` by regrouping and
     `str-contains-concat-find`, `MACRO_STR_STRIP_ENDPOINTS` by regrouping into
     three components and `str-overlap-endpoints-ctn` (`-replace`,
     `-indexof`), `MACRO_STR_SPLIT_CTN` by `str-overlap-split-ctn`.
     Regrouping that splits a constant (`regroup`) is proven by rewriting the
     regrouped term back (`rewriteConcat`) and reversing that proof
     (`Proof.reverse`, `symm`). Cases that cvc5 itself leaves as proof holes
     (a trusted step) are left unchanged: `CTN_SPLIT` for a constant first
     argument, `REPL_SUBST_IDX`, `IDOF_STRIP_CNST_ENDPTS`, `STR_LEQ_ID`; so is
     `CTN_LEN_INEQ` unless `str-ctn-multiset-subset` proves it (cvc5 goes
     through `str-eq-len-false`, whose premise needs a proof by contradiction).
   - Two fixes found on the way: the matcher compared the bindings of a list
     variable that occurs twice with the seed of each occurrence, so rules
     such as `str-leq-concat-true` never matched with an empty list
     (`Binding.same`); and `Proof.emitChain` emitted unused `refl` steps for a
     congruence whose child did not change, so that the proof's last fact was
     not the rewrite.
   - Fuzzing: 65.4% identical to cvc5 (from 43.9%), 83.0% up to the
     orientation of equalities, no semantic disagreements; Ethos accepts all
     proofs. The other modes are unchanged.
   - Then: `stripSymbolicLength` strips part of a constant, as cvc5 does
     (the regrouping splits the constant: `regroup`), and stripping a whole
     string from the start gives `str-substr-empty-start`;
     `rewriteConcatRegExp` (`absorb` for `RE_CONCAT_EMPTY`, `aci_norm` for
     `RE_CONCAT_FLATTEN`, and `re-concat-merge`, `re-concat-star-repeat`,
     `re-concat-star-nullable1/2` and `re-concat-star-swap` one at a time);
     in `rewriteMembership`, `RE_EMPTY_IN_STR_STAR` (`str-in-re-eval`),
     `RE_CONCAT_PURE_ALLCHAR` (`str-in-re-sigma`), `RE_IN_CHAR_MODULUS_STAR`
     (`str-in-re-sigma-star`) and simple consumption (`str-in-re-consume`, whose
     result telos computes with CPC's own `$str_re_consume`);
     `RE_ANDOR_CONST_REMOVE` for the intersections cvc5 can prove
     (`re-inter-cstring`, `re-inter-cstring-neg`); and `str.<=` of two equal
     constants by evaluation. `RE_CHAR_IN_STR_STAR` and the other constant
     removals are proof holes in cvc5 and are left unchanged.
   - Fuzzing: 71.3% identical to cvc5 (3000 terms of depth 3), 92.3% up to the
     orientation of equalities, no semantic disagreements; Ethos accepts all
     proofs. The other modes are unchanged.
   - cvc5's proof holes found by fuzzing (`scripts/find-holes.py`) have
     reproducers in `test/cvc5-holes/`.
   - Then, with Logos `512983a8`, whose new rules cover most of those holes:
     `RE_ANDOR_CONST_REMOVE` in full, for intersections and unions, one removal
     at a time (`re-inter-const-elim`, `re-union-const-elim`), and
     `RE_INTER_CONST_CONST_CONFLICT` (`re-inter-const-const-conflict`);
     `RE_CHAR_IN_STR_STAR` (`re-char-in-str-star`); `STR_LEQ_ID`
     (`str-leq-id`); `CTN_SPLIT` for a constant first argument, one character
     at a time as in PR #13167 (`str-contains-cnst-split-leq-one`, and
     `str-contains-char` for the last); `CTN_REPL_LEN_ONE_TO_CTN` for
     `|z| <= 1` (`str-contains-repl-self-tgt-leq-one`); `CTN_STRIP_ENDPT` past a
     `str.from_int` (`str-contains-strip-from-int-pre/post`, the premise by
     `str-is-digit-elim`); `IDOF_LEN` (`str-indexof-len`);
     `IDOF_STRIP_CNST_ENDPTS` (one character at a time, as in PR #13167, by
     `str-indexof-strip-char-pre`); and `IDOF_STRIP_SYM_LEN`
     (`MACRO_STR_INDEXOF_STRIP_SYM_LENGTH` in PR #13167:
     `str-indexof-strip-prefix-len`, or `str-indexof-strip-sym-len` with cvc5's
     remaining index as its `m`). PR #13167 moves `IDOF_NORM_PREFIX`, which has
     no rule, to the extended rewriter.
   - Fuzzing: 73.3% identical to cvc5 (3000 terms of depth 3), 96.1% up to the
     orientation of equalities, 97.3% also up to the order of commutative
     arguments, no semantic disagreements (against `bab27e4f17`, where 48 of
     the other 82 are `IDOF_NORM_PREFIX`); Ethos accepts all proofs. The other modes are unchanged. Of the 15 reproducers in
     `test/cvc5-holes/`, telos now matches cvc5 on all but `idof-norm-prefix`
     (up to the orientation of equalities).
   - Then: `CTN_LEN_INEQ` certified as cvc5 proves it, by `str-eq-len-false`
     and `str-contains-leq-len-eq`, except for the premise
     `(= (= (str.len a) (str.len b)) false)`. cvc5 proves that by
     contradiction, in a scope; Logos's checker pushes only closed assumptions,
     and telos's terms have free variables (`Term.Var`), so telos uses
     `arith-eq-elim-int` and shows one conjunct false (`ctnLenIneq`). The
     rewrites that use it through `checkContains` follow (`RPL_NCTN`,
     `IDOF_NCTN`, …).
   - Then: `RE_IN_DIST_CHAR_STAR` (`str-in-re-concat-star-char`, the fixed
     length by CPC's own `$str_fixed_len_re`); `RE_IN_EVAL` for the empty
     string in a regular expression with variables (nullability); everything
     stripped from a substring in `CTN_STRIP_ENDPT` (`str-substr-ctn-contra`);
     `Word.rfind` as cvc5's `String::rfind` (the number of characters after
     the last match, which `stripConstantEndpoints` uses); the approximation
     `(+ n 1)` of `(str.len (str.from_int n))` in the order CPC's
     `$str_arith_entail_is_approx_len` expects; and the `RPL_CCTN` target with
     its constants merged.
   - Fuzzing against PR #13167: 74.0% identical to cvc5 (3000 terms of depth
     3), 98.6% up to the orientation of equalities, 99.9% also up to the order
     of commutative arguments, no semantic disagreements; Ethos accepts all
     proofs. The other 4 are `MACRO_STR_IN_RE_INCLUSION`, which cvc5 proves by
     contradiction in a scope (`re-inter-inclusion`); telos cannot push an
     assumption with its free constants (`Term.Var`, where Logos's parser makes
     declared constants `UConst`). At depth 4 (another seed, 3000 terms): 64.1%,
     95.2% and 100%.
   - Next: free constants as `UConst` (scoped proofs, then inclusion),
     `rewriteLoopRegExp`, inclusion
     (`rewriteViaMacroStrInReInclusion`, `rewriteViaMacroReInterUnionInclusion`),
     `RE_IN_DIST_CHAR_STAR`, and `CTN_NCONST_CTN_CONCAT`.
9. **Performance.** ~~Rewrite cache~~ (done: `Cache` in
   `Telos/Rewriter/Rewriter.lean`, for one call of `rewriteWith`, as cvc5 caches
   `rewriteTo`; children are rewritten in order and assembled by
   `Rw.congrList`). Sharing, cached hashes; a proof that children
   of well-typed nodes are well typed (removing the runtime check); generated
   program-equals-template lemmas for hot rules; normalizers (first
   `arith_poly_norm`) proven to produce steps the checker accepts, so that
   their steps need no run-time check.
   - Static steps share one interface, `StaticProc` (`Telos/Rewriter/Static.lean`,
     `Certified.static`, `TelosProofs/Static.lean`); `docs/theory-rewriters.md`
     says how to add one.
   - Static `arith_poly_norm`: done. `normalizeTerm` rewrites `n` to
     `arithNorm n` (`Telos/Arith/PolyNorm.lean`) by `StaticProc.arithNorm`,
     whose step Logos's checker never runs. It is justified in `verification/`:
     Logos's term order is a strict total order (`TelosProofs/TermOrder.lean`,
     per-constructor part generated by `scripts/gen-term-order.py`); Logos's
     normal form is canonical, normal forms of `Int`/`Real` terms are not stuck,
     and telos's `polyOf`/`Poly.toNode` preserve the value of a term
     (`TelosProofs/PolyNorm.lean`); so `[arith_poly_norm (= n (arithNorm n))]`
     meets `ProvesEq` (`TelosProofs/ArithNorm.lean`), and `Certified.equiv`
     covers the step. Printed proofs contain that step, so `--proof` is
     unchanged. The run-time side conditions (`ArithNormOk`) are a type query:
     the equation's SMT type is `Bool`, `n` is `Int` or `Real`, and an integer
     normal form has integer coefficients. On the arithmetic benchmark this
     replaces 12,738 checker runs (about 5.6µs each) by 1.7µs of side
     conditions: 1.14s to 1.06s.
   - Static `arith_poly_norm_rel`: done. The premise `(= (* cx x) (* cy y))` of
     the inequality and equality normalizations is justified statically when
     both sides have the same telos polynomial up to order (`ArithRelOk`,
     decided natively); only Logos's cheap `arith_poly_norm_rel` program (shapes
     and signs) runs, as a side condition (`StaticProc.arithRel`,
     `arithRel_provesEq`). Arithmetic benchmark: 1.06s to 0.89s, 15,290 more
     checker runs removed. Versus cvc5 on the same 3000-query script: telos
     1.15s, cvc5 0.30s (Booleans: 0.42s, 0.14s). Now the largest costs are
     translations and type queries (`types` 15%, checker read back and compare
     15%) rather than checking. To do: prove the typing side conditions
     statically, cache types and translations, template lemmas for RARE rules.
   - Congruence without type checks: under the built-in Boolean, equality and
     arithmetic operators (`Op.childrenTypedOfParent`), the driver no longer
     checks at run time that the children are well typed. `Certified.congr` and
     `congrArg` accept that condition instead, and `Certified.equiv` derives
     the children's typing from the parent's
     (`TelosProofs/ChildTyping.lean`, `children_wellTyped`). Other operators
     (`APPLY_UF`, `extract`) keep the check. Strategies' type queries (`isInt`,
     `theoryOf`) use `Node.typeHint`, a structural type that falls back to
     Logos's type checker; nothing proved depends on it. Arithmetic benchmark:
     0.89s to 0.76s; Booleans 0.27s to 0.22s. Remaining: checking the
     remaining RARE, `evaluate` and `aci_norm` steps (run, read back, compare:
     about 28%).
   - Profiling: `--profile` on `telos` and `telos-fuzz` prints where the time
     went (`Telos/Profile.lean`: probes on the checker's phases, per rule, on
     type queries, the RARE matcher and the arithmetic normal form);
     `scripts/profile.sh` is the standard benchmark. Baseline (3000 arithmetic
     terms of depth 4, 1.1s): running the checker 31%, of which
     `arith_poly_norm_rel` is 61%; comparing its result with the expected
     equation 9% and reading it back 7%; type queries 12% (260k, uncached);
     telos's polynomial normal form 4%; matching 1%; unprobed strategy and
     driver code most of the rest. No check is rejected.
10. ~~Proof output.~~ Done: `telos --proof` prints a CPC proof of
   `(= t (rewrite t))`, checked by Logos's checker before printing, and accepted
   by Ethos (`scripts/check-proofs.py`: 2000 of 2000 fuzzed terms). Open:
   proofs are not compacted (one `cong` per rewrite below an operator).
11. **Sets.** telos supports only what cvc5's `--safe-mode=safe` allows. For
    sets, that is the operators below: safe mode excludes `set.card`, the
    relations, `set.universe`, `set.complement` and comprehensions, and
    `set.map`, `set.filter`, `set.fold`, `set.all` and `set.some` have no CPC
    counterpart. `TheorySetsRewriter` is ported (`Telos/Theory/Sets.lean`,
    `test/examples/sets.smt2`).
    - Kinds `SET_SINGLETON`, `SET_UNION`, `SET_INTER`, `SET_MINUS`, `SET_MEMBER`,
      `SET_SUBSET`, `SET_CHOOSE`, `SET_IS_EMPTY`, `SET_IS_SINGLETON` and
      `SET_INSERT` (binary, as cvc5's type rule has it; `:right-assoc` in
      `Cpc.eo`), all spines. The empty set is a constant, `Const.emptySet T`
      (cvc5's `SET_EMPTY` is a constant kind), translated to
      `(as set.empty (Set T))` (`UOp1 set_empty`), which the proof printer
      writes with `as`.
    - 12 RARE rules are generated. The 8 whose premise is
      `(= x (as set.empty (Set T)))` (`sets-member-emp`, `sets-union-emp1`, …,
      `sets-eq-singleton-emp`) are applied when `x` is the empty set, with the
      premise by `refl`. Operations on two constant sets are computed and
      certified by `sets-eval-op`. Distinct constant sets are unequal by
      `distinct_values` and `false_intro`.
    - Set constants are cvc5's normal form,
      `(set.union (set.singleton c₁) (… (set.singleton cₙ)))` with
      `c₁ > … > cₙ`, in telos's term order (`SetsRewriter.isConstNode`).
      `Node.isConst` is unchanged; only the sets rewriter uses this.
    - Deviations: `(set.union s s)` and `(set.inter s s)` are left unchanged
      unless `s` is a constant. cvc5 rewrites them to `s` with a
      `TRUST_THEORY_REWRITE` step (`test/cvc5-trust/sets-*-self.smt2`). The
      membership of a constant in a constant set, and `set.is_empty` of a
      constant, go through the general rewrites, with the same results.
      Elements, arguments and equalities are ordered by telos's term order.
    - `set.is_singleton` of any other set is
      `(= A (set.singleton (set.choose A)))` (`sets-is-singleton-elim`), as in
      cvc5's current main.
    - Fuzzing (`scripts/fuzz.py --sets`, 3000 terms of depth 3), against cvc5
      main `9d7d9ee04b` (built 2026-11-17): 44.8% identical, 58.4% up to the
      orientation of equalities, 60.9% also up to the order of commutative
      arguments, no semantic disagreements. Most of the other differences are
      the order of set arguments, which cvc5 decides by node id, and the holes
      above. Ethos accepts all proofs (`check-proofs.py --fuzz 500 --sets`).
      The other modes are unchanged.

12. **Datatypes.** Inductive datatypes, as in cvc5's safe mode (no
    codatatypes, `match` or nullables), not yet parametric, and not yet tuples.
    `DatatypesRewriter` is ported (`Telos/Theory/Datatypes.lean`,
    `test/examples/datatypes.smt2`).
    - Representation, mirroring Logos: `TypeNode.datatype name decl`, with the
      block `decl` (`DtDecl`, `Dt`, `DtCons`: datatypes, constructors, field
      types, `typeRef` for the block's own datatypes), as Logos's
      `Term.DatatypeType`. Constructors and selectors are `Const.dtCons T i` and
      `Const.dtSel T i j`, the operators (`Op.node`) of `APPLY_CONSTRUCTOR`,
      `APPLY_SELECTOR`, `APPLY_TESTER` and `APPLY_UPDATER`, all spines, so their
      congruence needs no new proof. A nullary constructor is an
      `APPLY_CONSTRUCTOR` with no children, as in cvc5. Logos's datatypes have no
      constructor or selector names, so neither does `TypeNode`: the front end
      reads them from `declare-datatypes` (`DtNames`), for printing results and
      proofs.
    - Each rewrite is certified by the `dt-*` rule that takes the equation as
      its argument, with the result computed in telos: `dt-collapse-selector`,
      `dt-collapse-tester`, `dt-inst` (a tester for a nullary constructor is an
      equality), `dt-collapse-tester-singleton`, and `dt-cons-eq-clash` for
      clashing equalities (cvc5's `checkClash`). `dt-collapse-updater` never
      applies: its side condition takes `eo::len` of a list and counts the field
      from the wrong end, so cvc5's own proofs fail there (upstream request 9).
      telos certifies the updater rewrite by `dt-updater-elim`, then the tester,
      the `ite` and the selectors (`collapseUpdater`).
    - `Node.isConst` is cvc5's: constructors applied to constants are constants.
      The Boolean rewriter's `eq-cond-deq` (cvc5's `rewriteViaEqConstEq`) proves
      its premise `(= (= k z) false)` for datatype values by
      `dt-cons-eq-clash`, since `evaluate` does not decide it.
    - Term order: nullary constructors come after constants and before
      variables, as their node ids usually do in cvc5 (`(= nil x)`).
    - Fuzzing (`scripts/fuzz.py --datatypes`, 3000 terms of depth 3, over a list
      datatype and an enumeration), against cvc5 main `9d7d9ee04b`: 79.4%
      identical, all others identical up to the orientation of equalities (node
      ids of compound terms), no semantic disagreements. Ethos accepts all
      proofs (`check-proofs.py --fuzz 500 --datatypes`). The other modes are
      unchanged.

## Working conventions

- Small commits; each commit builds both projects and passes
  `scripts/check-hygiene.sh`.
- Never weaken a theorem statement to make a proof go through. If an obligation
  fails, stop and report.
- When a Logos statement is awkward to use, write an adapter lemma here and note
  it as an upstream candidate; do not edit Logos from this repository.
