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
soundness does. A cold build of `verification/` therefore compiles every rule
proof in Logos (hours on CI; cached afterwards).

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
result)))`, the steps, and `false` by `contra`. It checks with
`ethos --include=Cpc.cached.eo` and with Logos. A bound variable outside its
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
- `Certified.lean`: `Certified.equiv`, from Logos's checker soundness.
- `Driver.lean`: `rewriteWith_sound`, for any theory rewriters: the driver's
  result is certified, so this is an instance of `Certified.equiv`.
- `Axioms.lean`: the axiom audit (`TRUSTED.md`).

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
   in `TelosTests/Bool.lean`). Open: the equality rewriting of the other
   theories (cvc5's builtin and UF rewriters: `(= x x)`, orientation, constants).
5. **Front end and fuzzing.** The `telos` executable reads SMT-LIB scripts of
   `(simplify t)` queries through Logos's parser (`Telos/Frontend.lean`).
   `telos-fuzz` (random Boolean terms over three Booleans and two integer
   equalities) and `scripts/fuzz.py` compare with cvc5's `(simplify t)`. On 6000
   terms of depth 4: about 94% identical to cvc5, every other result identical up
   to (or caused by) the orientation of equalities, and no semantic
   disagreements. To do: `define-fun`, and fuzzing in CI.
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
     `arith-is-int-elim-to-real`), and `to_real` removed from both sides of `/`
     (`arith-div-elim-to-real`).
   - Fuzzing (`scripts/fuzz.py --arith`, 3000 terms of depth 4, including
     `div`, `mod`, `abs`, `to_int` and `is_int`): 83.5% identical to cvc5,
     92.7% up to the orientation of equalities, no semantic disagreements.
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
   - To do: the extended operators (`int.pow2`, `int.log2`, `iand`,
     transcendentals), then bit-vectors. Bit-vectors are where `bv_poly_norm`
     comes in.
7. **Performance.** Rewrite cache, sharing, cached hashes; a proof that children
   of well-typed nodes are well typed (removing the runtime check); generated
   program-equals-template lemmas for hot rules; normalizers (first
   `arith_poly_norm`) proven to produce steps the checker accepts, so that
   their steps need no run-time check.
   - Profiling: `--profile` on `telos` and `telos-fuzz` prints where the time
     went (`Telos/Profile.lean`: probes on the checker's phases, per rule, on
     type queries, the RARE matcher and the arithmetic normal form);
     `scripts/profile.sh` is the standard benchmark. Baseline (3000 arithmetic
     terms of depth 4, 1.1s): running the checker 31%, of which
     `arith_poly_norm_rel` is 61%; comparing its result with the expected
     equation 9% and reading it back 7%; type queries 12% (260k, uncached);
     telos's polynomial normal form 4%; matching 1%; unprobed strategy and
     driver code most of the rest. No check is rejected.
8. ~~Proof output.~~ Done: `telos --proof` prints a CPC proof of
   `(= t (rewrite t))`, checked by Logos's checker before printing, and accepted
   by Ethos (`scripts/check-proofs.py`: 2000 of 2000 fuzzed terms). Open:
   proofs are not compacted (one `cong` per rewrite below an operator).

## Working conventions

- Small commits; each commit builds both projects and passes
  `scripts/check-hygiene.sh`.
- Never weaken a theorem statement to make a proof go through. If an obligation
  fails, stop and report.
- When a Logos statement is awkward to use, write an adapter lemma here and note
  it as an upstream candidate; do not edit Logos from this repository.
