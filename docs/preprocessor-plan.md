# Plan: a verified preprocessor

telos's rewriter is verified (`Telos.rewrite_correct`) and matches cvc5's
rewriter by differential testing. The next step is a **verified preprocessor**
that matches cvc5's: given an SMT-LIB script, produce the assertions cvc5
prints with `-o post-asserts`, with a machine-checked proof that they mean the
same as the input. It builds on the rewriter, which keeps its interface: the
preprocessor calls `rewrite` and its `Rw` certificates, and adds passes around it.

The scope is that of `design.md` ("Scope: cvc5's safe mode"), and the target
configuration is cvc5 with proofs: every pass that runs then has proof support.

## The target

`ProcessAssertions::apply` (`src/smt/process_assertions.cpp`) runs a fixed
sequence of passes; most are off by default. With safe mode and proofs, on the
theories in scope, the passes that run are:

| Pass | When | What it does | CPC justification (cvc5) |
|---|---|---|---|
| `apply-substs` | always | expands `define-fun`s (beta reduction) | `beta-reduce`, `cong` |
| `rewrite` | always (twice) | the rewriter on each assertion | as telos's rewriter |
| `quantifiers-preprocess` | quantified logics | `QuantifiersRewriter::preprocess` | rewrites |
| `non-clausal-simp` | not QF_SAT (`simplification=batch`) | Boolean propagation over the top-level assertions (`CircuitPropagator`); learned literals solved by the theories (`ppAssert`) into substitutions `x := t`; the substitutions applied, and the assertion rewritten | `eq_resolve`, `cong`, `trans`, theory solving steps |
| `static-learning` | default on | theory lemmas implied by each assertion (`ppStaticLearn`: arith, UF, BV) | theory lemmas |
| `repeat-simp` | QF_AUFBV | `non-clausal-simp` again | as above |
| `static-rewrite` | always | `ppStaticRewrite` (arith, BV, strings, datatypes, builtin) | theory rewrites |
| `theory-preprocess` | always | `TheoryPreprocessor`: term formula removal (`ite` to purification skolems, with lemmas), the theories' `ppRewrite` (arith's `OperatorElim` for `div`, `mod`, `to_int`, `is_int`, …; strings, sets, datatypes, arrays, BV, UF), then rewriting | `arith_reduction`, `ite_eq`, `skolem_intro`, rewrites |

Out of scope: unconstrained simplification (QF_AUFBV without models). It
preserves only satisfiability and has no proofs, so cvc5 disables it with
proofs. Also out: incremental solving (`push`/`pop`), and the passes that are
off by default or outside safe mode (`ite-simp`, `miplib-trick`,
`learned-rewrite`, `bv-to-bool`, `sort-inference`, …).

`-o post-asserts` prints a benchmark: `set-logic`, then `define-fun`s for the
top-level substitutions (the solved variables and the defined functions),
declarations of the remaining symbols and of the skolems (`@purify_k`), the
assertions (including `true` placeholders for assertions that were solved),
and `check-sat`. For example, for

```smt2
(declare-const x Int) (declare-const y Int) (declare-const a Bool)
(declare-fun f (Int) Int) (define-fun g ((z Int)) Int (+ z 1))
(assert (= x (+ y 1)))
(assert (or a (> (f x) (g y))))
(assert (and a (< (ite a x y) 10)))
(assert (> (div y 3) (mod x 2)))
```

cvc5 solves `x := (+ 1 y)` and `a := true`, so the second assertion becomes
`true`. It turns `(ite a x y)` into `x` and then into `(+ 1 y)`, and replaces
`div` and `mod` by skolems with their defining bounds:

```smt2
(define-fun a () Bool true)
(define-fun x () Int (+ 1 y))
(declare-fun @purify_2 () Int)  (declare-fun @purify_3 () Int)
(assert (not (>= y 9)))
(assert (not (>= (+ y (* (- 2) @purify_2) (* (- 1) @purify_3)) (- 1))))
(assert (>= (+ y (* (- 2) @purify_2)) (- 1)))  ...
```

(the `(assert true)` placeholders are omitted here.)

## The theorem

The skolems are what make an *equivalence* possible. In CPC, a purification
skolem is the term `(@purify t)`, and Logos gives it the value of `t`
(`__smtx_model_eval__at_purify` is the identity). The other skolems that
preprocessing introduces in scope are also terms with a meaning (choice terms,
`@int_div_by_zero`). So telos represents skolems as those terms internally and
prints them as `@purify_k` declarations.

As in cvc5, a skolem is its own kind of node, `Node.skolem id cacheVals`
(cvc5's `SKOLEM`, `mkSkolemFunction(id, cacheVals)`, with `SkolemId` mirroring
cvc5's), not an operator application: it is atomic, so rewriting, congruence and
substitution do not enter its cache values, with no special cases. Its meaning
is its CPC term (`SkolemId.eoShape` in `ToEo.lean`): `(@purify t)` for
`.skolem .PURIFY #[t]`. Function skolems are applied with `APPLY_UF`, as in
cvc5's `OperatorElim`: `(div x 0)` becomes
`APPLY_UF (.skolem .INT_DIV_BY_ZERO #[]) #[x]`, printed `(@int_div_by_zero x)`,
whose argument is a child. The functions that must see a skolem's cache values
handle `skolem` explicitly: `toEo`, `vars` (for the solved-form condition, a
symbol occurs in a skolem's cache values), `typeHint`, and printing. The preprocessed assertions then mean,
in every model, what the input means, given the definitions:

```lean
theorem Telos.preprocess_correct (s : Script) (h : s.WellTyped) :
    let r := preprocess s
    ∀ M, (∀ a ∈ s.assertions, M ⊨ a) ↔
         (∀ b ∈ r.assertions, M ⊨ b) ∧ (∀ (x, t) ∈ r.defs, M ⊨ (= x t))
```

`r.defs` is in solved form: no defined symbol occurs in `r.assertions` or in a
later definition. So the output is satisfiable iff the input is, a model of the
output extends to one of the input by the definitions (which is cvc5's model
reconstruction), and an unsatisfiable output means an unsatisfiable input.

## Architecture

The rewriter certifies each step as a CPC proof of `(= t s)`, and one theorem
turns any certified rewrite into an equivalence. The preprocessor does the same
at the level of assertion lists.

- **State.** `Pipeline`: the assertions (an array, with cvc5's positions and
  `true` placeholders, so output order matches), the definitions (cvc5's
  `TopLevelSubstitutions`), and the skolems introduced. The invariant is the
  theorem's statement, between the input and the current state.
- **Certified steps.** A step changes the state, with a CPC proof, checked by
  Logos from the empty state, of one of these closed formulas:
  - `(= a b)`: replace assertion `a` by `b`. This is any `Rw` (rewriting,
    static rewrites, theory preprocessing rewrites).
  - `(=> (and d₁ … dₙ) (= a b))`: replace `a` by `b` using definitions
    `dᵢ` (substitution). It is proved with `assume-push`/`scope`, as Logos
    takes closed assumptions.
  - `(= a (= x t))`, with `a` then moved to the definitions as `x := t` (a
    theory solving a learned literal, `ppAssert`). The definition must be
    solved: `x` not in `t`, nor in the definitions.
  - `(=> a l)`: add an implied lemma `l` (static learning, learned literals).
  - `l` valid: add a lemma `l` (skolem lemmas: `div` bounds, `ite` cases).

  One soundness theorem per form, from Logos's checker soundness (the
  `LogosFacts` already used by the rewriter, plus the semantics of `=>`, `and`
  and `=`), shows that the step preserves the invariant. A pass is then a
  composition of certified steps, and needs no proof of its own, as with theory
  strategies today.
- **Passes** are strategies, as theory rewriters are: they mirror cvc5's C++
  (which literal to solve, which variable, which lemma, in which order) and are
  tested against it, not proved.
- **Front end.** Full scripts: `declare-fun`, `declare-const`, `define-fun`,
  `assert`, `set-logic`, `check-sat`, and the datatype and sort declarations
  already read. Assertions are read through Logos's parser (as `assume`s), as
  `simplify` terms are today.
- **Output.** A post-asserts printer, and optionally the CPC proof of the whole
  preprocessing: input assertions as `assume`s, the steps, and the output
  assertions and definitions as conclusions, checked by Ethos as the rewriter's
  proofs are.

## Status

Phase 1 is done, without the definitions, as `define-fun`s are macros
(expanded when the script is read, not recorded or printed). The pipeline is one
node, the conjunction of the assertions, as a certified rewrite (`Rw`) of the
conjunction of the input assertions and `true` (`Telos/Preprocess/Pipeline.lean`).
So the theorem, `Telos.preprocess_correct`, is `Certified.equiv` and needed no
new proof, and so far the step forms are those of rewrites: `aci_norm` (splitting
conjunctions, `push_back`), congruence below `and` (the `rewrite` pass) and
`absorb` (conflicts). Scripts are read with `assert` and `check-sat`
(`Telos/Frontend/Script.lean`, non-incremental), and printed as cvc5 does
(`Telos/Frontend/PostAsserts.lean`, `telos --post-asserts`). `scripts/fuzz-pp.py`
compares with `cvc5 -o post-asserts --simplification=none --no-static-learning`:
on 150 random benchmarks of 1 to 4 assertions, the Boolean and UF ones are all
identical up to the orientation of equalities. In the other modes a third to
three quarters differ, by the passes cvc5 always runs: `theory-preprocess`
(`ite` removal, `to_int` and `div` elimination, datatype updaters,
constructor equalities split into conjunctions) and `static-rewrite` (arith
normalizes equalities, `rewriteEqualityExt`). These are phase 2.

Phase 2 is under way. `static-rewrite` is ported for arithmetic and datatype
equalities and `distinct`. `theory-preprocess` is ported with term formula
removal (non-Boolean `ite`s and Boolean terms inside terms purified, with
their lemmas) and arithmetic's `ppRewrite` (`OperatorElim`: `div`, `mod`, `/`,
their total versions, `to_int`, `is_int`, `abs`), in
`Telos/Preprocess/Passes/TheoryPreprocess.lean`. The new steps are still
rewrites (`Telos/Preprocess/SkolemSteps.lean`): `t → (@purify t)` by
`skolem_intro`, and a lemma `L` as `true → L`, proven by `ite_eq`,
`skolem_intro` or `arith_reduction` and `and_elim` (cvc5's `OperatorElim`
lemmas are the conjuncts of `arith_reduction`), then `true_intro`; lemmas take
the place of `true` conjuncts added after the last assertion. So the theorem
still needed no new proof. Skolems are printed as cvc5 prints them
(`@purify_k`, `@int_div_by_zero_k`, declared), numbered by occurrence.

Then the `ppRewrite` of bit-vectors (`UltAddOne`, and the overflow predicates
eliminated, `Telos/Preprocess/Theory/BVPreprocess.lean`) and of datatypes
(updaters as an `ite` on the tester, by `dt-updater-elim`;
`DatatypesPreprocess.lean`). Tuple updaters are blocked on Logos, which does not
translate a tester on the `tuple` constructor (`upstream-requests.md`,
request 9); selectors stay as they are (cvc5's shared selectors have no CPC
term, and cvc5 prints them as the selectors). On the way: `static-rewrite`'s
`MACRO_DT_CONS_EQ` now splits tuple equalities (the fields were those of the
binary `TUPLE` node), and the rule matcher takes a premise after the premises
that bind its variables (`bv-ult-add-one`). Strings: `ppRewrite` purifies
`str.from_code` with its eager reduction (`string_eager_reduction`), and
`static-rewrite` applies `rewriteStrEqualityExt`
(`Theory/StringsStaticRewrite.lean`): `EQ_NCTN` (`str-eq-ctn-full-false*`),
`EQ_NFIX` and `STR_EQ_UNIFY` (constants split at the ends with `regroup`, then
`str-concat-unify`/`-clash`), and the `str.replace` cases (`str-eq-repl-*`);
cvc5 trusts this step and elaborates it, telos certifies each case. Not ported:
the `str.substr` cases and the length-based unifications. Sets and UF have no
`ppRewrite` on telos's input; arrays' (`select` over `store` and store
reordering at disequal indices) is what the rewriter does without
non-clausal simplification's facts. On 150 benchmarks, strings went from 28 to
9 differences.

`fuzz-pp.py` compares up to the numbering of skolems and up to Int/Real casts
(cvc5's post-asserts prints its mixed arithmetic without `to_real`, where its
`simplify`, which the rewriter matches, prints them). On 150 benchmarks per
mode: UF all agree up to orientation; arith 146 agree (64 only up to casts),
4 differ; mixed 137 agree, 13 differ; bit-vectors 145 agree, 5 differ;
datatypes 111 agree, 39 differ (37 of them by tuple updaters). The remaining differences come
from cvc5's node ids, which order skolems by creation: the order of two
skolems in a sum or an equality, and of terms built during preprocessing
against skolems, and so of the lemmas that follow from them.

Performance: the pipeline's reorganizations of the whole conjunction
(splitting the input's conjunctions, adding `true` conjuncts for lemmas) were
`aci_norm` steps, which Logos checks in cubic time (`list_setof` at every level
of the nested conjunction); they took seconds on a few hundred assertions. They
are now `andReorg` (`Telos/Preprocess/Conjunctions.lean`): a CPC proof by
`assume_push`, `and_elim`, `and_intro`, `scope` and resolution, whose steps are
list walks, still checked by Logos's checker, so it needed no proof. Lemmas are
split by checking their own small proofs (`splitLemma`), and set in one
congruence step. On Certora QF_UFNIA benchmarks, an 87KB file went from 80s to
1.2s and a 36KB one from 14s to 0.6s; 0.13MB with 400 assertions takes 14s,
growing about linearly, mostly in the rewriter's type checks (Logos's
translation and typing of every node checked) and the checking of the two
`andReorg` steps.

Phase 3 is under way: non-clausal simplification
(`Telos/Preprocess/Passes/NonClausalSimp.lean`) with the circuit propagator
(`CircuitPropagator.lean`), learned literals solved by the theories'
`ppAssert` (Booleans, the default one, arithmetic) into substitutions, constant
propagations, and learned literals re-added, as cvc5 does. The substitutions are
cvc5's top-level substitutions: they are stored in the pipeline as its last
conjunct (the definitions slot, `(= x t)` with `t` substituted to a fixed point)
and printed as `define-fun`s. The theorem is unchanged: the conjunction it
relates to the input now includes the definitions. The pass is one CPC proof of
`(= C C')` (`ConjProof.lean`): assuming `C`, the propagator gives each
assignment a fact (the parent's clause, `not_and`, `ite_elim1`, `equiv_elim2`,
… or the CNF rules, resolved against the children's facts), each solved
literal its equation, and each assertion its simplification (congruence with
the equations at the leaves, then rewriting); assuming `C'`, the old conjuncts
follow from the new ones and the definitions; resolution gives the equality.
With cvc5's simplification on (`fuzz-pp.py` no longer passes
`--simplification=none`), on 150 benchmarks per mode: the default and UF modes
agree on all, arith on 144, bit-vectors 142, arrays 145, sets 145, strings 135.
Not ported: bit-vector extract solving (`BvPpAssert`), static learning, and
`repeat-simp`. Performance: the pass is now semantic and triangular steps, each
checked in time linear in the size of the terms as DAGs (`ncsSteps`): the
learned literals are added by `SemProc.learn` (`Telos/Core/Learn.lean`), whose
side condition replays the trace of the propagator (`CircuitPure.lean`), and
the substitutions are applied by two `Certified.tri` steps (`Telos/Core/Tri.lean`;
two, since learned literals are simplified by the substitutions found before
them, and the definitions by those found after them), with `SemProc.reorg`
steps between. Both are proven sound (`verification/TelosProofs/Core/Learn.lean`,
`Tri.lean`). On Goel's hardware QF_UF benchmarks of about 115KB the pass went
from 8–11s to under a second (the same output), and on the largest (`collision`)
from over 60s to 7.7s; what remains is the rewriter's CPC checks of steps on the
substituted terms, whose translations are trees. The rewriter's cache is kept
for the whole pass (`rewriteCertCached`). Substitution goes below every operator
kind: by congruence, which holds model by model where the entries hold
(`CondEquiv`) and needs the children of a well-typed application to be well
typed (`ChildTyping.lean`); into the bodies of quantifiers (`JustKind.body`,
`QuantCong.lean`: the entries are closed, so they hold whatever the values of the
bound variables); and below `distinct` (`DistinctCong.lean`). The CPC proof of
the pass (`ncsProof`) remains the fallback, for conflicts, for definitions that
are not ground (with `str.++`, whose nil depends on the type, or a quantifier),
and for substitutions below applications of terms other than declared functions,
constructors and selectors. `--simplification=none` turns the
pass off. Output is printed with `let`, as cvc5's default `--dag-thresh=1`.

## Phases

Each phase ends with fuzzing and benchmark agreement against cvc5, with the
passes not yet ported switched off on cvc5's side. For example,
`--simplification=none --no-static-learning` leaves only rewriting and theory
preprocessing.

1. **Pipeline, theorem, front end, printer.** `Pipeline`, the certified step
   forms and their soundness theorems, `preprocess_correct` for a pipeline of
   `apply-substs` and `rewrite`, scripts in, post-asserts out. Target: cvc5 with
   every optional pass off.
2. **Theory preprocessing.** `TheoryPreprocessor` and term formula removal
   (`ite` purification and its lemmas; their order and placement after the
   last assertion), arith `OperatorElim` (`div`, `mod`, `to_int`, `is_int`,
   division by zero), then the other theories' `ppRewrite`, and `static-rewrite`.
   Skolem printing as `@purify_k`, compared up to renaming.
3. **Non-clausal simplification.** `CircuitPropagator` (top-level Boolean
   propagation, learned literals), theory solving (`ppAssert`: Boolean
   variables, arith's linear equations and its choice of variable, BV, arrays,
   sets), the substitution map (composition, application, re-rewriting), and
   learned literals added back. This is the largest phase and the one most
   sensitive to order. Then `repeat-simp` for QF_AUFBV.
4. **Static learning.** `ppStaticLearn` for arith, UF and BV.
5. **Quantifiers preprocessing.** `QuantifiersRewriter::preprocess` for
   quantified logics.

## Testing

- **Differential, by pass.** `scripts/fuzz-pp.py`: random scripts (several
  assertions over the existing term generators, with equalities that invite
  solving, `define-fun`s, and `ite`, `div` and `mod` terms), through telos and
  through `cvc5 -o post-asserts` with the same passes on. Compared up to the
  names of skolems, the order of `define-fun`s (cvc5 prints them from a hash
  map), and the orientation of equalities, as the rewriter's fuzzing is.
- **Semantic.** cvc5 checks that the two outputs, with their definitions, are
  equivalent, as the rewriter's fuzzing does for terms.
- **Benchmarks.** The SMT-LIB benchmarks in `~/benchmarks/smt-lib-2026`, by
  logic, as a match rate per logic.
- **Proofs.** Ethos checks the printed preprocessing proofs.

## Decisions to make

- **Exactness.** Whether to match the `(assert true)` placeholders and the
  positions of lemmas exactly. The proposal is yes, as they are part of
  cvc5's pipeline semantics, and skipping them would hide ordering bugs.
- **Definitions in the theorem.** The statement above includes them. The
  alternative, equisatisfiability only, is weaker and would also admit
  unconstrained simplification. The proposal is the equivalence, leaving
  unconstrained simplification out.
- **Skolem naming.** cvc5's `@purify_k` numbers come from its skolem
  manager. The proposal is to compare up to renaming rather than replicate the
  numbering.
- **Order-sensitive ports.** Non-clausal simplification depends on cvc5's
  traversal and hash orders in places. Where cvc5's choice depends on node
  ids, telos uses its term order, as the rewriter does, and fuzzing compares up
  to it.

## Risks

- `CircuitPropagator` and the substitution map are subtle (composition,
  occurs checks, cycles), and cvc5's output depends on their exact behaviour.
- Logos's checker takes only closed assumptions. Substitutions under
  definitions over declared constants are closed, but anything under binders
  (quantified assertions) needs the assumption-free proofs used for the
  quantifier rewriter.
- Proof size and checking time: certifying every substitution application
  with a scoped proof per assertion may be slow on large benchmarks. Static
  checking, as for `arith_poly_norm_rel`, may be needed for the common steps.
