# Writing a theory rewriter

This is the guide for porting another of cvc5's theory rewriters to telos (strings,
bit-vectors, …). It covers what a rewriter must provide, which parts are
trusted, how to test it, and how to make a hot part of it faster without running
Logos's checker. `docs/design.md` explains why the design is this way; this
document says what to do.

## The contract

Every rewrite telos returns is equivalent to its input
(`Telos.rewrite_correct`). A theory rewriter gets this **without writing any
proofs**: it builds each rewrite out of CPC steps, which Logos's checker
validates when the rewrite is built (`Certified.step`), or out of steps whose
acceptance is proved once in `verification/` (`Certified.static`).

So the strategy code, which decides *what* a node rewrites to, is untrusted. A
bug in it can make telos miss a rewrite or differ from cvc5, but never return a
non-equivalent node. Match cvc5 as closely as possible. Agreement is tested by
differential fuzzing, not proved.

## The parts of a theory

| Part | File | Trusted? |
|---|---|---|
| Operator kinds | `Telos/Node/Kind.lean` (`Kind`, `Kind.theoryId`) | no |
| CPC form of each kind | `Telos/Node/ToEo.lean` (`Kind.eoShape`) | **yes, specification** |
| Reading CPC terms back | `Telos/Node/OfEo.lean` | no |
| Printing | `Telos/Node/Print.lean` | no (not covered by the theorem) |
| Rule table | `scripts/gen-rules.py` → `Telos/Rules/Generated.lean` | no |
| The rewriter | `Telos/Theory/<Theory>.lean` | no |
| Registration | `Telos/Rewrite.lean` (`theoryRewriter`) | no |
| Static steps (optional) | `Telos/<Theory>/…` below `Telos.Rewriter.Certified` | no; proved in `verification/` |

### New kinds

1. Add the kind to `Kind` and its theory to `Kind.theoryId`.
2. Add its CPC shape to `Kind.eoShape` (`spine` with an arity, `rightAssocNil`,
   …). This is the **specification**: it gives the node its meaning. Copy how cvc5
   prints the kind in CPC exactly, and review it like a definition, not like
   code. Each shape's congruence is proved once (`TelosProofs/Congruence.lean`),
   so a new kind with an existing shape needs no proof. One exception: a
   `rightAssocNil` operator with a typed nil (like `bvand` or `bvadd`) must also
   be listed in `AppShape.isChildCongruent` (only `+` and `*` are now), with its
   case in `Congruence.lean`. A new shape also needs its case in
   `Congruence.lean` (trivial if it is not child-congruent), and the proof
   printer (`Telos/Proof/Eunoia.lean`) must print it so that Logos's parser
   reads it back as the same term: check with `scripts/check-proofs.py`, which
   fails when proofs are missing. `distinct`, an operator applied to a list
   built from its arguments, is the example.
3. Read it back in `Node.ofEo`, print it in `Print.lean`, and map its Eunoia
   operator in `scripts/gen-rules.py` (`KINDS`). Then regenerate the rule table
   (`python3 scripts/gen-rules.py`), which picks up every RARE rule whose
   left-hand side now uses only known kinds. An indexed operator goes in
   `INDEXED`, with its number of indices, and an n-ary one in `NARY`.
   `python3 scripts/gen-rules.py --report` lists the rules skipped, and why.
   Rules whose left-hand sides have integer parameters (indices, widths, `@bv`
   literals) are not covered by the fresh-variable self-test
   (`TelosTests/Rules.lean`), so test them on concrete terms.
4. Optionally add the kind to `Op.childrenTypedOfParent`
   (`Telos/Rewriter/Certified.lean`). Then the driver skips the run-time check
   that its children are well typed. This needs the kind's case in
   `verification/TelosProofs/ChildTyping.lean`: an application with an SMT type
   has arguments with SMT types. That is short for most operators, using the
   kind's typing rule. Leave the kind out for operators where it fails, such as
   partial applications or user functions.

## Writing the rewriter

A rewriter is a `TheoryRewriter` (`Telos/Rewriter/Rewriter.lean`): `preRewrite`
and `postRewrite`, each `(n : Node) → RewriteResponse n`, as in cvc5. A response
is a status (`REWRITE_DONE`, `REWRITE_AGAIN`, `REWRITE_AGAIN_FULL`, with cvc5's
meanings), the result, and its certificate. The driver (`rewriteWith`) handles
children, fuel and theory changes. Follow the cvc5 source function by function,
and say in comments which function each part ports and where it differs.

Build rewrites with the combinators of `Telos/Theory/Common.lean`. Each returns
`Option (Rw n)`, which is `none` when the step does not apply or the checker
rejects it:

- `byRule "rule-name" n`: a RARE rule. The generated matcher finds the rule's
  arguments, and Logos computes the right-hand side. You never write the result.
- `byRuleWithPremises r args premiseSteps n`: a rule whose premises need steps.
- `byEvaluate n`: `n` to its value (constant folding).
- `checkBy r n m`: telos computes `m`, and a rule taking `(= n m)` as its argument
  (`aci_norm`, `arith_poly_norm`, …) validates it. This is how results of
  unverified algorithms are certified.
- `Rw.next`, `Rw.next?`, `Rw.congrArg`, `firstOf`: chain steps, rewrite below
  the top, try alternatives.
- For a rule whose `:requires` computes the right-hand side with a Logos
  program (`bv-bitwise-slicing`, `bv-repeat-elim`), call that program from Lean
  to get the result, read it back, and `checkBy` the rule (`BvRewriter.byProgram`).
- A premise that cvc5 decides by rewriting (like `mkEqNode` for array
  indices) can be proven the same way: give the theory rewriter a rewriter
  (`TheoryRewriter.arrays` takes one), rewrite the premise's term, and put the
  CPC proof of that rewrite (`Proof.emitProof`, `Step.toCmd`) before the rule
  step, which cites its last fact (`ArraysRewriter.byRuleAfter`).
- A macro rewrite of cvc5 (a normalization proven by several CPC steps) can be
  certified by a short search over the steps its elaborator uses, from the input
  towards cvc5's result (`BvNorm.reach`). If none is found, keep the input.

Rules of thumb:

- **Never assume a step applies.** Handle `none`: keep the result so far, or
  fall back. A rejected step costs only a missed rewrite.
- **Strategy helpers need no proofs.** Use `Node.typeHint` (a structural type,
  cheap) rather than `Node.getType` (a Logos type check, which translates the
  node) for decisions. Use `Node.lt` for orders. Anything a strategy computes
  only affects *which* step is tried.
- **Rewrites to other kinds** should usually return `REWRITE_AGAIN_FULL`, as cvc5's
  `returnRewrite` does.
- Register the rewriter in `theoryRewriter`.

## Testing and measuring

- `test/examples/<theory>.smt2` with `.expected`: examples, run in CI. Use
  `(simplify t)` queries.
- Compare with a recent build of cvc5's main branch, not a release: cvc5's
  rewriter changes, and telos ports the current one. `fuzz.py` prints the
  version it compared with.
- `FuzzMain.lean` generates random terms. Add the theory's operators to it, and
  to the declarations in `scripts/fuzz.py`. Then
  `python3 scripts/fuzz.py --cvc5 PATH` (or `CVC5=PATH`) reports the agreement
  with cvc5 and any
  semantic disagreement (which would be a bug in Logos or cvc5). Run it with a
  few thousand terms before and after each change; report the rates in
  `docs/design.md`.
- `python3 scripts/check-proofs.py --fuzz 500` checks printed proofs with Ethos.
- `bash scripts/profile.sh` and `--profile` show where the time goes, per checker
  phase and per rule (`Telos/Profile.lean`). Add probes (`Profile.time`) only in
  untrusted code.
- `bash scripts/check-hygiene.sh`, `lake build`, and `lake -d verification build`.

## Making a hot step static

When the profile shows one rule dominating, usually a normalization rule like
`arith_poly_norm`, its steps can be justified by a theorem instead of a checker
run. The procedure is then computed natively, and the CPC step is only printed.
Do this only for hot steps: it costs a proof.

The interface is `StaticProc` (`Telos/Rewriter/Static.lean`). To add a procedure:

1. Its code, in a module below `Telos.Rewriter.Certified` (like
   `Telos/Arith/PolyNorm.lean`), and a decidable side condition. Keep the side
   condition cheap and decide it at run time. Typical parts: the terms have the
   expected types, and a fast native check such as two polynomials being equal.
2. A `StaticProc` constructor, its `Ok` case (the side condition) and its `cmds`
   case (the CPC commands the step stands for, printed in proofs).
3. In the theory rewriter: `if h : decide (…) then some ⟨m, .static p h (.refl m)⟩`
   `else` the checked step, as a fallback.
4. In `verification/`, the case of `StaticProc.provesEq`
   (`TelosProofs/Static.lean`): the side condition implies
   `ProvesEq (p.cmds n m) n m`, that is, Logos's checker accepts the commands.

For a normalization rule (`= a b` accepted when Logos's normal forms of `a` and
`b` agree), the proof has the shape of `TelosProofs/PolyNorm.lean`:

- **Logos side, once per rule:** read Logos's normal-form terms as values in a
  mathematical structure (polynomials, for arithmetic). Show that its operations
  compute the matching operations on values, that its outputs are well formed,
  and that well-formed outputs with equal values are equal terms (canonicity;
  this needs `TelosProofs/TermOrder.lean`, the order laws of `native_tcmp`). Also
  show that its normal form of a well-typed term is not stuck.
- **telos side, once per algorithm:** telos's procedure preserves the value. Any
  data structure or algorithm can be used, as long as this can be shown.
- **Glue:** run the one or two commands symbolically from the empty state and
  check `ProvesEq` (`arithNorm_provesEq_of_typeof`), getting the Eunoia type from
  the SMT type with Logos's `eo_typeof_eq_of_smt_type_eq`.

Lessons from the arithmetic port:

- The proof printer writes indexed operators with their indices as leading
  arguments, `(extract 1 0 x)`, as the signature does; Ethos rejects
  `((_ extract 1 0) x)`. The empty bit-vector is `@bv_empty`.
- Instances that Lean derives for mutual or nested inductives (`Ord`, `BEq` on
  `Term` and `Node`) are **opaque**: nothing about them can be proved. In code
  you want to reason about, compare with `decide (a = b)` (from `DecidableEq`),
  not `==`. Logos's term order is transparent (`termCmp`).
- Avoid `partial def` in code you want to reason about. Use well-founded
  recursion over `sizeOf`, with list patterns (`⟨[a, b]⟩`) rather than array
  literals (`#[a, b]`), which break the generated equation lemmas.
- Keep `let`-bound helper functions at top level, so that each has its own lemmas.
- The proofs build with `-DwarningAsError=true`. Deprecated names and unused
  `simp` arguments are errors.
- Measure before and after on the same build (switch the static path off for the
  "before") and record the numbers in `docs/design.md`.

## Checklist for a new theory

- [ ] Kinds, `eoShape` (reviewed as specification), `ofEo`, printing,
      `gen-rules.py` mapping; rule table regenerated.
- [ ] `TheoryRewriter` porting cvc5's, registered in `theoryRewriter`.
- [ ] Examples with expected output; fuzzer generators; agreement with cvc5 and
      no semantic disagreements; Ethos accepts the printed proofs.
- [ ] Optional: `childrenTypedOfParent` and `ChildTyping` cases for the new kinds.
- [ ] Optional: `StaticProc` cases for hot normalization steps, with their proofs.
- [ ] `docs/design.md` updated: what is ported, deviations from cvc5, fuzzing
      results, timings.
