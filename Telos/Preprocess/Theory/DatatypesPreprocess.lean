import Telos.Rewriter.Theory.Datatypes
import Telos.Preprocess.SkolemSteps

/-!
# Datatypes theory preprocessing

cvc5's `TheoryDatatypes::ppRewrite`, which is `DatatypesRewriter::expandDefinition`
(`src/theory/datatypes/datatypes_rewriter.cpp`):

* an updater `((_ update s_j) t u)`, for a selector `s_j` of constructor `C`, is
  `(ite ((_ is C) t) (C (s₁ t) … u … (sₙ t)) t)` (`expandUpdater`, certified by
  `dt-updater-elim`);
* a selector is unchanged: cvc5 expands it to a shared selector, which CPC has no
  term for and which cvc5 prints as the selector.

For a tuple updater `((_ tuple.update j) t u)`, the tester `((_ is tuple) t)`
is `true` (tuples have one constructor), so cvc5's rewriting of the `ite` leaves
the tuple `(tuple (sel₀ t) … u … (selₙ t))`. That is the result here, certified
without the tester as a node (`Node` has no term for the `tuple` constructor):
`t` is rewritten to `(tuple (sel₀ t) … (selₙ t))` (`tupleEta`: `dt-inst` and
`dt-collapse-tester-singleton` on the tester, as CPC terms), then the update of
that tuple collapses (`dt-collapse-updater`). Logos does not translate the
tester on `tuple` yet (`upstream-requests.md`, request 9), so it rejects the
`dt-inst` step and tuple updaters are left unchanged for now.

Not ported: `DT_SIZE` (only for SyGuS).
-/

namespace Telos.Preprocess

open Node

/-- `DatatypesRewriter::expandUpdater`. -/
def expandUpdater (n : Node) : Option (Rw n) := do
  let .app (.node .APPLY_UPDATER (.const (.dtSel T i j))) #[t, u] := n | none
  let fields ← T.dtFields? i
  let sel (m : Nat) : Node := .app (.node .APPLY_SELECTOR (.const (.dtSel T i m))) #[t]
  let ci : Node := .const (.dtCons T i)
  let tu : Node := .app (.node .APPLY_CONSTRUCTOR ci)
    ((List.range fields.length).map fun m => if m == j then u else sel m).toArray
  checkBy .dt_updater_elim n (iteNode (.app (.node .APPLY_TESTER ci) #[t]) tu t)

open Eo in
/-- `t`, a tuple with `k` fields, rewritten to `(tuple (sel₀ t) … (selₖ₋₁ t))`:
`dt-inst` gives `(= ((_ is tuple) t) (= t …))`, `dt-collapse-tester-singleton`
gives `(= ((_ is tuple) t) true)`, so `(= t …)` by `symm`, `trans` and
`true_elim`. -/
def tupleEta (t : Node) (k : Nat) : Option (Rw t) :=
  let ts := DatatypesRewriter.mkTupleNode
    ((List.range k).map fun i => .app (.indexed .TUPLE_SELECT #[Int.ofNat i]) #[t])
  let tester := Term.Apply (Term.UOp1 UserOp1.is (Term.UOp UserOp.tuple)) t.toEo
  let eq := eqFormula t ts
  applyCmds (cmdList [
    stepWith .dt_inst [eoApp2 UserOp.eq tester eq],
    stepWith .dt_collapse_tester_singleton [eoApp2 UserOp.eq tester (Term.Boolean true)],
    .step .symm .nil (.cons 1 .nil),
    .step .trans .nil (.cons 0 (.cons 1 .nil)),
    .step .true_elim .nil prevPremise]) t

/-- `expandUpdater` for `((_ tuple.update j) t u)`, with the tester rewritten to
`true` and the `ite` collapsed, as cvc5's rewriting of its result does. -/
def expandTupleUpdater (n : Node) : Option (Rw n) := do
  let .app (.indexed .TUPLE_UPDATE #[j]) #[t, _] := n | none
  let fields ← (← t.typeHint).tupleFields?
  if j < 0 || j.toNat ≥ fields.length then none
  let r ← Rw.congrArg n 0 fun c => tupleEta c fields.length
  r.next? fun m =>
    match m.getChildren with
    | #[ts, u] => do
      let es ← DatatypesRewriter.tupleElems? ts
      checkBy .dt_collapse_updater m (DatatypesRewriter.mkTupleNode (es.set j.toNat u))
    | _ => none

/-- `TheoryDatatypes::ppRewrite`. -/
def dtPpRewrite (n : Node) : Option (Rw n) :=
  match n.getKind with
  | .APPLY_UPDATER => expandUpdater n
  | .TUPLE_UPDATE => expandTupleUpdater n
  | _ => none

end Telos.Preprocess
