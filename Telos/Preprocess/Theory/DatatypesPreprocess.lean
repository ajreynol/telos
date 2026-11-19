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

For a tuple updater `((_ tuple.update j) t u)` (tuples have one constructor),
cvc5 gives the tuple `(tuple (sel₀ t) … u … (selₙ t))` directly, with no tester
(cvc5 #13176), certified by `dt-updater-elim` in the same way.

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

/-- `expandUpdater` for `((_ tuple.update j) t u)`: the tuple of `t`'s fields,
with field `j` replaced by `u`. -/
def expandTupleUpdater (n : Node) : Option (Rw n) := do
  let .app (.indexed .TUPLE_UPDATE #[j]) #[t, u] := n | none
  let fields ← (← t.typeHint).tupleFields?
  if j < 0 || j.toNat ≥ fields.length then none
  let es := (List.range fields.length).map fun i =>
    if i == j.toNat then u else .app (.indexed .TUPLE_SELECT #[Int.ofNat i]) #[t]
  checkBy .dt_updater_elim n (DatatypesRewriter.mkTupleNode es)

/-- `TheoryDatatypes::ppRewrite`. -/
def dtPpRewrite (n : Node) : Option (Rw n) :=
  match n.getKind with
  | .APPLY_UPDATER => expandUpdater n
  | .TUPLE_UPDATE => expandTupleUpdater n
  | _ => none

end Telos.Preprocess
