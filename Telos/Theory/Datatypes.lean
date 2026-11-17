import Telos.Theory.Common
import Telos.Rewriter.Rewriter

/-!
# The datatypes rewriter

A port of cvc5's `DatatypesRewriter` (`src/theory/datatypes/datatypes_rewriter.cpp`)
for the datatypes of cvc5's safe mode: inductive datatypes, not parametric (yet),
with no codatatypes, `match` or nullables. Each step is a CPC rule that takes the
whole equation as its argument, with the result computed here:

* a selector of a constructor application is the field it selects
  (`rewriteSelector`, `dt-collapse-selector`), unless the selector belongs to
  another constructor;
* a tester of a constructor application is `true` or `false`
  (`rewriteTester`, `dt-collapse-tester`); a tester for a nullary constructor is
  an equality with it (`dt-inst`); a tester of a datatype with one constructor is
  `true` (`dt-collapse-tester-singleton`);
* an updater of a constructor application replaces the field, or is the
  application itself for another constructor (`rewriteUpdater`; certified by
  `dt-updater-elim`, see `collapseUpdater`);
* equalities: `true` for equal sides (`eq-refl`), `false` when the sides clash
  (`utils::checkClash`: distinct constructors, or distinct constants, at the same
  position; `dt-cons-eq-clash`), and otherwise oriented by the term order
  (`eq-symm`).

Deviations from cvc5: cvc5 orders the sides of equalities by node id; telos by
its term order (`Node.lt`).
-/

open Eo

namespace Telos

namespace DatatypesRewriter

open Node

/-- A constructor application: its datatype, constructor index and fields. -/
def consApp? : Node → Option (TypeNode × Nat × Array Node)
  | .app (.node .APPLY_CONSTRUCTOR (.const (.dtCons T i))) cs => some (T, i, cs)
  | _ => none

/-- The symbol of a datatype operator application, and its children. -/
def dtOp? : Node → Option (Const × Array Node)
  | .app (.node _ (.const c)) cs => some (c, cs)
  | _ => none

def respond {n : Node} (st : RewriteStatus) : Option (Rw n) → RewriteResponse n
  | some ⟨m, h⟩ => ⟨st, m, h⟩
  | none => .done n

/-- cvc5's `rewriteSelector`: `(s_j (C_i t₁ … tₙ))` is `t_j` for the selectors of
`C_i`. -/
def rewriteSelector (n : Node) : RewriteResponse n :=
  match dtOp? n with
  | some (.dtSel T i j, #[t]) =>
    match consApp? t with
    | some (T', k, cs) =>
      if T' == T && k == i then
        match cs[j]? with
        | some f => respond .REWRITE_DONE (checkBy .dt_collapse_selector n f)
        | none => .done n
      else .done n
    | none => .done n
  | _ => .done n

/-- cvc5's `rewriteTester`. -/
def rewriteTester (n : Node) : RewriteResponse n :=
  match dtOp? n with
  | some (c@(.dtCons T i), #[t]) =>
    match consApp? t with
    | some (_, k, _) => respond .REWRITE_DONE (checkBy .dt_collapse_tester n (mkBool (i == k)))
    | none =>
      match T.dtFields? i, T.dtConstructors? with
      -- `((_ is nil) x)` is `(= x nil)`.
      | some [], _ =>
        respond .REWRITE_AGAIN_FULL
          (checkBy .dt_inst n (eqNode t (.app (.node .APPLY_CONSTRUCTOR (.const c)) #[])))
      | _, some [_] => respond .REWRITE_DONE (checkBy .dt_collapse_tester_singleton n mkTrue)
      | _, _ => .done n
  | _ => .done n

/-- `((_ update s_j) t u)` for a constructor application `t = (C_k t₁ … tₙ)` and a
selector `s_j` of `C_i`: `(C_i t₁ … u … tₙ)` if `k = i`, else `t` (cvc5's
`rewriteUpdater`). CPC's `dt-collapse-updater` states this, but its side
condition does not evaluate (`$mk_dt_collapse_updater_rhs` takes `eo::len` of a
list, and counts the field from the wrong end), so it is certified as
`dt-updater-elim`, `(ite ((_ is C_i) t) (C_i (s₁ t) … u … (sₙ t)) t)`, then the
tester (`dt-collapse-tester`), the `ite` (`ite-true-cond`, `ite-false-cond`), and
the selectors (`dt-collapse-selector`). -/
def collapseUpdater (T : TypeNode) (i j : Nat) (t u : Node) (k : Nat) (cs : Array Node)
    (n : Node) : Option (Rw n) := do
  let fields ← T.dtFields? i
  let sel (m : Nat) : Node := .app (.node .APPLY_SELECTOR (.const (.dtSel T i m))) #[t]
  let ci : Node := .const (.dtCons T i)
  let tu : Node := .app (.node .APPLY_CONSTRUCTOR ci)
    ((List.range fields.length).map fun m => if m == j then u else sel m).toArray
  let tester : Node := .app (.node .APPLY_TESTER ci) #[t]
  let r ← checkBy .dt_updater_elim n (iteNode tester tu t)
  let r ← r.next? fun m => Rw.congrArg m 0 fun c => checkBy .dt_collapse_tester c (mkBool (i == k))
  let r ← r.next? (byRule (if i == k then "ite-true-cond" else "ite-false-cond"))
  if i != k then return r
  -- `(C_i … (s_m t) …)` to `(C_i … t_m …)`, one field at a time.
  (List.range fields.length).foldlM (init := r) fun r m =>
    if m == j then some r
    else r.next? fun m' => Rw.congrArg m' m fun c => cs[m]?.bind (checkBy .dt_collapse_selector c)

/-- cvc5's `rewriteUpdater`. -/
def rewriteUpdater (n : Node) : RewriteResponse n :=
  match dtOp? n with
  | some (.dtSel T i j, #[t, u]) =>
    match consApp? t with
    | some (T', k, cs) =>
      if T' != T then .done n
      else respond .REWRITE_DONE (collapseUpdater T i j t u k cs n)
    | none => .done n
  | _ => .done n

/-- cvc5's `utils::checkClash`, with `checkNdtConst`: the two terms are
constructor applications that differ in their constructor, or in distinct
constants, at some position. -/
partial def checkClash (a b : Node) : Bool :=
  match consApp? a, consApp? b with
  | some (_, i, as), some (_, j, bs) =>
    i != j || (as.zip bs).any fun (x, y) => checkClash x y
  | _, _ => a != b && a.isConst && b.isConst

/-- Equalities of datatypes (cvc5's `postRewrite`). -/
def rewriteEqual (n : Node) : RewriteResponse n :=
  match n.getChildren with
  | #[a, b] =>
    if a == b then respond .REWRITE_DONE (byRule "eq-refl" n)
    else
      let clash := if checkClash a b then checkBy .dt_cons_eq_clash n mkFalse else none
      match clash with
      | some ⟨m, h⟩ => ⟨.REWRITE_DONE, m, h⟩
      | none => if b.lt a then respond .REWRITE_DONE (byRule "eq-symm" n) else .done n
  | _ => .done n

def postRewrite (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .APPLY_SELECTOR => rewriteSelector n
  | .APPLY_TESTER => rewriteTester n
  | .APPLY_UPDATER => rewriteUpdater n
  | .EQUAL => rewriteEqual n
  | _ => .done n

/-- cvc5's `preRewrite` only ascribes types to parametric constructors, which
telos does not have yet. -/
def preRewrite (n : Node) : RewriteResponse n := .done n

end DatatypesRewriter

/-- cvc5's `DatatypesRewriter`. -/
def TheoryRewriter.datatypes : TheoryRewriter where
  preRewrite := DatatypesRewriter.preRewrite
  postRewrite := DatatypesRewriter.postRewrite

end Telos
