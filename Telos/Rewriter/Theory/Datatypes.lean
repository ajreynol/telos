import Telos.Rewriter.Theory.Common
import Telos.Rewriter.Rewriter

/-!
# The datatypes rewriter

A port of cvc5's `DatatypesRewriter` (`src/theory/datatypes/datatypes_rewriter.cpp`)
for the datatypes of cvc5's safe mode: inductive datatypes, parametric ones (which
Logos's parser instantiates, so that each instance is a datatype of its own), and
tuples (`TUPLE`, `TUPLE_SELECT`, `TUPLE_UPDATE`, in Eunoia's form), with no
codatatypes, `match` or nullables. Each step is a CPC rule that takes the
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

/-- Whether a datatype is an instance of a parametric datatype (named
`.par_k_D` by Logos's parser). -/
def isParInstance : TypeNode → Bool
  | .datatype s _ => s.startsWith ".par_"
  | _ => false

/-- cvc5's `rewriteTester`. -/
def rewriteTester (n : Node) : RewriteResponse n :=
  match dtOp? n with
  | some (c@(.dtCons T i), #[t]) =>
    match consApp? t with
    | some (_, k, _) =>
      -- A nullary constructor of an instance of a parametric datatype tested
      -- by its own tester: `dt-inst` and `eq-refl`. Ethos does not accept
      -- `dt-collapse-tester` there: it writes the tester's constructor bare
      -- and the tested one `(as C T)`, which `$dt_eq_cons` finds different.
      if i == k && T.dtFields? i == some [] && isParInstance T then
        respond .REWRITE_DONE <| (checkBy .dt_inst n (eqNode t t)).bind fun r =>
          r.next? (byRule "eq-refl")
      else respond .REWRITE_DONE (checkBy .dt_collapse_tester n (mkBool (i == k)))
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

/-- The fields of a tuple `(TUPLE a₁ (… (TUPLE aₙ TUPLE_UNIT)))`. -/
def tupleElems? : Node → Option (List Node)
  | .app (.kind .TUPLE_UNIT) #[] => some []
  | .app (.kind .TUPLE) #[a, r] => (a :: ·) <$> tupleElems? r
  | _ => none

/-- The tuple with these fields. -/
def mkTupleNode (es : List Node) : Node :=
  es.foldr (fun a r => mkNode .TUPLE #[a, r]) (mkNode .TUPLE_UNIT #[])

/-- The index of an indexed operator with one index. -/
def index? : Node → Option Int
  | .app (.indexed _ #[j]) _ => some j
  | _ => none

/-- cvc5's `rewriteSelector`, for tuples: `((_ tuple.select j) (tuple t₁ … tₙ))`
is `t_j` (`dt-collapse-selector`). -/
def rewriteTupleSelect (n : Node) : RewriteResponse n :=
  match index? n, n.getChildren with
  | some j, #[t] =>
    match tupleElems? t >>= fun es => es[j.toNat]? with
    | some f => if j ≥ 0 then respond .REWRITE_DONE (checkBy .dt_collapse_selector n f) else .done n
    | none => .done n
  | _, _ => .done n

/-- cvc5's `rewriteUpdater`, for tuples: `((_ tuple.update j) (tuple t₁ … tₙ) u)`
is the tuple with `u` for `t_j` (`dt-collapse-updater`). -/
def rewriteTupleUpdate (n : Node) : RewriteResponse n :=
  match index? n, n.getChildren with
  | some j, #[t, u] =>
    match tupleElems? t with
    | some es =>
      if j ≥ 0 && j.toNat < es.length then
        respond .REWRITE_DONE (checkBy .dt_collapse_updater n (mkTupleNode (es.set j.toNat u)))
      else .done n
    | none => .done n
  | _, _ => .done n

/-- cvc5's `utils::checkClash`, with `checkNdtConst`: the two terms are
constructor applications (or tuples) that differ in their constructor, or in
distinct constants, at some position. -/
partial def checkClash (a b : Node) : Bool :=
  match consApp? a, consApp? b with
  | some (_, i, as), some (_, j, bs) =>
    i != j || (as.zip bs).any fun (x, y) => checkClash x y
  | _, _ =>
    match tupleElems? a, tupleElems? b with
    | some as, some bs => (as.zip bs).any fun (x, y) => checkClash x y
    | _, _ => a != b && a.isConst && b.isConst

/-- The fields of a constructor application or a tuple, if `n` is one; for
tuples, `(TUPLE a r)` has fields `a` and `r`. -/
def fieldsOf? (n : Node) : Option (Nat × Array Node) :=
  match consApp? n with
  | some (_, i, cs) => some (i, cs)
  | none => if n.getKind == .TUPLE then some (0, n.getChildren) else none

/-- cvc5's `utils::checkClash`, collecting the equalities of the leaves at
which `a` and `b` differ (`rew`): `none` for a clash. -/
partial def consEqLeaves (a b : Node) : Option (List Node) :=
  match fieldsOf? a, fieldsOf? b with
  | some (i, as), some (j, bs) =>
    if i != j || as.size != bs.size then none
    else (as.toList.zip bs.toList).foldlM (fun acc (x, y) => (acc ++ ·) <$> consEqLeaves x y) []
  | _, _ =>
    if a == b then some []
    else if a.isConst && b.isConst then none
    else some [eqNode a b]

/-- A conjunction of `es`: `e` for one, `true` for none. -/
def mkAndOf : List Node → Node
  | [] => mkTrue
  | [e] => e
  | es => mkNode .AND es.toArray

/-- cvc5's `MACRO_DT_CONS_EQ` (applied by `ppStaticRewrite`): an equality of
constructor applications (or tuples) is `false` if they clash
(`dt-cons-eq-clash`), and otherwise the conjunction of the equalities of the
leaves at which they differ. Certified by `dt-cons-eq` (the equalities of the
fields), then each field equality: `eq-refl` for equal sides, again for
constructor applications; then `aci_norm`. -/
partial def consEq (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  if n.getKind != .EQUAL then none
  let some (_, as) := fieldsOf? a | none
  let some (_, bs) := fieldsOf? b | none
  match consEqLeaves a b with
  | none => checkBy .dt_cons_eq_clash n mkFalse
  | some [] => none
  | some leaves =>
    let target := mkAndOf leaves
    if target == n then none
    let eqs := (as.toList.zip bs.toList).map fun (x, y) => eqNode x y
    let r ← checkBy .dt_cons_eq n (mkAndOf eqs)
    -- each field equality
    let field (e : Node) : Option (Rw e) :=
      match e.getChildren with
      | #[x, y] => if x == y then byRule "eq-refl" e else consEq e
      | _ => none
    let r := match eqs with
      | [_] => (r.next? field).getD r
      | _ => (List.range eqs.length).foldl (fun r i => (r.next? fun m => Rw.congrArg m i field).getD r) r
    if r.1 == target then some r
    else r.next? fun m => checkBy .aci_norm m target

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
  | .TUPLE_SELECT => rewriteTupleSelect n
  | .TUPLE_UPDATE => rewriteTupleUpdate n
  | .EQUAL => rewriteEqual n
  | _ => .done n

/-- cvc5's `preRewrite` only ascribes types to parametric constructors, which
Logos's instances already have. -/
def preRewrite (n : Node) : RewriteResponse n := .done n

end DatatypesRewriter

/-- cvc5's `DatatypesRewriter`. -/
def TheoryRewriter.datatypes : TheoryRewriter where
  preRewrite := DatatypesRewriter.preRewrite
  postRewrite := DatatypesRewriter.postRewrite

end Telos
