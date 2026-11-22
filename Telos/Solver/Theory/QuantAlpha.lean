import Std.Data.HashMap
import Telos.Core.Node.Key
import Telos.Core.Node.FastType
import Telos.Core.Node.Print

/-!
# Alpha-equivalence of quantified formulas

cvc5's `AlphaEquivalence` (`src/theory/quantifiers/alpha_equivalence.cpp`,
`quant-alpha-equiv`, on by default) with `TermCanonize`
(`src/expr/term_canonize.cpp`): a quantified formula whose body is, up to the
names of its variables and the order of the children of commutative operators,
that of a formula registered before, with variables of the same types, is
reduced to it: the lemma `(= q' q)` (`QUANTIFIERS_REDUCE_ALPHA_EQ`), and `q`
is neither registered nor skolemized.

The canonical form numbers the bound variables of each type in the order they
are met, then sorts the children of commutative operators (`getTermOrder`:
variables first, by number; then by operator, children, arity). cvc5 orders
operators by node id; telos by `lt` for function symbols (cvc5's node order),
and by kind otherwise.

Deviation: cvc5's miniscoping gives the quantifiers it makes fresh variables,
so two of them may be distinct, alpha-equivalent nodes where telos's (which
keep their names) are one node: telos has no lemma then.
-/

namespace Telos.Solver.Quant

/-- The canonical variable `i` of type `T`. -/
def canonVar (T : TypeNode) (i : Nat) : Node := .boundVar s!"@canon_{i}" T

def canonIndex : Node → Option Nat
  | .boundVar n _ => if n.startsWith "@canon_" then (n.drop 7).toNat? else none
  | _ => none

/-- `TermUtil::isComm`. -/
def isCommKind (k : Kind) : Bool :=
  k == .EQUAL || k == .ADD || k == .MULT || k == .AND || k == .OR || k == .XOR ||
    k == .BITVECTOR_ADD || k == .BITVECTOR_MULT || k == .BITVECTOR_AND || k == .BITVECTOR_OR ||
    k == .BITVECTOR_XOR || k == .BITVECTOR_XNOR || k == .SET_UNION || k == .SET_INTER

/-- The operator of an application for `getTermOrder`, as a comparable key:
kinds first (by kind), then function symbols (by `lt`). -/
def opLt (lt : Node → Node → Bool) (a b : Node) : Bool :=
  match a, b with
  | .app (.kind k₁) _, .app (.kind k₂) _ => compare k₁ k₂ == .lt
  | .app (.kind _) _, .app _ _ => true
  | .app _ _, .app (.kind _) _ => false
  | .app (.node _ f₁) _, .app (.node _ f₂) _ => lt f₁ f₂
  | .app _ _, _ => false
  | _, .app _ _ => true
  | _, _ => lt a b

def opEq (a b : Node) : Bool :=
  match a, b with
  | .app o₁ _, .app o₂ _ => o₁ == o₂
  | .app .., _ | _, .app .. => false
  | _, _ => a == b

/-- `TermCanonize::getTermOrder`. -/
partial def termOrder (lt : Node → Node → Bool) (a b : Node) : Bool :=
  match canonIndex a, canonIndex b with
  | some i, some j => i < j
  | some _, none => true
  | none, some _ => false
  | none, none =>
    if opEq a b then
      let ca := a.getChildren
      let cb := b.getChildren
      if ca.size == cb.size then
        match (ca.zip cb).find? fun (x, y) => x != y with
        | some (x, y) => termOrder lt x y
        | none => false
      else ca.size < cb.size
    else opLt lt a b

/-- The canonical form of `n` (`getCanonicalTerm`, with the order of children
of commutative operators), with the canonical variable of each bound variable
met. -/
partial def canonical (lt : Node → Node → Bool) (n : Node) :
    StateM (Std.HashMap Key Node × Std.HashMap (Option TypeNode) Nat) Node := do
  if let some r := (← get).1.get? ⟨n⟩ then return r
  let r ← match n with
    | .boundVar _ T =>
      let k := ((← get).2.get? (some T)).getD 0
      modify fun (m, c) => (m, c.insert (some T) (k + 1))
      pure (canonVar T k)
    | .app op cs =>
      let mut ds : Array Node := #[]
      for c in cs do ds := ds.push (← canonical lt c)
      if let .kind k := op then
        if isCommKind k then ds := ds.qsort (termOrder lt)
      pure (.app op ds)
    | .skolem id cs =>
      let mut ds : Array Node := #[]
      for c in cs do ds := ds.push (← canonical lt c)
      pure (.skolem id ds)
    | n => pure n
  modify fun (m, c) => (m.insert ⟨n⟩ r, c)
  return r

/-- The key of a quantified formula in the database: the types of its
variables, with their numbers (a multiset), and its body's canonical form. -/
def alphaKey (lt : Node → Node → Bool) (vars : Array Node) (body : Node) : List (String × Nat) × Key :=
  let tys : List (String × Nat) := vars.foldl (fun acc v =>
    let t := match v with | .boundVar _ T => T.toSmtLibWith {} | _ => ""
    match acc.lookup t with
    | some k => acc.filter (·.1 != t) ++ [(t, k + 1)]
    | none => acc ++ [(t, 1)]) []
  let tys := tys.toArray.qsort (fun a b => a.1 < b.1) |>.toList
  (tys, ⟨((canonical lt body).run ({}, {})).1⟩)

/-- The alpha-equivalence database (user context). -/
structure AlphaDb where
  trie : Std.HashMap (List (String × Nat) × Key) Node := {}
  /-- `d_quants_red`: whether each formula was reduced. -/
  red : Std.HashMap Key Bool := {}
  deriving Inhabited

end Telos.Solver.Quant
