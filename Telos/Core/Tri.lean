import Telos.Core.Node.DecEq
import Telos.Core.Node.ToEo
import Cpc.Logos

/-!
# Triangular substitution steps

The data and side conditions of `Certified.tri` (`Telos/Core/Certified.lean`),
the step of non-clausal simplification that substitutes the sides of equations
in the conjuncts of a conjunction.

A step relates `n = (and c₁ … cₖ)` to `k = (and d₁ … dₖ)` conjunct by conjunct:
`cᵢ` is rewritten to `dᵢ` by a chain of steps, each a certified rewrite, or a
substitution justified by the **entries**: equations `l ↦ r` read off conjuncts
`dⱼ` of the result with `j > i` (`(= l r)`, `(= r l)`, `l` for `l ↦ true`,
`(not l)` for `l ↦ false`). Because an entry used for `cᵢ` comes from a later
conjunct of the result, `n` holds in a model iff `k` does: by induction from the
last conjunct down, each `dⱼ` with `j > i` holds, so the entries for `cᵢ` hold,
so `cᵢ` and `dᵢ` are equal (`verification/TelosProofs/Core/Tri.lean`).

Everything is checked in time linear in the size of the terms as DAGs: the
substitutions are given as an array of **justifications** (`Just`), each a pair
`(a, b)` related by reflexivity, an entry, or congruence, whose premises are
earlier justifications given by index; and the conjuncts the entries come from
are shown closed (`Ground`) by an array of nodes, children first, with the
indices of their children.

Congruence is used below the operators whose congruence holds model by model
(not quantifiers), and whose children are well typed when they are
(`Op.substOk`).
-/

open Eo

namespace Telos

instance : LawfulBEq Node where
  eq_of_beq h := of_decide_eq_true h
  rfl := decide_eq_true rfl

/-- Operators whose applications, when well typed, have well-typed children
(`verification/TelosProofs/Core/ChildTyping.lean`), so congruence under them needs no
run-time check of the children: the built-in Boolean, equality and arithmetic
operators. -/
def Op.childrenTypedOfParent : Op → Bool
  | .kind k => match k with
    | .EQUAL | .NOT | .AND | .OR | .IMPLIES | .XOR | .ITE
    | .ADD | .MULT | .SUB | .NEG | .DIVISION | .INTS_DIVISION | .INTS_MODULUS
    | .DIVISION_TOTAL | .INTS_DIVISION_TOTAL | .INTS_MODULUS_TOTAL | .ABS
    | .LT | .LEQ | .GT | .GEQ | .TO_REAL | .TO_INTEGER | .IS_INTEGER
    | .BITVECTOR_NOT | .BITVECTOR_NEG | .BITVECTOR_NAND | .BITVECTOR_NOR | .BITVECTOR_XNOR
    | .BITVECTOR_COMP | .BITVECTOR_SUB | .BITVECTOR_UDIV | .BITVECTOR_UREM | .BITVECTOR_SDIV
    | .BITVECTOR_SREM | .BITVECTOR_SMOD | .BITVECTOR_SHL | .BITVECTOR_LSHR | .BITVECTOR_ASHR
    | .BITVECTOR_ULT | .BITVECTOR_ULE | .BITVECTOR_UGT | .BITVECTOR_UGE | .BITVECTOR_SLT
    | .BITVECTOR_SLE | .BITVECTOR_SGT | .BITVECTOR_SGE | .BITVECTOR_AND | .BITVECTOR_OR
    | .BITVECTOR_XOR | .BITVECTOR_ADD | .BITVECTOR_MULT | .BITVECTOR_CONCAT => true
    | _ => false
  | _ => false

/-- Operators whose well-typed applications have well-typed children: those of
`childrenTypedOfParent`, and applications of declared functions. -/
def Op.childrenTypedForSubst : Op → Bool
  | .node .APPLY_UF (.var _ _) => true
  | op => op.childrenTypedOfParent

/-- The CPC head of an application is not that of a quantifier, so neither is
the application (nor any prefix of its spine). -/
def headQuantFree : Term → Bool
  | .UOp .forall | .UOp .exists => false
  | .Apply (.UOp .forall) _ | .Apply (.UOp .exists) _ => false
  | .Apply (.Apply (.UOp .forall) _) _ | .Apply (.Apply (.UOp .exists) _) _ => false
  | _ => true

/-- Shapes whose congruence holds model by model: spines with a head that is not
a quantifier, and the `:right-assoc-nil` operators of `isChildCongruent`. -/
def AppShape.substCongruent : AppShape → Bool
  | .spine head _ => headQuantFree head
  | .rightAssocNil op (.const _) => op == UserOp.and || op == UserOp.or || op.isReNary
  | .rightAssocNil op .typed => op == UserOp.plus || op == UserOp.mult || op.isTypedNary
  | _ => false

/-- Substitution may go below `op`. -/
def Op.substOk (op : Op) : Bool :=
  op.eoShape.substCongruent && op.childrenTypedForSubst

/-! ## Closed nodes -/

/-- The constants whose translation is closed and not stuck. -/
def Const.groundOk : Const → Bool
  | .emptySet _ => false
  | .dtCons (.datatype ..) _ | .dtSel (.datatype ..) _ _ => true
  | .dtCons .. | .dtSel .. => false
  | _ => true

/-- `n`'s translation is closed given that its children's are (and that it is
well typed, for the nil of a typed operator): a constant, a declared constant, or
an application below which substitution may go, with an accepted number of
children and a closed head (or nil). -/
def Node.groundLocal : Node → Bool
  | .const c => c.groundOk
  | .var .. => true
  | .boundVar .. | .skolem .. => false
  | .app op cs =>
    op.substOk && match op.eoShape with
      | .spine head arity => arity.accepts cs.size && __eo_is_closed head == Term.Boolean true
      | .rightAssocNil _ (.const t) => 2 ≤ cs.size && __eo_is_closed t == Term.Boolean true
      | .rightAssocNil o .typed => 2 ≤ cs.size && o != UserOp.str_concat
      | _ => false

/-- A node with the indices of its children in a `GroundOrder`. -/
structure GroundItem where
  node : Node
  kids : Array Nat

/-- The item at `g` is well formed: its node is `groundLocal`, and its children
are the nodes of earlier items, given by `kids`. -/
def groundItemOk (order : Array GroundItem) (g : Nat) : Bool :=
  match order[g]? with
  | none => false
  | some it =>
    it.node.groundLocal &&
      it.kids.size == it.node.getChildren.size &&
      (List.range it.kids.size).all fun t =>
        match it.kids[t]?, it.node.getChildren[t]? with
        | some k, some c => k < g && (order[k]?.map (·.node == c)).getD false
        | _, _ => false

/-! ## Justifications -/

/-- An equation `lhs ↦ rhs` read off the conjunct at `pos` of the result. -/
structure Entry where
  lhs : Node
  rhs : Node
  pos : Nat
  /-- The item of the `GroundOrder` that is the conjunct. -/
  ground : Nat

inductive JustKind where
  /-- `a = b`. -/
  | refl
  /-- `a ↦ c` is the entry `e`, and the justification `k` relates `c` to `b`. -/
  | entry (e k : Nat)
  /-- `a` and `b` apply the same operator, and the justifications `ks` relate
  their children. -/
  | congr (ks : Array Nat)

/-- A justification that `a` and `b` are equal in a model where the entries
with position at least `minPos` hold. -/
structure Just where
  a : Node
  b : Node
  minPos : Nat
  kind : JustKind

/-- How the conjunct `i` is rewritten, step by step. -/
inductive ChainStep where
  /-- A substitution, by the justification of that index. -/
  | subst (j : Nat)
  /-- A certified rewrite, the one of that index (`TriPlan.rws`). -/
  | rw (r : Nat)

/-- The data of a `Certified.tri` step. -/
structure TriPlan where
  entries : Array Entry
  justs : Array Just
  ground : Array GroundItem
  /-- The certified rewrites the chains use: their endpoints. -/
  rws : Array (Node × Node)
  /-- The chain of each conjunct. -/
  chains : Array (Array ChainStep)

namespace TriPlan

/-- The conjunct of the result at `pos`. -/
def conj (k : Node) (pos : Nat) : Option Node := k.getChildren[pos]?

/-- The entry `e` is read off the conjunct it names, which is ground. -/
def entryOk (P : TriPlan) (k : Node) (e : Entry) : Bool :=
  match conj k e.pos, P.ground[e.ground]? with
  | some d, some g =>
    g.node == d && (
      d == .app (.kind .EQUAL) #[e.lhs, e.rhs] ||
      d == .app (.kind .EQUAL) #[e.rhs, e.lhs] ||
      (e.lhs == d && e.rhs == .const (.boolean true)) ||
      (d == .app (.kind .NOT) #[e.lhs] && e.rhs == .const (.boolean false)))
  | _, _ => false

/-- The justification `j` is well formed: its premises are earlier ones, valid
at least as far down as it is. -/
def justOk (P : TriPlan) (j : Nat) : Bool :=
  match P.justs[j]? with
  | none => false
  | some J =>
    match J.kind with
    | .refl => J.a == J.b
    | .entry e k =>
      match P.entries[e]?, P.justs[k]? with
      | some E, some K =>
        k < j && E.lhs == J.a && K.a == E.rhs && K.b == J.b &&
          J.minPos ≤ E.pos && J.minPos ≤ K.minPos
      | _, _ => false
    | .congr ks =>
      match J.a, J.b with
      | .app op cs, .app op' ds =>
        op == op' && op.substOk && cs.size == ds.size && ks.size == cs.size &&
          (List.range ks.size).all fun t =>
            match ks[t]?, cs[t]?, ds[t]? with
            | some k, some c, some d =>
              k < j && (P.justs[k]?.map fun K => K.a == c && K.b == d && J.minPos ≤ K.minPos).getD false
            | _, _, _ => false
      | _, _ => false

/-- The endpoints of a chain step. -/
def stepEnds (P : TriPlan) (i : Nat) : ChainStep → Option (Node × Node)
  | .subst j => P.justs[j]?.bind fun J => if i + 1 ≤ J.minPos then some (J.a, J.b) else none
  | .rw r => P.rws[r]?

/-- The chain of conjunct `i` leads from `c` to `d`. -/
def chainOk (P : TriPlan) (i : Nat) (c d : Node) : Bool :=
  match P.chains[i]? with
  | none => false
  | some steps =>
    match steps.foldl (fun acc s => acc.bind fun cur =>
        (P.stepEnds i s).bind fun (a, b) => if a == cur then some b else none) (some c) with
    | some e => e == d
    | none => false

/-- The side condition of `Certified.tri n k`. -/
def Ok (P : TriPlan) (n k : Node) : Bool :=
  match n, k with
  | .app (.kind .AND) cs, .app (.kind .AND) ds =>
    2 ≤ cs.size && cs.size == ds.size && P.chains.size == cs.size &&
      (List.range P.ground.size).all (groundItemOk P.ground) &&
      P.entries.toList.all (P.entryOk k) &&
      (List.range P.justs.size).all P.justOk &&
      (List.range cs.size).all fun i =>
        match cs[i]?, ds[i]? with
        | some c, some d => P.chainOk i c d
        | _, _ => false
  | _, _ => false

end TriPlan

end Telos
