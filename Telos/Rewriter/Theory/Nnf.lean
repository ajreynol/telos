import Telos.Rewriter.Theory.Common
import Telos.Core.Node.FastType

/-!
# Negation normal form

A port of cvc5's `TheoryBoolRewriter::computeNnfNorm`
(`src/theory/booleans/theory_bool_rewriter.cpp`), which the quantifiers rewriter
applies to the bodies of quantified formulas (`COMPUTE_ELIM_SYMBOLS`).
Implications and `xor` are eliminated, negations are pushed down through `or`,
`and`, `=>`, `xor`, Boolean equalities and `ite`, and the `and`s and `or`s are
flattened, with duplicate literals removed and a literal and its negation giving
`true` or `false` (`addNnfNormChild`).

Each step is a CPC rule: `bool-impl-elim`, `bool-xor-elim`,
`bool-double-not-elim`, `bool-or-de-morgan`, `bool-implies-de-morgan`,
`bool-and-de-morgan`, `bool-not-xor-elim`, `bool-not-eq-elim1` and
`bool-not-ite-elim` for the negations, then `aci_norm` for flattening and
duplicates, and `bool-or-taut`, `bool-or-taut2`, `bool-and-conf` and
`bool-and-conf2` for complementary literals. The De Morgan rules split off one
child at a time; flattening the result gives cvc5's.
-/

namespace Telos

namespace Nnf

open Node

def isBool (n : Node) : Bool := n.typeHint == some .boolean

/-- The literal and polarity of a child of an `and` or `or`. -/
def litPol (c : Node) : Node × Bool :=
  match c.getKind, c.getChildren with
  | .NOT, #[l] => (l, false)
  | _, _ => (c, true)

/-- cvc5's reconstruction of an `and` or `or` of normalized children: flattened,
without duplicate literals, or `true` (`or`) or `false` (`and`) when a literal
occurs with both polarities. `none` for a conflict, else the children. -/
def flatten (k : Kind) (cs : Array Node) : Option (Array Node) :=
  let flat := cs.foldl (init := #[]) fun acc c =>
    if c.getKind == k then acc ++ c.getChildren else acc.push c
  let step (st : Array Node × List (Node × Bool)) (c : Node) :
      Option (Array Node × List (Node × Bool)) :=
    let (l, p) := litPol c
    match st.2.find? (·.1 == l) with
    | some (_, p') => if p' == p then some st else none
    | none => some (st.1.push c, (l, p) :: st.2)
  (flat.foldlM step (#[], [])).map (·.1)

/-- The reconstruction step of an `and` or `or` whose children are normalized. -/
def post (n : Node) : Option (Rw n) :=
  let k := n.getKind
  let cs := n.getChildren
  match flatten k cs with
  | none =>
    -- Flatten (and keep duplicates), then the complementary pair.
    let flat := cs.foldl (init := #[]) fun acc c =>
      if c.getKind == k then acc ++ c.getChildren else acc.push c
    let flatNode := mkNode k flat
    let r := if flatNode == n then some (Rw.id n) else checkBy .aci_norm n flatNode
    r.bind fun r => r.next? fun m =>
      if k == .OR then firstOf [fun _ => byRule "bool-or-taut" m, fun _ => byRule "bool-or-taut2" m]
      else firstOf [fun _ => byRule "bool-and-conf" m, fun _ => byRule "bool-and-conf2" m]
  | some ds =>
    let target := if ds.size == 1 then ds[0]! else mkNode k ds
    if target == n then none else checkBy .aci_norm n target

mutual

/-- The NNF of `n` (cvc5's `computeNnfNorm`). -/
partial def nnf (n : Node) : Rw n :=
  match n.getKind, n.getChildren with
  | .IMPLIES, #[_, _] => step "bool-impl-elim"
  | .XOR, #[_, _] => step "bool-xor-elim"
  | .NOT, #[c] =>
    match c.getKind, c.getChildren with
    | .NOT, #[_] => step "bool-double-not-elim"
    | .OR, _ => step "bool-or-de-morgan"
    | .IMPLIES, #[_, _] => step "bool-implies-de-morgan"
    | .AND, _ => step "bool-and-de-morgan"
    | .XOR, #[_, _] => step "bool-not-xor-elim"
    | .EQUAL, #[a, _] => if isBool a then step "bool-not-eq-elim1" else Rw.id n
    | .ITE, #[_, _, _] => step "bool-not-ite-elim"
    | _, _ => Rw.id n
  | .AND, _ | .OR, _ =>
    let r := children n
    r.next post
  | .ITE, #[_, _, _] => children n
  | .EQUAL, #[a, _] => if isBool a then children n else Rw.id n
  | _, _ => Rw.id n
where
  step (name : String) : Rw n :=
    match byRule name n with
    | some r => r.next fun m => some (nnf m)
    | none => Rw.id n

/-- `n` with each child in NNF. -/
partial def children (n : Node) : Rw n :=
  (List.range n.getNumChildren).foldl (init := Rw.id n) fun r i =>
    r.next fun m => Rw.congrArg m i fun c =>
      let rc := nnf c
      if rc.1 == c then none else some rc

end

end Nnf

end Telos
