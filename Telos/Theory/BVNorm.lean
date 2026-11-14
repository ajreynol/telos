import Telos.Theory.Common

/-!
# Bit-vector normalizations

cvc5's rewrite rules over whole n-ary bit-vector terms
(`theory_bv_rewrite_rules_normalization.h`), ported function by function. Each
computes cvc5's result natively, and the result is certified by a CPC step:

* the polynomial rules (`FlattenAssocCommut` for `bvadd` and `bvmul`,
  `AddCombineLikeTerms`, `MultSimplify`, `MultDistribConst`, `MultDistrib`,
  `NegIdemp`, `NegSub`, `NegAdd`) by one `bv_poly_norm` step, since their
  results are equal polynomials modulo `2^w`;
* the bitwise rules (`AndSimplify`, `OrSimplify`, `XorSimplify`, `XorZero`) as
  cvc5's `MacroRewriteElaborator` proves them: `aci_norm` (flattening, order,
  duplicates of `bvand`/`bvor`, the nil), the constants grouped by `aci_norm` and
  evaluated, `absorb` (the zero element), and the RARE rules `bv-and-simplify-*`,
  `bv-or-simplify-*` and `bv-xor-simplify-*` (`x` with `(bvnot x)`, pairs in a
  `bvxor`). A result for which this finds no certificate is not used.

cvc5 sorts children and orders its coefficient maps by node id; telos uses its
term order (`Node.lt`) instead, so results can differ from cvc5's in the order of
children.

cvc5's `NegMult` is not ported: its `applies` tests whether the only child of the
`bvneg` is a constant, rather than the last factor of the product, so it never
applies.
-/

namespace Telos

namespace BvNorm

open Node

/-- The width of a bit-vector node, from its structural type. -/
def width? (n : Node) : Option Nat :=
  match n.typeHint with
  | some (.bitVector w) => some w.toNat
  | _ => none

/-- The bit-vector constant of width `w` with value `v` modulo `2^w`. -/
def mkBv (w : Nat) (v : Int) : Node := .const (.bitVector w (v % (2 ^ w : Nat)))

/-- The value of a bit-vector constant. -/
def bvValue? : Node → Option Int
  | .const (.bitVector _ v) => some v
  | _ => none

/-- cvc5's `mkNaryNode`: the child itself when there is one. -/
def naryNode (k : Kind) : List Node → Node
  | [c] => c
  | cs => mkNode k cs.toArray

/-- Sort by the term order, as cvc5 sorts by node id. -/
def sortNodes (cs : List Node) : List Node := cs.mergeSort fun a b => !b.lt a

/-- cvc5's `mkSortedNode`. -/
def sortedNode (k : Kind) (cs : List Node) : Node := naryNode k (sortNodes cs)

/-! ## Polynomial rules -/

/-- The children cvc5's `FlattenAssocCommut` collects, in its order: a stack,
so the children of a nested application come in reverse. -/
partial def flattenOrder (k : Kind) : List Node → List Node → List Node
  | [], out => out
  | c :: stack, out =>
    if c.getKind == k then flattenOrder k (c.getChildren.toList.reverse ++ stack) out
    else flattenOrder k stack (out ++ [c])

/-- cvc5's `FlattenAssocCommut`, for `bvadd` and `bvmul` (not sorted). -/
def flattenAssocCommut (n : Node) : Option Node :=
  let k := n.getKind
  if n.getChildren.any (·.getKind == k) then some (naryNode k (flattenOrder k [n] [])) else none

/-- A coefficient map: terms with their coefficients, in insertion order. -/
abbrev CoefMap := List (Node × Int)

def CoefMap.add (m : CoefMap) (t : Node) (c : Int) : CoefMap :=
  if m.any (fun e => e.1 == t) then m.map fun e => if e.1 == t then (e.1, e.2 + c) else e
  else m ++ [(t, c)]

/-- cvc5's `updateCoefMap`. -/
def updateCoefMap (m : CoefMap) (constSum : Int) (current : Node) : CoefMap × Int :=
  match current.getKind, current.getChildren with
  | .BITVECTOR_MULT, cs =>
    let (coeff, term) : Int × Node :=
      if cs.size == 2 then
        match bvValue? cs[1]! with
        | some c => (c, cs[0]!)
        | none => (1, current)
      else
        match cs.back?.bind bvValue? with
        | some c => (c, mkNode .BITVECTOR_MULT cs.pop)
        | none => (1, current)
    match term.getKind, term.getChildren with
    | .BITVECTOR_SUB, #[a, b] => ((m.add a coeff).add b (-coeff), constSum)
    | .BITVECTOR_NEG, #[a] => (m.add a (-coeff), constSum)
    | _, _ => (m.add term coeff, constSum)
  | .BITVECTOR_SUB, #[a, b] => ((m.add a 1).add b (-1), constSum)
  | .BITVECTOR_NEG, #[a] => (m.add a (-1), constSum)
  | _, _ =>
    match bvValue? current with
    | some v => (m, constSum + v)
    | none => (m.add current 1, constSum)

/-- cvc5's `addToChildren`. -/
def addToChildren (w : Nat) (term : Node) (coeff : Int) : List Node :=
  let c := coeff % (2 ^ w : Nat)
  if c == 0 then []
  else if c == 1 then [term]
  else if c == (2 ^ w : Nat) - 1 then [mkNode .BITVECTOR_NEG #[term]]
  else if term.getKind == .BITVECTOR_MULT then
    [mkNode .BITVECTOR_MULT (term.getChildren.push (mkBv w c))]
  else [mkNode .BITVECTOR_MULT #[term, mkBv w c]]

/-- cvc5's `AddCombineLikeTerms`. The terms come in the term order, as cvc5's
`std::map<Node, BitVector>` orders them by node id. -/
def addCombineLikeTerms (n : Node) : Option Node := do
  let w ← width? n
  let (m, constSum) := n.getChildren.foldl (fun (m, s) c => updateCoefMap m s c) (([] : CoefMap), (0 : Int))
  let sorted := m.mergeSort fun a b => !b.1.lt a.1
  let children := sorted.flatMap (fun (t, c) => addToChildren w t c) ++
    (if constSum % (2 ^ w : Nat) != 0 then [mkBv w constSum] else [])
  if children.length == n.getChildren.size then none
  else some (if children.isEmpty then mkBv w 0 else naryNode .BITVECTOR_ADD children)

/-- cvc5's `MultSimplify`. -/
def multSimplify (n : Node) : Option Node := do
  let w ← width? n
  let mod := (2 ^ w : Nat)
  let (isNeg, constant, children, zero) := n.getChildren.foldl (init := (false, (1 : Int), ([] : List Node), false))
    fun (neg, k, cs, z) c =>
      let (neg, c) := match c.getKind, c.getChildren with
        | .BITVECTOR_NEG, #[d] => (!neg, d)
        | _, _ => (neg, c)
      match bvValue? c with
      | some v => let k := (k * v) % mod; (neg, k, cs, z || k == 0)
      | none => (neg, k, cs ++ [c], z)
  if zero then return mkBv w 0
  if children.isEmpty then return mkBv w (if isNeg then -constant else constant)
  let children := sortNodes children
  let (isNeg, children) :=
    if constant == mod - 1 then (!isNeg, children)
    else if constant != 1 then
      let (isNeg, constant) := if isNeg then (false, -constant) else (isNeg, constant)
      (isNeg, children ++ [mkBv w constant])
    else (isNeg, children)
  let ret := naryNode .BITVECTOR_MULT children
  return if isNeg && w > 1 then mkNode .BITVECTOR_NEG #[ret] else ret

/-- cvc5's `MultDistribConst`. -/
def multDistribConst (n : Node) : Option Node :=
  match n.getChildren with
  | #[factor, c@(.const (.bitVector w v))] =>
    match factor.getKind, factor.getChildren with
    | .BITVECTOR_NEG, #[f] => some (mkNode .BITVECTOR_MULT #[f, mkBv w.toNat (-v)])
    | .BITVECTOR_ADD, fs | .BITVECTOR_SUB, fs =>
      some (naryNode factor.getKind (fs.toList.map fun f => mkNode .BITVECTOR_MULT #[f, c]))
    | _, _ => none
  | _ => none

/-- cvc5's `MultDistrib`. -/
def multDistrib (n : Node) : Option Node :=
  match n.getChildren with
  | #[a, b] =>
    let isSum := fun (x : Node) => x.getKind == .BITVECTOR_ADD || x.getKind == .BITVECTOR_SUB
    let applies := if isSum a then !isSum b else isSum b
    if !applies then none else
    let (factor, sum) := if isSum a then (b, a) else (a, b)
    some (naryNode sum.getKind (sum.getChildren.toList.map fun s => mkNode .BITVECTOR_MULT #[s, factor]))
  | _ => none

/-- cvc5's `NegIdemp`. -/
def negIdemp (n : Node) : Option Node :=
  match n.getChildren with
  | #[.app (.kind .BITVECTOR_NEG) #[x]] => some x
  | _ => none

/-- cvc5's `NegSub`. -/
def negSub (n : Node) : Option Node :=
  match n.getChildren with
  | #[.app (.kind .BITVECTOR_SUB) #[a, b]] => some (mkNode .BITVECTOR_SUB #[b, a])
  | _ => none

/-- cvc5's `NegAdd`. -/
def negAdd (n : Node) : Option Node :=
  match n.getChildren with
  | #[.app (.kind .BITVECTOR_ADD) cs] =>
    some (naryNode .BITVECTOR_ADD (cs.toList.map fun c => mkNode .BITVECTOR_NEG #[c]))
  | _ => none

/-- A polynomial rule: its result, certified by `bv_poly_norm`. -/
def polyStep (f : Node → Option Node) : (m : Node) → Option (Rw m) := fun m => do
  let r ← f m
  if r == m then none else checkBy .bv_poly_norm m r

/-! ## Bitwise rules -/

/-- Occurrences of a term: positive and negated (under `bvnot`). -/
abbrev Counts := List (Node × Nat × Nat)

def Counts.insert (m : Counts) (t : Node) (neg : Bool) : Counts :=
  if m.any (fun e => e.1 == t) then
    m.map fun e => if e.1 == t then (if neg then (t, e.2.1, e.2.2 + 1) else (t, e.2.1 + 1, e.2.2)) else e
  else m ++ [if neg then (t, 0, 1) else (t, 1, 0)]

/-- The constants combined with `op` and the counts of the other children. -/
def collect (cs : Array Node) (init : Int) (op : Int → Int → Int) : Int × Counts :=
  cs.foldl (init := (init, [])) fun (k, m) c =>
    match bvValue? c with
    | some v => (op k v, m)
    | none =>
      match c.getKind, c.getChildren with
      | .BITVECTOR_NOT, #[d] => (k, m.insert d true)
      | _, _ => (k, m.insert c false)

/-- cvc5's `AndSimplify` (`isAnd`) and `OrSimplify`. -/
def andOrSimplify (isAnd : Bool) (n : Node) : Option Node := do
  let w ← width? n
  let ones : Int := (2 ^ w : Nat) - 1
  let (neutral, zero) := if isAnd then (ones, 0) else (0, ones)
  let (constant, counts) := collect n.getChildren neutral fun a b =>
    if isAnd then Int.ofNat (a.toNat &&& b.toNat) else Int.ofNat (a.toNat ||| b.toNat)
  if constant == zero then return mkBv w zero
  if counts.any (fun (_, p, q) => p > 0 && q > 0) then return mkBv w zero
  let children := (if constant != neutral then [mkBv w constant] else []) ++
    counts.map fun (t, _, q) => if q > 0 then mkNode .BITVECTOR_NOT #[t] else t
  if children.isEmpty then return mkBv w neutral
  return sortedNode n.getKind children

/-- cvc5's `XorSimplify`. -/
def xorSimplify (n : Node) : Option Node := do
  let w ← width? n
  let ones : Int := (2 ^ w : Nat) - 1
  let consts := n.getChildren.toList.filterMap bvValue?
  let (_, counts) := collect n.getChildren 0 fun a _ => a
  let trueCount := counts.filter (fun (_, p, q) => p % 2 == 1 && q % 2 == 1) |>.length
  let children := counts.filterMap fun (t, p, q) =>
    if p % 2 == 1 && q % 2 == 1 then none
    else if p % 2 == 1 then some t
    else if q % 2 == 1 then some (mkNode .BITVECTOR_NOT #[t])
    else none
  let xorConst := (if trueCount > 0 then [if trueCount % 2 == 1 then ones else 0] else []) ++
    (match consts with
     | [] => []
     | c :: cs => [cs.foldl (fun a b => Int.ofNat (a.toNat ^^^ b.toNat)) c])
  let children := children ++ match xorConst with
    | [] => []
    | c :: cs => [mkBv w (cs.foldl (fun a b => Int.ofNat (a.toNat ^^^ b.toNat)) c)]
  if children.isEmpty then return mkBv w 0
  return sortedNode .BITVECTOR_XOR children

/-- cvc5's `XorZero`: the zero children removed. -/
def xorZero (n : Node) : Option Node := do
  let w ← width? n
  let cs := n.getChildren.toList
  if !cs.any (· == mkBv w 0) then none
  let rest := cs.filter (· != mkBv w 0)
  return if rest.isEmpty then mkBv w 0 else naryNode .BITVECTOR_XOR rest

/-- The constants of a bitwise application grouped into one child, by
`aci_norm`, and evaluated (as cvc5's `ensureProofForSimplify` does). -/
def groupConsts (m : Node) : Option (Rw m) := do
  let k := m.getKind
  let cs := m.getChildren.toList
  let consts := cs.filter (·.isConst)
  let others := cs.filter (!·.isConst)
  if consts.length < 2 || others.isEmpty then none
  let grouped := mkNode k ((mkNode k consts.toArray) :: others).toArray
  let r ← checkBy .aci_norm m grouped
  r.next? fun g => Rw.congrArg g 0 byEvaluate

/-- The RARE rules that simplify a bitwise application. -/
def bitwiseRules : Kind → List String
  | .BITVECTOR_AND => ["bv-and-simplify-1", "bv-and-simplify-2"]
  | .BITVECTOR_OR => ["bv-or-simplify-1", "bv-or-simplify-2"]
  | .BITVECTOR_XOR => ["bv-xor-simplify-1", "bv-xor-simplify-2", "bv-xor-simplify-3",
      "bv-xor-duplicate", "bv-xor-ones"]
  | _ => []

/-- A certificate that `cur` rewrites to `target`: `aci_norm` or `absorb`
directly, or after evaluating a variable-free `cur`, grouping the constants or
applying a simplification rule. -/
partial def reach (target : Node) : Nat → (cur : Node) → Option (Rw cur)
  | 0, _ => none
  | fuel + 1, cur =>
    if cur == target then some (Rw.id cur) else
    firstOf [fun _ => checkBy .aci_norm cur target, fun _ => checkBy .absorb cur target,
      fun _ => if cur.vars.isEmpty && !cur.isConst then (byEvaluate cur).bind (·.next? (reach target fuel))
        else none,
      fun _ => (groupConsts cur).bind (·.next? (reach target fuel)),
      fun _ => (firstOf ((bitwiseRules cur.getKind).map fun r _ => byRule r cur)).bind
        (·.next? (reach target fuel))]

/-- A bitwise rule: its result, certified by `reach`. -/
def bitwiseStep (f : Node → Option Node) : (m : Node) → Option (Rw m) := fun m => do
  let r ← f m
  if r == m then none else reach r (m.getChildren.size + 2) m

end BvNorm

end Telos
