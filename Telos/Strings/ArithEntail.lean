import Telos.Theory.Arith
import Telos.Proof.Emit

/-!
# Arithmetic entailment for strings

A port of cvc5's `ArithEntail` (`src/theory/strings/arith_entail.cpp`) as the
strings rewriter uses it by default: without a rewriter and without recursive
approximations (`--strings-rec-arith-approx` is off), so that `rewriteArith` is
`rewriteLengthIntro` followed by the polynomial normal form (cvc5's
`PolyNorm::getPolyNorm`), and approximations are always simple.

It decides whether an integer term about strings is entailed to be
non-negative (`check`), by approximating its string terms (`findApprox`: for
example, `(str.len (str.substr x n m))` is at most `m` when `m >= 0`) until the
sum is a sum of non-negative terms (`checkSimple`).

This is strategy code and is not trusted. `proveGeq` turns an entailment into a
certified rewrite of `(>= a b)` to `true`, as cvc5 elaborates
`MACRO_ARITH_STRING_PRED_ENTAIL`: length introduction (`str-len-concat-rec`,
`evaluate`), normalization to `(>= n 0)` (`arith_poly_norm_rel`), the
approximation (`arith-string-pred-safe-approx`, whose Logos program checks that
the approximation is one of `getArithApproximations`), normalization again, and
`arith-string-pred-entail` (whose `$str_arith_entail_simple` is `checkSimple` on
the polynomial normal form) or `evaluate`.
-/

namespace Telos

namespace ArithEntail

open Node Arith

def zero : Node := .const (.integer 0)
def one : Node := .const (.integer 1)
def intC (i : Int) : Node := .const (.integer i)

/-- The length of a string constant. -/
def wordLen? : Node → Option Nat
  | .const (.string cs) => some cs.length
  | _ => none

/-- The children of a concatenation, flattened, without empty constants (cvc5's
`getACINormalForm` and `getConcat`). -/
partial def concatChildren (n : Node) : List Node :=
  if n.getKind == .STRING_CONCAT then n.getChildren.toList.flatMap concatChildren
  else if wordLen? n == some 0 then []
  else [n]

/-- cvc5's `rewriteLengthIntro`: `(str.len (str.++ x y))` is
`(+ (str.len x) (str.len y))`, and the length of a constant is a numeral,
everywhere in the term. -/
partial def lengthIntro (n : Node) : Node :=
  match n with
  | .app op cs =>
    let n' := Node.app op (cs.map lengthIntro)
    match n'.getKind, n'.getChildren with
    | .STRING_LENGTH, #[a] =>
      if a.getKind == .STRING_CONCAT || a.isConst then
        let parts := (concatChildren a).map fun c =>
          match wordLen? c with
          | some l => intC l
          | none => mkNode .STRING_LENGTH #[c]
        match parts with
        | [] => zero
        | [p] => p
        | ps => mkNode .ADD ps.toArray
      else n'
    | _, _ => n'
  | n => n

/-- cvc5's `PolyNorm::getPolyNorm` for an integer term: the node of its
polynomial normal form. -/
def polyNorm (n : Node) : Node := (polyOf n).toNode false

/-- cvc5's `rewriteArith` without a rewriter. -/
def rewriteArith (n : Node) : Node := polyNorm (lengthIntro n)

/-- cvc5's `checkSimple`: `a` is a sum or product of non-negative constants and
lengths. -/
partial def checkSimple (a : Node) : Bool :=
  match a with
  | .const (.integer i) => i ≥ 0
  | .const (.rational q) => q ≥ 0
  | _ =>
    match a.getKind with
    | .STRING_LENGTH => true
    | .ADD | .MULT => a.getChildren.all checkSimple
    | _ => false

/-- `check` with `isSimple`: the normal form of `a` (minus one if `strict`)
passes `checkSimple`. -/
def checkS (a : Node) (strict : Bool := false) : Bool :=
  match a with
  | .const (.integer i) => if strict then i ≥ 1 else i ≥ 0
  | _ => checkSimple (polyNorm (if strict then mkNode .SUB #[a, one] else a))

def checkS2 (a b : Node) (strict : Bool := false) : Bool :=
  if a == b then !strict else checkS (mkNode .SUB #[a, b]) strict

/-- cvc5's `getArithApproximations` (simple): the terms that `a` may be
replaced by, an under-approximation unless `isOver`. -/
partial def approximations (a : Node) (isOver : Bool) : List Node :=
  match a.getKind, a.getChildren with
  | .MULT, #[c@(.const (.integer k)), v] =>
    (approximations v (if k < 0 then !isOver else isOver)).map fun av => mkNode .MULT #[c, av]
  | .STRING_LENGTH, #[x] =>
    match x.getKind, x.getChildren with
    | .STRING_SUBSTR, #[s, n, m] =>
      let lenx := mkNode .STRING_LENGTH #[s]
      if isOver then
        (if checkS m then [m] else []) ++
          (if checkS2 lenx n then [mkNode .SUB #[lenx, n]] else [lenx])
      else
        let npm := mkNode .ADD #[n, m]
        (if checkS n && checkS2 lenx npm then [m] else []) ++
          (if checkS n && checkS2 npm lenx then [mkNode .SUB #[lenx, n]] else [])
    | .STRING_REPLACE, #[s, t, r] =>
      let lenx := mkNode .STRING_LENGTH #[s]
      let leny := mkNode .STRING_LENGTH #[t]
      let lenz := mkNode .STRING_LENGTH #[r]
      if isOver then
        if checkS2 leny lenz then [lenx] else [mkNode .ADD #[lenx, lenz]]
      else
        if checkS2 lenz leny || checkS2 lenz lenx then [lenx] else [mkNode .SUB #[lenx, leny]]
    | .STRING_ITOS, #[i] =>
      if isOver then
        if checkS i then (if checkS i true then [i] else [mkNode .ADD #[one, i]]) else []
      else if checkS i then [one] else []
    | _, _ => []
  | .STRING_INDEXOF, #[x, y, _] =>
    if isOver then
      let lenx := mkNode .STRING_LENGTH #[x]
      let leny := mkNode .STRING_LENGTH #[y]
      if checkS2 lenx leny then [mkNode .SUB #[lenx, leny]] else [lenx]
    else [intC (-1)]
  | .STRING_STOI, #[_] => if isOver then [] else [intC (-1)]
  | _, _ => []

/-- The monomials of a normalized sum, as (term, coefficient); the constant has
term `none`. -/
def monomials (ar : Node) : List (Option Node × Rat) :=
  (polyOf ar).map fun (m, c) => (if m.isEmpty then none else some (monoKey m), c)

/-- cvc5's `ArithSubs::applyArith`: replace the terms of `sub` in the arithmetic
skeleton of `n` (sums and products by constants). -/
partial def applyArith (sub : List (Node × Node)) (n : Node) : Node :=
  match sub.find? (·.1 == n) with
  | some (_, v) => v
  | none =>
    match n.getKind with
    | .ADD | .MULT | .SUB | .NEG => .app (.kind n.getKind) (n.getChildren.map (applyArith sub))
    | _ => n

/-- The polynomial of `c * t`. -/
def scaled (c : Rat) (t : Node) : Poly := (polyOf t).scale c

/-- cvc5's `findApproxInternal`, with simple approximations. -/
def findApproxInternal (ar : Node) : Option Node := do
  let ms := monomials ar
  -- Each monomial: fixed (one approximation) or a choice.
  let (fixed, sub, choices, changed) := ms.foldl
    (init := (([] : Poly), ([] : List (Node × Node)), ([] : List (Node × Rat × List Node)), false))
    fun (fixed, sub, choices, changed) (v?, c) =>
      match v? with
      | none => (Poly.add fixed (Poly.const c), sub, choices, changed)
      | some v =>
        let cur := polyNorm v
        let apx := match approximations cur (c < 0) with
          | [] => [cur]
          | as => as
        match apx with
        | [a] =>
          ((Poly.add fixed (scaled c a)), (if v != a then sub ++ [(v, a)] else sub), choices,
            changed || v != a)
        | as => (fixed, sub, choices ++ [(v, c, as)], true)
  if !changed then none
  -- Choose the approximations, in the order of the terms (cvc5: node ids).
  let choices := choices.mergeSort fun a b => !b.1.lt a.1
  let (aar, sub) := choices.foldl (init := (fixed, sub)) fun (aar, sub) (v, c, as) =>
    let score := fun (aa : Node) =>
      let (helps, adds) := (polyOf (polyNorm aa)).foldl (init := (0, 0)) fun (helps, adds) (ti, ci) =>
        let ci := c * ci
        match aar.find? (fun e => decide (e.1 = ti)) with
        | some (_, cc) =>
          if cc == 0 then (helps, adds + (if ci < 0 then 1 else 0))
          else if (cc > 0) != (ci > 0) then (helps + 1, adds + (if cc + ci < 0 then 1 else 0))
          else (helps, adds)
        | none => (helps, adds + (if ci < 0 then 1 else 0))
      (if adds > 0 then 0 else 2) + (if helps > 0 then 1 else 0)
    let best := as.foldl (init := (none : Option (Node × Nat))) fun best aa =>
      let s := score aa
      match best with
      | some (_, bs) => if s > bs then some (aa, s) else best
      | none => some (aa, s)
    match best with
    | some (aa, _) => (Poly.add aar (scaled c aa), sub ++ [(v, aa)])
    | none => (aar, sub)
  let aarN := Poly.toNode false aar
  if aarN == ar then none
  if checkS aarN then some (applyArith sub ar) else none

/-- cvc5's `findApprox`: `ar` itself if it is simple, else an approximation. -/
def findApprox (ar : Node) : Option Node :=
  if checkSimple ar then some ar else findApproxInternal ar

/-- cvc5's `check (a, strict)`: `a` (minus one if `strict`) is entailed to be
non-negative. -/
def check (a : Node) (strict : Bool := false) : Bool :=
  match a with
  | .const (.integer i) => if strict then i ≥ 1 else i ≥ 0
  | _ => (findApprox (rewriteArith (if strict then mkNode .SUB #[a, one] else a))).isSome

/-- cvc5's `check (a, b, strict)`: `a >= b` (or `a > b`). -/
def check2 (a b : Node) (strict : Bool := false) : Bool :=
  if a == b then !strict else check (mkNode .SUB #[a, b]) strict

/-- cvc5's `checkEq`. -/
def checkEq (a b : Node) : Bool := a == b || rewriteArith a == rewriteArith b

/-- cvc5's `getConstantBound` for a lower bound of a normalized term: constants,
lengths (at least 0), and sums and products of terms with bounds. -/
partial def lowerBound? (a : Node) : Option Int :=
  match a with
  | .const (.integer i) => some i
  | _ =>
    match a.getKind with
    | .STRING_LENGTH => some 0
    | .ADD => a.getChildren.foldlM (fun acc c => (lowerBound? c).map (acc + ·)) 0
    | .MULT =>
      -- A product is bounded below by the product of positive bounds.
      a.getChildren.foldlM (init := (1 : Int)) fun acc c => do
        let b ← lowerBound? c
        if b > 0 then some (acc * b) else none
    | _ => none

/-- cvc5's `StringsEntail::checkLengthOne`: the length of `s` is at most one
(exactly one if `strict`). -/
def checkLengthOne (s : Node) (strict : Bool := false) : Bool :=
  match wordLen? s with
  | some l => if strict then l == 1 else l ≤ 1
  | none =>
    let l := rewriteArith (mkNode .STRING_LENGTH #[s])
    check2 one l && (!strict || check l true)

/-! ## Certificates -/

def geqZero (t : Node) : Node := mkNode .GEQ #[t, zero]

/-- `n` rewritten by length introduction (`str-len-concat-rec`, and `evaluate`
for the length of a constant), under congruence. -/
partial def lengthIntroRw (n : Node) : Rw n :=
  let r := (List.range n.getChildren.size).foldl (init := Rw.id n) fun r i =>
    r.next fun m => Rw.congrArg m i fun c => some (lengthIntroRw c)
  r.next fun m =>
    match m.getKind, m.getChildren with
    | .STRING_LENGTH, #[a] =>
      if a.isConst then byEvaluate m
      else if a.getKind == .STRING_CONCAT then
        (byRule "str-len-concat-rec" m).map fun r => r.next fun k => some (lengthIntroRw k)
      else none
    | _, _ => none

/-- A certified rewrite of `(>= a b)` (or `(<= b a)`) to `true`, when `a >= b`
is entailed (cvc5's elaboration of `MACRO_ARITH_STRING_PRED_ENTAIL`). -/
def proveGeq (p : Node) : Option (Rw p) := do
  -- `(<= b a)` is `(>= a b)` (`arith-elim-leq`).
  let r0 ← match p.getKind with
    | .GEQ => some (Rw.id p)
    | .LEQ => byRule "arith-elim-leq" p
    -- cvc5's `normalizeGeq` for integers
    | .GT => byRule "arith-elim-int-gt" p
    | .LT => byRule "arith-elim-int-lt" p
    | _ => none
  let r1 := r0.next fun m => some (lengthIntroRw m)
  let (a, b) ← match r1.1.getChildren with
    | #[a, b] => some (a, b)
    | _ => none
  let diff := mkNode .SUB #[a, b]
  let expRew := polyNorm diff
  let approx ← findApprox expRew
  let approxRew := polyNorm approx
  -- (>= a b) = (>= expRew 0)
  let r2 ← if r1.1 == geqZero expRew then some r1
    else r1.next? fun m => polyNormRel m 1 1 diff (mkNode .SUB #[expRew, zero]) (geqZero expRew)
  -- (>= expRew 0) = (>= approx 0)
  let r3 ← if expRew == approx then some r2
    else r2.next? fun m => checkBy .arith_string_pred_safe_approx m (geqZero approx)
  -- (>= approx 0) = (>= approxRew 0)
  let r4 ← if approx == approxRew then some r3
    else r3.next? fun m =>
      polyNormRel m 1 1 (mkNode .SUB #[approx, zero]) (mkNode .SUB #[approxRew, zero]) (geqZero approxRew)
  -- (>= approxRew 0) = true
  r4.next? fun m =>
    if approxRew.isConst then byEvaluate m
    else checkBy .arith_string_pred_entail m (.const (.boolean true))

/-- A certified rewrite of `(= a b)` to `true` for integer terms with the same
polynomial after length introduction (cvc5's `checkEq`): length introduction
under congruence, then `arith_poly_norm` and `true_intro`. -/
def proveEq (p : Node) : Option (Rw p) := do
  let r := (Rw.id p).next fun m => Rw.congrArg m 0 fun c => some (lengthIntroRw c)
  let r := r.next fun m => Rw.congrArg m 1 fun c => some (lengthIntroRw c)
  match r.1.getChildren with
  | #[a, b] =>
    if !(isInt a) || !(List.Perm (polyOf a) (polyOf b) |> decide) then none
    else r.next? fun m =>
      applyCmds (.cons (.step .arith_poly_norm (.cons (eqFormula a b) .nil) .nil)
        (.cons (.step .true_intro .nil (.cons 0 .nil)) .nil)) m
  | _ => none

/-- The CPC commands proving `(= p true)`, for an arithmetic predicate `p`
entailed by `ArithEntail` (`>=`, `<=`, or an equality by `checkEq`). -/
def premiseProof (p : Node) (v : Node) : Option (List Eo.CCmd) := do
  if v != .const (.boolean true) then none
  let r ← if p.getKind == .EQUAL then proveEq p else proveGeq p
  if r.1 != .const (.boolean true) then none
  match Proof.emitProof r with
  | .ok steps => some (steps.toList.zipIdx.map fun (st, k) => st.toCmd k)
  | .error _ => none

end ArithEntail

end Telos
