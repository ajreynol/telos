import Telos.Theory.Common
import Telos.Arith.PolyNorm
import Telos.Rewriter.Rewriter

/-!
# The arithmetic rewriter

A port of the core of cvc5's `ArithRewriter` (`src/theory/arith/arith_rewriter.cpp`
and `src/theory/arith/rewriter/`): polynomial normalization of `+`, `-`, `*`,
unary `-`, `to_real` and division by a constant, and the normalization of `>=`
and `<=` to `(>= sum c)` or `(not (>= sum c))`.

Normal forms are computed here, by unverified code that follows cvc5's `Sum`
(`addition.cpp`), and each is certified by CPC: terms by `arith_poly_norm`,
inequalities by `arith_poly_norm_rel` (with an `arith_poly_norm` premise) and the
RARE rules `arith-elim-leq`, `arith-leq-norm` and `arith-int-geq-tighten`. A
normal form the checker rejects is not used.

Differences from cvc5:

* cvc5 builds mixed Int/Real sums, such as `(+ r x)` with `x : Int`; Logos's typing
  rejects them, so an integer leaf of a real sum keeps its `to_real`
  (`(+ r (to_real x))`, which is also how cvc5 prints that sum).
* Monomials are ordered by telos's structural term order where cvc5 uses node ids
  (`LeafNodeComparator`'s last case).
* `to_real` is removed from the sides of a division only when both have it, and
  an integer constant numerator is made real only when the denominator is an
  integer (`(/ 1 x)` is `(/ 1.0 (to_real x))`).
-/

open Eo

namespace Telos.Arith

open Node

/-! ## Terms -/

def isArithTerm (n : Node) : Bool :=
  match n.getKind with
  | .ADD | .SUB | .NEG | .MULT | .DIVISION => true
  | _ => false

/-- The normal form of an arithmetic term. When `ArithNormOk` holds, the step is
justified statically (`StaticProc.arithNorm`); otherwise it is checked by
`arith_poly_norm`. -/
def normalizeTerm (n : Node) : Option (Rw n) :=
  let p := Profile.time "strategy: arith normal form" (fun _ => "term") fun _ => polyOf n
  let m := p.toNode (isReal n)
  if m == n then none
  else if h : Profile.time "static: side conditions" (fun _ => "arith_poly_norm")
      (fun _ => decide (ArithNormOk n p m)) = true then
    some ⟨m, .static .arithNorm ⟨rfl, of_decide_eq_true h⟩ (.refl m)⟩
  else checkBy .arith_poly_norm n m

/-- `(to_real c)` for a constant `c`: the real constant, by `evaluate`. -/
def rewriteToReal (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[.const _] => byEvaluate n
  | _ => none

/-! ## Other operators -/

def intConst? : Node → Option Int
  | .const (.integer i) => some i
  | _ => none

/-- cvc5's `rewriteIntsDivMod`: `div` and `mod` by a nonzero constant are total. -/
def rewriteIntsDivMod (n : Node) : Option (Rw n) :=
  match n.getKind, n.getChildren with
  | .INTS_DIVISION, #[_, .const (.integer d)] =>
    if d == 0 then none else byRule "arith-int-div-total" n
  | .INTS_MODULUS, #[_, .const (.integer d)] =>
    if d == 0 then none else byRule "arith-int-mod-total" n
  | _, _ => none

/-- cvc5's `rewriteIntsDivModTotal`. -/
def rewriteIntsDivModTotal (n : Node) : Option (Rw n) :=
  let isDiv := n.getKind == .INTS_DIVISION_TOTAL
  let name (s : String) := (if isDiv then "arith-int-div-total-" else "arith-int-mod-total-") ++ s
  match n.getChildren with
  | #[t, d] =>
    match intConst? d with
    | some 0 => byRule (name "zero") n
    | some 1 => byRule (name "one") n
    | some k =>
      if k < 0 then
        -- `(div_total t (- k))` and `(mod_total t (- k))`, with `(- k)` evaluated.
        (byRule (name "neg") n).bind fun r => r.next? fun m =>
          if isDiv then Rw.congrArg m 0 fun g => Rw.congrArg g 1 byEvaluate
          else Rw.congrArg m 1 byEvaluate
      else if t.isConst then byEvaluate n
      else if !isDiv then
        match t.getKind with
        | .INTS_MODULUS_TOTAL =>
          if t.getChildren[1]? == some d then byRule "arith-mod-over-mod-1" n else none
        | .ADD => byRule "arith-mod-over-mod" n
        | .MULT => byRule "arith-mod-over-mod-mult" n
        | _ => none
      else divOverMod n t d
    | none => if isDiv then divOverMod n t d else none
  | _ => none
where
  /-- `(div_total (mod_total x d) d)` is `0`, for any `d`. -/
  divOverMod (n t d : Node) : Option (Rw n) :=
    if t.getKind == .INTS_MODULUS_TOTAL && t.getChildren[1]? == some d then
      byRule "arith-int-div-total-over-mod" n
    else none

/-- cvc5's `rewriteAbs`, `rewriteExtIntegerOp` and constant division: evaluate
constants; `(to_int (to_real x))` is `x` and `(is_int (to_real x))` is `true`
(cvc5 goes through `(is_int x)`, which Logos's typing rejects). -/
def rewriteOther (n : Node) : Option (Rw n) :=
  match n.getKind, n.getChildren with
  | .ABS, #[.const _] | .TO_INTEGER, #[.const _] | .IS_INTEGER, #[.const _] => byEvaluate n
  -- cvc5's `rewriteExtIntegerOp`, for constants (the rest is not ported).
  | .POW2, #[.const _] | .INTS_LOG2, #[.const _] | .INTS_ISPOW2, #[.const _] => byEvaluate n
  | .TO_INTEGER, #[.app (.kind .TO_REAL) _] => byRule "arith-to-int-elim-to-real" n
  | .IS_INTEGER, #[.app (.kind .TO_REAL) _] => byRule "arith-is-int-elim-to-real" n
  | .DIVISION_TOTAL, #[_, .const (.rational 0)] => byRule "arith-div-total-zero-real" n
  | .DIVISION_TOTAL, #[_, .const (.integer 0)] => byRule "arith-div-total-zero-int" n
  | _, _ => none

/-- cvc5's `rewriteDiv` removes `to_real` from the sides of a division by a
non-constant: `(/ (to_real x) (to_real y))` is `(/ x y)`, and likewise for
`/_total`, by `arith-div-int-to-real` (resp. `arith-div-total-int-to-real`)
read right to left. Removing it from one side only would give a mixed
division, which Logos's typing rejects. -/
def rewriteDivToReal (n : Node) : Option (Rw n) :=
  match n.getKind, n.getChildren with
  | .DIVISION, #[.app (.kind .TO_REAL) #[x], .app (.kind .TO_REAL) #[y]] =>
    symmRule .arith_div_int_to_real x y
  | .DIVISION_TOTAL, #[.app (.kind .TO_REAL) #[x], .app (.kind .TO_REAL) #[y]] =>
    symmRule .arith_div_total_int_to_real x y
  -- An integer constant numerator becomes real, e.g. (/ 1 x) is (/ 1.0 x); for
  -- an integer `x`, Logos's typing needs `(to_real x)`.
  | .DIVISION, #[c@(.const (.integer _)), y] | .DIVISION_TOTAL, #[c@(.const (.integer _)), y] =>
    if isInt y && !y.isConst then
      let r := if n.getKind == .DIVISION then CRule.arith_div_int_to_real else .arith_div_total_int_to_real
      (applyCmds (.cons (stepCmd r [c, y]) .nil) n).bind fun r =>
        r.next? fun t => Rw.congrArg t 0 byEvaluate
    else none
  | _, _ => none
where
  symmRule (r : CRule) (x y : Node) : Option (Rw n) :=
    applyCmds (.cons (stepCmd r [x, y]) (.cons (.step .symm .nil (.cons 0 .nil)) .nil)) n

/-! ## Inequalities -/

/-- `(= (* cx (- a b)) (* cy (- s c)))`, the premise of `arith_poly_norm_rel`. -/
def scaledEq (real : Bool) (cx cy : Rat) (x y : Node) : Node :=
  eqNode (mkNode .MULT #[constNode real cx, x]) (mkNode .MULT #[constNode real cy, y])

/-- `(r a b) = (r s c)` by `arith_poly_norm_rel`, where `cy (s - c) = cx (a - b)`
with `cx, cy > 0`. `x` and `y` are `(- a b)` and `(- s c)`, either wrapped in
`to_real` to give them the same type. -/
def polyNormRel (n : Node) (cx cy : Rat) (x y : Node) (target : Node) : Option (Rw n) :=
  let real := isReal x
  let a := mkNode .MULT #[constNode real cx, x]
  let b := mkNode .MULT #[constNode real cy, y]
  -- The premise `(= a b)` is justified statically when `ArithRelOk` holds.
  if h : Profile.time "static: side conditions" (fun _ => "arith_poly_norm_rel")
      (fun _ => decide (ArithRelOk n target a b)) = true then
    some ⟨target, .static (.arithRel a b) (show ArithRelOk n target a b from of_decide_eq_true h) (.refl _)⟩
  else
    byRuleWithPremises .arith_poly_norm_rel [eqNode n target]
      [stepCmd .arith_poly_norm [scaledEq real cx cy x y]] n

def toReal (t : Node) : Node := if isInt t then mkNode .TO_REAL #[t] else t

/-- `(>= (to_real s) c) = (>= s ⌈c⌉)` for an integer `s` and a non-integral `c`,
by `arith-int-geq-tighten`. -/
def tighten (s : Node) (c : Rat) (t : Node) : Option (Rw t) :=
  let toIntC := mkNode .TO_INTEGER #[constNode true c]
  -- Premises: `(= (= (to_real (to_int c)) c) false)` and `(= ⌈c⌉ (+ (to_int c) 1))`.
  let p₁ := stepCmd .evaluate [eqNode (mkNode .TO_REAL #[toIntC]) (constNode true c)]
  let p₂ := stepCmd .evaluate [mkNode .ADD #[toIntC, constNode false 1]]
  let p₂' := CCmd.step .symm .nil (.cons 0 .nil)
  let rule := CCmd.step .arith_int_geq_tighten
    (toArgList ([s, constNode true c, constNode false c.ceil].map Node.toEo)) (.cons 2 (.cons 0 .nil))
  applyCmds ([p₁, p₂, p₂', rule].foldr .cons .nil) t

/-- `(>= c s) = (<= s c) = (not (>= s (+ c 1))) = (not (>= s c+1))`, for an
integer `s` and an integer `c`. -/
def negTail (s : Node) (c : Rat) (t : Node) : Option (Rw t) := do
  let cN := constNode false c
  let r ← applyCmds (.cons (stepCmd .arith_elim_leq [s, cN])
    (.cons (.step .symm .nil (.cons 0 .nil)) .nil)) t
  let r ← r.next? (byRule "arith-leq-norm")
  r.next? fun t => Rw.congrArg t 0 fun g => Rw.congrArg g 1 byEvaluate

/-- Rewrite `(>= a b)` to cvc5's normal form (`buildIntegerInequality`,
`buildRealInequality`). -/
def normalizeGeq (n : Node) (a b : Node) : Option (Rw n) := do
  let sum := Profile.time "strategy: arith normal form" (fun _ => "inequality") fun _ =>
    (polyOf a).add ((polyOf b).scale (-1))
  let terms := sum.removeConstant
  let realSides := isReal a
  if terms.isEmpty then
    -- `a - b` is a constant `k`: (>= a b) = (>= 0 (- k)), then evaluate.
    let real := realSides || !sum.isIntegral
    let c := -sum.constant
    let zero := constNode real 0
    let cN := constNode real c
    let x := mkNode .SUB #[a, b]
    let r ← polyNormRel n 1 1 x (mkNode .SUB #[zero, cN]) (mkNode .GEQ #[zero, cN])
    r.next? byEvaluate
  else if sum.isIntegral then
    -- cvc5's normalizeGCDLCM, following the sign of the leading coefficient.
    let lc ← sum.leadingCoeff?
    let den : Nat := terms.foldl (fun acc (_, c) => Nat.lcm acc c.den) 1
    let num : Nat := terms.foldl (fun acc (_, c) => Nat.gcd acc c.num.natAbs) 0
    let μ : Rat := (den : Rat) / (num : Rat)
    let negate := lc < 0
    let μ := if negate then -μ else μ
    let scaled := sum.scale μ
    let s := scaled.removeConstant.toNode false
    let c := -scaled.constant
    let x := mkNode .SUB #[a, b]
    if !negate then
      if c.isInt then
        -- (>= a b) = (>= s c)
        let y := mkNode .SUB #[s, constNode false c]
        let (x, y) := if realSides then (x, mkNode .TO_REAL #[y]) else (x, y)
        polyNormRel n μ.num μ.den x y (mkNode .GEQ #[s, constNode false c])
      else
        -- (>= a b) = (>= (to_real s) c) = (>= s ⌈c⌉)
        let sR := mkNode .TO_REAL #[s]
        let target := mkNode .GEQ #[sR, constNode true c]
        let r ← polyNormRel n μ.num μ.den (toReal x) (mkNode .SUB #[sR, constNode true c]) target
        r.next? (tighten s c)
    else
      let μ := -μ
      if c.isInt then
        -- (>= a b) = (>= c s), then `negTail`
        let cN := constNode false c
        let y := mkNode .SUB #[cN, s]
        let (x, y) := if realSides then (x, mkNode .TO_REAL #[y]) else (x, y)
        let r ← polyNormRel n μ.num μ.den x y (mkNode .GEQ #[cN, s])
        r.next? (negTail s c)
      else
        -- (>= a b) = (>= (to_real (- s)) (- c)) = (>= (- s) ⌈- c⌉) = (>= ⌊c⌋ s),
        -- then `negTail`
        let ns := (scaled.removeConstant.scale (-1)).toNode false
        let nsR := mkNode .TO_REAL #[ns]
        let nc := constNode true (-c)
        let r ← polyNormRel n μ.num μ.den (toReal x) (mkNode .SUB #[nsR, nc]) (mkNode .GEQ #[nsR, nc])
        let r ← r.next? (tighten ns (-c))
        let k := constNode false (-c).ceil
        let fc := constNode false c.floor
        r.next? fun t => do
          let r ← polyNormRel t 1 1 (mkNode .SUB #[ns, k]) (mkNode .SUB #[fc, s]) (mkNode .GEQ #[fc, s])
          r.next? (negTail s c.floor)
  else
    -- cvc5's normalizeLCoeffAbsOne: divide by the absolute value of the leading
    -- coefficient.
    let lc := (sum.leadingCoeff?).getD 1
    let l := if lc < 0 then -lc else lc
    let scaled := sum.scale (1 / l)
    let s := scaled.removeConstant.toNode true
    let c := -scaled.constant
    let cN := constNode true c
    polyNormRel n l.den l.num (mkNode .SUB #[toReal a, toReal b]) (mkNode .SUB #[s, cN])
      (mkNode .GEQ #[s, cN])

/-- cvc5's `postRewriteAtom` for an equality of arithmetic terms: `true` for
equal sides, and the value of an equality of constants. -/
def rewriteEq (n : Node) : Option (Rw n) :=
  match n.getChildren with
  | #[a, b] =>
    if !(isInt a || isReal a) then none
    else if a == b then byRule "eq-refl" n
    else if a.isConst && b.isConst then byEvaluate n
    else normalizeEq n a b
  | _ => none
where
  /-- cvc5's `normalizeEquality`, of which the arithmetic rewriter keeps only a
  constant result, or else the orientation: since cvc5 PR #12833, the rewritten
  form of `(= a b)` is one of `true`, `false`, `(= a b)` and `(= b a)`, so that
  rewriting preserves the terms of an equality (for theory combination). The
  full normalization (solving for a term) is cvc5's `ppStaticRewrite` and
  extended rewriter, not its rewriter. -/
  normalizeEq (n a b : Node) : Option (Rw n) := do
    let sum := Profile.time "strategy: arith normal form" (fun _ => "equality") fun _ =>
      (polyOf a).add ((polyOf b).scale (-1))
    let terms := sum.removeConstant
    let real := isReal a
    let x := mkNode .SUB #[a, b]
    if terms.isEmpty then
      -- `a - b` is a constant `k`: (= a b) = (= 0 (- k)), then evaluate.
      let zero := constNode real 0
      let cN := constNode real (-sum.constant)
      let r ← polyNormRel n 1 1 x (mkNode .SUB #[zero, cN]) (mkNode .EQUAL #[zero, cN])
      r.next? byEvaluate
    else if sum.isIntegral then
      let den : Nat := terms.foldl (fun acc (_, c) => Nat.lcm acc c.den) 1
      let num : Nat := terms.foldl (fun acc (_, c) => Nat.gcd acc c.num.natAbs) 0
      let μ : Rat := (den : Rat) / (num : Rat)
      let scaled := sum.scale μ
      let c := -scaled.constant
      if !c.isInt then
        -- No integer solution: (= a b) = (= (to_real s) c) = false.
        let s := scaled.removeConstant.toNode false
        let sR := mkNode .TO_REAL #[s]
        let cN := constNode true c
        let r ← polyNormRel n μ.num μ.den (toReal x) (mkNode .SUB #[sR, cN]) (mkNode .EQUAL #[sR, cN])
        let toIntC := mkNode .TO_INTEGER #[cN]
        r.next? (byRuleWithPremises .arith_int_eq_conflict [s, cN]
          [stepCmd .evaluate [eqNode (mkNode .TO_REAL #[toIntC]) cN]])
      else
        -- Orient by the sign of the coefficient of least absolute value.
        let m := scaled.removeConstant.sorted.foldl (fun best (mono, d) =>
          match best with
          | some (_, e) => if (if d < 0 then -d else d) < (if e < 0 then -e else e)
              then some (mono, d) else best
          | none => some (mono, d)) none
        if (m.map (fun (_, d) => decide (d < 0))).getD false then byRule "eq-symm" n else none
    else
      -- Orient by the sign of the leading coefficient.
      if ((sum.leadingCoeff?).map (fun d => decide (d < 0))).getD false then byRule "eq-symm" n
      else none

/-- cvc5's `postRewriteAtom` for `>=` and `<=`. -/
def rewriteIneq (n : Node) : Option (Rw n) :=
  match n.getKind, n.getChildren with
  | .GEQ, #[a, b] => finish (normalizeGeq n a b)
  | .LEQ, #[_, _] =>
    (byRule "arith-elim-leq" n).bind fun r => (r.next? fun t =>
      match t.getChildren with
      | #[a, b] => normalizeGeq t a b
      | _ => none) |> finish
  | _, _ => none
where
  /-- Evaluate a comparison of constants, and drop a rewrite that changes
  nothing. -/
  finish {n : Node} (r : Option (Rw n)) : Option (Rw n) :=
    r.map fun r => r.next fun t =>
      match t.getKind, t.getChildren with
      | .GEQ, #[.const _, .const _] => byEvaluate t
      | .NOT, #[.app (.kind .GEQ) #[.const _, .const _]] =>
        (byEvaluate t)
      | _, _ => none

/-! ## The rewriter -/

def preRewrite (n : Node) : RewriteResponse n :=
  let r : Option (Rw n) := match n.getKind with
    | .GT => byRule "arith-elim-gt" n
    | .LT => byRule "arith-elim-lt" n
    | _ => none
  match r with
  | some ⟨m, h⟩ => ⟨.REWRITE_DONE, m, h⟩
  | none => .done n

def postRewrite (n : Node) : RewriteResponse n :=
  -- Rewrites to other operators are rewritten again from the start, as cvc5's
  -- `returnRewrite` does (`REWRITE_AGAIN_FULL`).
  let r : Option (RewriteStatus × Rw n) :=
    if isArithTerm n then
      match (.REWRITE_AGAIN_FULL, ·) <$> (if n.getKind == .DIVISION then rewriteDivToReal n else none) with
      | some r => some r
      | none => (.REWRITE_DONE, ·) <$> normalizeTerm n
    else match n.getKind with
      | .TO_REAL => (.REWRITE_DONE, ·) <$> rewriteToReal n
      | .GEQ | .LEQ => (.REWRITE_DONE, ·) <$> rewriteIneq n
      | .EQUAL => (.REWRITE_DONE, ·) <$> rewriteEq n
      | .INTS_DIVISION | .INTS_MODULUS => (.REWRITE_AGAIN_FULL, ·) <$> rewriteIntsDivMod n
      | .INTS_DIVISION_TOTAL | .INTS_MODULUS_TOTAL =>
        (.REWRITE_AGAIN_FULL, ·) <$> rewriteIntsDivModTotal n
      | .DIVISION_TOTAL =>
        (.REWRITE_AGAIN_FULL, ·) <$> (rewriteDivToReal n).orElse fun _ => rewriteOther n
      | _ => (.REWRITE_AGAIN_FULL, ·) <$> rewriteOther n
  match r with
  | some (st, ⟨m, h⟩) => if m == n then .done n else ⟨st, m, h⟩
  | none => .done n

end Telos.Arith

namespace Telos

/-- The arithmetic rewriter. -/
def TheoryRewriter.arith : TheoryRewriter where
  preRewrite := Arith.preRewrite
  postRewrite := Arith.postRewrite

end Telos
