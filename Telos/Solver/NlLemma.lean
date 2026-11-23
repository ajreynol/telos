import Telos.Solver.DtLemma
import Telos.Solver.StringsCore
import Telos.Solver.Theory.Arith.Nl.Ext

/-!
# Certificates of the nonlinear extension's lemmas

A lemma of the nonlinear extension (`Telos/Solver/Theory/Arith/Nl/Ext.lean`)
is valid. `prove l` gives an `EqProof` of `(lem, true)` from no assumptions,
by the CPC rule cvc5's proof uses, or by substitution and the rewriter:
- `ARITH_NL_SIGN`, `(=> (= v 0) (= m 0))`: under the assumption, congruence
  substitutes `0` for `v` in `m`, and the rewriter makes the product `0`
  (cvc5's `MACRO_SR_PRED_INTRO`), then `scope`;
- `ARITH_NL_SIGN`, `(=> antec (r m 0))`: `arith_mult_sign`;
- `ARITH_NL_TANGENT_PLANE`: `arith_mult_tangent`;
- `ARITH_NL_INFER_BOUNDS_NT`: `arith_mult_pos` or `arith_mult_neg` on the
  bound as the check states it, related to the lemma by their rewrites
  (cvc5's `MACRO_SR_PRED_TRANSFORM`);
- `ARITH_NL_FACTOR`: the skolem's definition by `skolem_intro`; the factoring
  lemma by substituting the definition, after which it rewrites to `true`;
- `ARITH_NL_FLATTEN_MON`, `EXTT_SIMPLIFY`: under the assumptions, congruence
  substitutes the equalities (to a fixed point), and the two sides have the
  same rewrite;
- the splits, `(or eq (not eq))`: `split`.

- `ARITH_NL_COMPARISON`, `(=> exp conc)`, as cvc5's
  `ArithNlCompareProofGenerator`: each comparison literal of the explanation,
  which states `|a| ⋈ |b|` without `abs`, as `(⋈ (abs a) (abs b))` (the RARE
  rules `arith-abs-eq`, `arith-abs-int-gt`, `arith-abs-real-gt`, which cvc5's
  proof leaves as trusted steps), repeated to match the exponents of the
  conclusion, strict comparisons guarded by disequalities to zero; then
  `arith_mult_abs_comparison`, the rewriter, and the RARE rule back to the
  conclusion's form.

Every proof is checked when it is made (`EqProof.check`); a lemma whose proof
does not check has none.
-/

open Eo

namespace Telos.Solver.NlLemma

open Arith.Nl

/-- A CPC step of rule `r` with the arguments `args`, from no premises. -/
def stepArgs (r : CRule) (args : List Node) : CCmd :=
  .step r (args.foldr (fun a acc => .cons a.toEo acc) .nil) .nil

/-- A proof of `(t, t')` that replaces, below `t`, each leaf `x` with a proof
`(x, s)` in `σ` by `s` (by congruence), with `t'`; `none` if nothing
changes. -/
partial def substProof (σ : Node → Option EqProof × Option Node) (t : Node) : Option (EqProof × Node) :=
  match σ t with
  | (some p, some s) => some (p, s)
  | _ =>
    match t with
    | .app op cs =>
      if !op.eoShape.substCongruent then none else
      let rs := cs.map (substProof σ)
      if rs.all Option.isNone then none
      else
        let args := rs.map (·.map (·.1))
        let cs' := (cs.zip rs).map fun (c, r) => (r.map (·.2)).getD c
        some (.congAt t args, .app op cs')
    | _ => none

/-- The assumptions of a lemma `(=> h F)` as proofs: a conjunction's
conjuncts, or `h` itself, each giving what it gives as an assumption. -/
def assumptions (h : Node) : Array (Node × EqProof) :=
  match h with
  | .app (.kind .AND) ls => ls.mapIdx fun i l => (l, .fromTrue (.andElim i (.assume 0)))
  | l => #[(l, .assume 0)]

/-- The substitution of the equalities `(= x s)` among the assumptions. -/
def eqSubst (as : Array (Node × EqProof)) (t : Node) : Option EqProof × Option Node :=
  match as.find? fun (l, _) => match l with
      | .app (.kind .EQUAL) #[x, _] => x == t
      | _ => false with
  | some (.app (.kind .EQUAL) #[_, s], p) => (some p, some s)
  | _ => (none, none)

/-- A proof of `(t, rewrite t*)`, for `t*` the fixed point of the
substitution of the assumptions' equalities in `t`. -/
def normalize (as : Array (Node × EqProof)) (t : Node) : EqProof × Node := Id.run do
  let mut p : Option EqProof := none
  let mut cur := t
  for _ in [0:as.size + 1] do
    match substProof (eqSubst as) cur with
    | some (q, c') =>
      p := some (match p with | some p => .trans p q | none => q)
      cur := c'
    | none => break
  let r := Telos.rewrite cur
  let q : EqProof := .rw cur
  return (match p with | some p => .trans p q | none => q, r)

/-- `(=> h (= a b))`, by substituting the equalities of `h` and rewriting
both sides. -/
def bySubst (h a b : Node) : Option EqProof := do
  let as := assumptions h
  let (pa, ra) := normalize as a
  let (pb, rb) := normalize as b
  if ra != rb then none
  DtLemma.implies h (Node.eqNode a b) (.trans pa (.symm pb))

/-- `F` from a proof `p : (G, true)` of `G` with the same rewrite. -/
def byRewrite (F G : Node) (p : EqProof) : EqProof :=
  if F == G then p else .trans (.rw F) (.trans (.symm (.rw G)) p)

/-! ## Comparisons (`ArithNlCompareProofGenerator`) -/

/-- `addProduct`: the factors of a side of a comparison. -/
partial def addProduct (n : Node) (acc : Array Node) : Array Node :=
  match n with
  | .app (.kind .TO_REAL) #[a] => addProduct a acc
  | _ => if isNlMult n then acc ++ n.getChildren else if valOf n == some 1 then acc else acc.push n

def stripToReal : Node → Node
  | .app (.kind .TO_REAL) #[a] => a
  | n => n

/-- `isDisequalZero`. -/
def isDiseqZero : Node → Option Node
  | .app (.kind .NOT) #[.app (.kind .EQUAL) #[v, z]] => if valOf z == some 0 then some v else none
  | _ => none

/-- Counts of factors. -/
abbrev Counts := Array (Node × Nat)
def cGet (m : Counts) (v : Node) : Nat := ((m.find? (·.1 == v)).map (·.2)).getD 0
def cSet (m : Counts) (v : Node) (k : Nat) : Counts :=
  match m.findIdx? (·.1 == v) with
  | some i => m.set! i (v, k)
  | none => m.push (v, k)
def cAdd (m : Counts) (v : Node) : Counts := cSet m v (cGet m v + 1)

/-- The comparison literal `(k (abs a) (abs b))`. -/
def absLit (k : Kind) (a b : Node) : Node :=
  Node.mkNode k #[Node.mkNode .ABS #[a], Node.mkNode .ABS #[b]]

/-- The RARE rule relating `(k (abs a) (abs b))` to cvc5's literal without
`abs` (`mkLit` with `isAbsolute`). -/
def absRule (k : Kind) (a : Node) : Option CRule :=
  if k == .EQUAL then some .arith_abs_eq
  else if k == .GT then some (if isRealTerm a then .arith_abs_real_gt else .arith_abs_int_gt)
  else none

/-- A premise of `arith_mult_abs_comparison`. -/
inductive CItem where
  /-- An explanation literal `e`, a comparison `(k |a| |b|)`. -/
  | cmp (e : Node) (k : Kind) (a b : Node)
  /-- `(= (abs v) (abs v))`. -/
  | refl (v : Node)
  deriving Inhabited

def CItem.kind : CItem → Kind
  | .cmp _ k _ _ => k
  | .refl _ => .EQUAL

/-- The left factor of a premise (`e[0][0]`). -/
def CItem.left : CItem → Node
  | .cmp _ _ a _ => a
  | .refl v => v

/-- The proof of a comparison lemma `(=> h conc)`. -/
def proveCompare (cmpLit? : Node → Option (Kind × Node × Node)) (lem : Node) : Option EqProof := do
  let .app (.kind .IMPLIES) #[h, conc] := lem | none
  let exp := match h with
    | .app (.kind .AND) ls => ls
    | l => #[l]
  -- the premises, and the disequalities to zero
  let mut items : Array CItem := #[]
  let mut deq : Array (Node × Node) := #[]
  for e in exp do
    match cmpLit? e with
    | some (k, a, b) => items := items.push (.cmp e k a b)
    | none =>
      let v ← isDiseqZero e
      deq := deq.push (v, e)
  let (ck, ca, cb) ← cmpLit? conc
  let cprod0 := addProduct ca #[]
  let cprod1 := addProduct cb #[]
  let mut m0 : Counts := cprod0.foldl cAdd #[]
  let mut m1 : Counts := cprod1.foldl cAdd #[]
  -- cancel the common factors
  let mut mcancel : Counts := #[]
  for (v, c0) in m0 do
    if m1.any (·.1 == v) then
      let n := min c0 (cGet m1 v)
      mcancel := cSet mcancel v n
      m0 := cSet m0 v (c0 - n)
      m1 := cSet m1 v (cGet m1 v - n)
  let mut eexp : Array Nat := #[]
  for it in items do
    let .cmp _ _ a b := it | continue
    let e0 := addProduct a #[]
    let e1 := addProduct b #[]
    if e0.isEmpty then
      let x := stripToReal e1[0]!
      let n := cGet m1 x - cGet m0 x
      m1 := cSet m1 x (cGet m1 x - n)
      eexp := eexp.push n
    else if e1.isEmpty then
      let x := stripToReal e0[0]!
      let n := cGet m0 x - cGet m1 x
      m0 := cSet m0 x (cGet m0 x - n)
      eexp := eexp.push n
    else
      let x := stripToReal e0[0]!
      let y := stripToReal e1[0]!
      let n := min (cGet m0 x) (cGet m1 y)
      m0 := cSet m0 e0[0]! (cGet m0 e0[0]! - n)
      m1 := cSet m1 e1[0]! (cGet m1 e1[0]! - n)
      eexp := eexp.push n
  for (v, c) in mcancel do m0 := cSet m0 v (cGet m0 v + c)
  for (v, c) in m0 do
    if c > 0 then
      items := items.push (.refl v)
      eexp := eexp.push c
  -- a strict conclusion: a strict premise first, the others guarded
  if ck == .GT then
    match (List.range items.size).find? fun i => items[i]!.kind == .GT && eexp[i]! > 0 with
    | some i =>
      if i > 0 then
        let t := items[i]!
        items := (items.set! i items[0]!).set! 0 t
        let te := eexp[i]!
        eexp := (eexp.set! i eexp[0]!).set! 0 te
    | none => pure ()
    if items[0]?.map CItem.kind != some .GT then none
  -- the CPC proof
  let act : StringsCore.M Unit := do
    let p ← Proof.push ⟨.refl, [.node h], [], .assume⟩
    let ih ← StringsCore.known h p
    -- the explanation's literals
    let mut lits : Array (Node × Nat) := #[]
    if exp.size == 1 then lits := #[(h, ih)]
    else
      for i in [0:exp.size] do
        let q ← Proof.push ⟨.and_elim, [.term (Term.Numeral i)], [p], .step⟩
        lits := lits.push (exp[i]!, ← StringsCore.known exp[i]! q)
    let litIdx := fun (l : Node) => (lits.find? (·.1 == l)).map (·.2)
    -- each premise's fact, guarded if needed
    let mut facts : Array Nat := #[]
    for it in items do
      let (lit, i) ← match it with
        | .cmp e k a b =>
          let some r := absRule k a | throw "a comparison of another kind"
          let some ie := litIdx e | throw "a literal not in the explanation"
          let (_, ieq) ← StringsCore.rule r [.node a, .node b] []
          -- `(k |a| |b|)` from `(= (k |a| |b|) e)` and `e`
          StringsCore.litFact (.trans (.assume ieq) (StringsCore.atomProof e ie))
        | .refl v =>
          let (_, i) ← StringsCore.rule .refl [.node (Node.mkNode .ABS #[v])] []
          pure (Node.eqNode (Node.mkNode .ABS #[v]) (Node.mkNode .ABS #[v]), i)
      if ck == .GT && it.kind != .GT then
        let t := it.left
        let z := zeroOf t
        let tgt := Node.notNode (Node.eqNode t z)
        let jd ← if t.isConst then
            let (_, j) ← StringsCore.litFact (.rw tgt)
            pure j
          else
            let some (_, e) := deq.find? fun (v, _) => v == t || (stripToReal t != t && v == stripToReal t)
              | throw "no disequality to zero for a premise"
            let some ie := litIdx e | throw "a literal not in the explanation"
            if e == tgt then pure ie
            else
              -- `(not (= v 0))` as `(not (= (to_real v) 0.0))`, by their rewrites
              let .app (.kind .NOT) #[ea] := e | throw "not a disequality"
              let (_, j) ← StringsCore.litFact (.trans (.rw (Node.eqNode t z))
                (.trans (.symm (.rw ea)) (StringsCore.atomProof e ie)))
              pure j
        let (_, g) ← StringsCore.rule .and_intro [] [i, jd]
        let _ := lit
        facts := facts.push g
      else facts := facts.push i
    -- the premises, repeated as the exponents ask
    let mut prems : Array Nat := #[]
    for k in [0:facts.size] do
      for _ in [0:eexp[k]!] do prems := prems.push facts[k]!
    let (newConc, inc) ← StringsCore.rule .arith_mult_abs_comparison [] prems.toList
    -- the comparison of the conclusion, by rewriting
    let concc := absLit ck ca cb
    let (_, icc) ← StringsCore.litFact (.trans (.rw concc) (.trans (.symm (.rw newConc)) (StringsCore.atomProof newConc inc)))
    -- the conclusion's form
    let some r := absRule ck ca | throw "a comparison of another kind"
    let (_, ieq) ← StringsCore.rule r [.node ca, .node cb] []
    let (_, ic) ← StringsCore.litFact (.trans (.symm (.assume ieq)) (StringsCore.atomProof concc icc))
    let _ ← Proof.push ⟨.scope, [], [← StringsCore.posOf ic], .pop⟩
  match (act.run {}).run {} with
  | .ok (((), _), st) => some (.valid lem (Proof.toCmds st.steps))
  | .error _ => none

/-- **A proof of `(lem, true)`** for the lemma `l`. -/
def proveRaw (cmpLit? : Node → Option (Kind × Node × Node)) (l : Lemma) : Option EqProof := do
  match l.info, l.lem with
  | .compare, lem => proveCompare cmpLit? lem
  | .zero v m, .app (.kind .IMPLIES) #[h, conc@(.app (.kind .EQUAL) #[_, z])] =>
    -- `m[v := 0]` rewrites to `0`
    let (p, m') ← substProof (fun t => if t == v then (some (.assume 0), some (zeroOf v)) else (none, none)) m
    if Telos.rewrite m' != z then none
    DtLemma.implies h conc (.trans p (.rw m'))
  | .sign antec m, lem =>
    some (.valid lem [stepArgs .arith_mult_sign [antec, m]])
  | .tangent a b av bv geq, lem =>
    some (.eqTrue (.valid lem [stepArgs .arith_mult_tangent [a, b, av, bv, Node.mkBool geq]]))
  | .bound mult simple pos, lem@(.app (.kind .IMPLIES) #[.app (.kind .AND) #[guard, _], infer]) =>
    let tmp := Node.mkNode .IMPLIES #[Node.mkNode .AND #[guard, simple], infer]
    let r := if pos then CRule.arith_mult_pos else .arith_mult_neg
    some (byRewrite lem tmp (.valid tmp [stepArgs r [mult, simple]]))
  | .split eq, lem => some (.valid lem [DT.argStep .split eq])
  | .factorDef, lem@(.app (.kind .EQUAL) #[k, _]) =>
    some (.eqTrue (.valid lem [DT.argStep .skolem_intro k]))
  | .factor _ k sum, lem =>
    let pk : EqProof := .valid (Node.eqNode k sum) [DT.argStep .skolem_intro k]
    let (p, lem') ← substProof (fun t => if t == k then (some pk, some sum) else (none, none)) lem
    if Telos.rewrite lem' != Node.mkTrue then none
    some (.trans p (.rw lem'))
  | .flatten, .app (.kind .IMPLIES) #[h, .app (.kind .EQUAL) #[a, b]] => bySubst h a b
  | .extt, .app (.kind .IMPLIES) #[h, .app (.kind .EQUAL) #[a, b]] => bySubst h a b
  | .extt, .app (.kind .EQUAL) #[a, b] =>
    if Telos.rewrite a == Telos.rewrite b then some (.eqTrue (.trans (.rw a) (.symm (.rw b)))) else none
  | _, _ => none

/-- The proof of `l`, if it checks. -/
def prove (cmpLit? : Node → Option (Kind × Node × Node)) (l : Lemma) : Option EqProof := do
  let p ← proveRaw cmpLit? l
  if EqProof.check #[] p == some (l.lem, Node.mkTrue) then some p else none

end Telos.Solver.NlLemma
