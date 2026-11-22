import Telos.Solver.DtLemma
import Telos.Solver.Theory.QuantState
import Telos.Solver.Theory.QuantAlpha

/-!
# Certificates of the quantifier lemmas

The lemmas of the quantifiers engine (`Telos/Solver/Theory/Quantifiers.lean`)
are valid. `prove l` gives an `EqProof` of `(l.lem, true)` from no assumptions:
- an instance `(=> q body)`, `body` the body of `q` with its variables replaced
  by the terms: under `q`, `instantiate` with the terms, then `scope`; then
  the rewrite of the lemma (`DtLemma.forFormula`);
- a skolemization `(=> (not q) (not body[k]))` for the skolems
  `(@quantifiers_skolemize q i)`: under `(not q)`, `skolemize`, then `scope`;
- a purification `(= k t)` of a ground term of a trigger
  (`QUANTIFIERS_GT_PURIFY`): `skolem_intro`;
- the congruence of two terms the equality engine has disequal
  (`QUANTIFIERS_TDB_DEQ_CONG`): under the equalities of their arguments,
  `cong`, then `scope`;
- an alpha-equivalence `(= q' q)` (`QUANTIFIERS_REDUCE_ALPHA_EQ`): `refl` when
  the two have the same CPC term (they differ in their annotations), else
  `alpha_equiv` renaming the variables as their canonical forms pair them (not
  certified when it takes more, such as reordering variables).

The proofs are checked when they are made (`EqProof.check`, and Logos's checker
for their CPC steps).
-/

open Eo

namespace Telos.Solver.QuantLemma

open Proof

/-- The CPC proof of `(=> h F)` by one rule, with the arguments `args`, from
the assumption `h`. -/
def underAssumption (h F : Node) (r : CRule) (args : List PArg) : Option EqProof :=
  let act : EmitM Unit := do
    let p ← push ⟨.refl, [.node h], [], .assume⟩
    let c ← push ⟨r, args, [p], .step⟩
    let _ ← push ⟨.scope, [], [c], .pop⟩
  match act.run {} with
  | .ok ((), st) => some (.valid (Node.mkNode .IMPLIES #[h, F]) (toCmds st.steps))
  | .error _ => none

/-- **A proof of `(l.lem, true)`** from no assumptions, for a lemma of the
quantifiers engine. -/
def prove (l : Quant.Lemma) : Option EqProof := do
  if let some (q, ts, lem₀) := l.inst then
    let .app (.kind .IMPLIES) #[_, body] := lem₀ | none
    let p ← underAssumption q body .instantiate [.term (eoList (ts.toList.map Node.toEo))]
    if let some r := DtLemma.forFormula lem₀ l.lem p then return r
    -- the lemma rewritten at its order
    let o ← l.order
    let r := if l.lem == lem₀ then p else .trans (.rwAt o l.lem) (.trans (.symm (.rwAt o lem₀)) p)
    if EqProof.check #[] r == some (l.lem, Node.mkTrue) then return r
    none
  -- a purification of a ground term of a trigger, `(= k t)` for the skolem
  -- `k` of `t`: `skolem_intro`
  if l.id == "QUANTIFIERS_GT_PURIFY" then
    let .app (.kind .EQUAL) #[k@(.skolem .PURIFY #[_]), _] := l.lem | none
    let p := EqProof.eqTrue (.valid l.lem [DT.argStep .skolem_intro k])
    if EqProof.check #[] p == some (l.lem, Node.mkTrue) then return p
    none
  -- two congruent terms the equality engine has disequal
  -- (`QUANTIFIERS_TDB_DEQ_CONG`), `(=> ante (= t₁ t₂))` with `ante` the
  -- equalities of their arguments that differ: under `ante`, `cong`
  if l.id == "QUANTIFIERS_TDB_DEQ_CONG" then
    let .app (.kind .IMPLIES) #[ante, .app (.kind .EQUAL) #[a0, b0]] := l.lem | none
    let .app op as := a0 | none
    let .app op' bs := b0 | none
    if op != op' || as.size != bs.size then none
    let ndiff := ((as.zip bs).filter fun (a, b) => a != b).size
    let act : EmitM Unit := do
      let h ← push ⟨.refl, [.node ante], [], .assume⟩
      let mut eqs : List Nat := []
      let mut j := 0
      for (a, b) in as.zip bs do
        if a == b then eqs := eqs ++ [← push ⟨.refl, [.node a], [], .step⟩]
        else if ndiff == 1 then eqs := eqs ++ [h]
        else
          eqs := eqs ++ [← push ⟨.and_elim, [.term (Eo.Term.Numeral j)], [h], .step⟩]
          j := j + 1
      let c ← congStep a0 op eqs
      let _ ← push ⟨.scope, [], [c], .pop⟩
    match act.run {} with
    | .ok ((), st) =>
      let p := EqProof.valid l.lem (toCmds st.steps)
      if EqProof.check #[] p == some (l.lem, Node.mkTrue) then return p
      none
    | .error _ => none
  -- an alpha-equivalence, `(= q' q)` (`QUANTIFIERS_REDUCE_ALPHA_EQ`): `refl`
  -- when their CPC terms are the same (they differ in their annotations), else
  -- `alpha_equiv`, renaming the variables of `q'` to those of `q` as the
  -- canonical forms pair them
  if l.id == "QUANTIFIERS_REDUCE_ALPHA_EQ" then
    let .app (.kind .EQUAL) #[q', q] := l.lem | none
    let cmds : List CCmd ← if q'.toEo == q.toEo then
        some [.step .refl (.cons q'.toEo .nil) .nil]
      else
        let canon (r : Node) : Std.HashMap Key Node := ((Quant.canonical Node.lt (Quant.quantBody r)).run ({}, {})).2.1
        let m1 := canon q'
        let m2 := canon q
        let inv : Std.HashMap Key Node := (Quant.quantVars q).foldl (fun m w =>
          match m2.get? ⟨w⟩ with
          | some c => m.insert ⟨c⟩ w
          | none => m) {}
        let ws ← (Quant.quantVars q').mapM fun v => (m1.get? ⟨v⟩).bind (inv.get? ⟨·⟩)
        some [.step .alpha_equiv
          (.cons q'.toEo (.cons (eoList ((Quant.quantVars q').toList.map Node.toEo))
            (.cons (eoList (ws.toList.map Node.toEo)) .nil))) .nil]
    let p := EqProof.eqTrue (.valid l.lem cmds)
    if EqProof.check #[] p == some (l.lem, Node.mkTrue) then return p
    none
  if l.skolemize.isSome then
    let .app (.kind .IMPLIES) #[h, c] := l.lem | none
    let p ← underAssumption h c .skolemize []
    return ← DtLemma.forFormula l.lem l.lem p
  none

end Telos.Solver.QuantLemma
