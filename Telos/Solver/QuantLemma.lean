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
  `alpha_equiv` of each to its canonical variables, then the order of the
  children of commutative operators by congruence (`aci_norm`, `eq-symm`,
  `arith_poly_norm`, ...) and that of the variables by `quant_var_reordering`
  (`alphaProof`).

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

/-! ## Alpha-equivalence -/

/-- `n` without the annotations of its quantifiers (its CPC term is that of `n`). -/
partial def dropPatterns (n : Node) : Node :=
  match n with
  | .app op@(.kind k) cs =>
    let cs := if (k == .FORALL || k == .EXISTS) && cs.size > 2 then cs.extract 0 2 else cs
    .app op (cs.map dropPatterns)
  | .app op cs => .app op (cs.map dropPatterns)
  | n => n

/-- `n` with its variables renamed, binders included (as `$rename_simul`). -/
partial def renameVars (σ : Std.HashMap Key Node) (n : Node) : Node :=
  match n with
  | .boundVar .. => (σ.get? ⟨n⟩).getD n
  | .app op cs => .app op (cs.map (renameVars σ))
  | .skolem id cs => .skolem id (cs.map (renameVars σ))
  | n => n

/-- `n` with the children of its commutative operators sorted, for `n` with
canonical variables. -/
partial def sortComm (n : Node) : Node :=
  match n with
  | .app op cs =>
    let ds := cs.map sortComm
    match op with
    | .kind k => if Quant.isCommKind k then .app op (ds.qsort (Quant.termOrder Node.lt)) else .app op ds
    | _ => .app op ds
  | n => n

/-- The fact `(= a b)`, for `a` and `b` with the same `sortComm`, at its
position; `none` if they are the same. -/
partial def sameSorted (a b : Node) : EmitM (Option Nat) := do
  if a == b then return none
  match a, b with
  | .app op cs, .app op' ds =>
    if op != op' || cs.size != ds.size then throw "another operator"
    -- the children of `a` in the order of `b`
    let mut mid := cs
    let comm := match op with
      | .kind k => Quant.isCommKind k
      | _ => false
    if comm then
      mid := #[]
      let mut rest := cs.toList.map fun c => (c, sortComm c)
      for d in ds do
        let s := sortComm d
        let some i := rest.findIdx? (·.2 == s) | throw "no child to pair"
        mid := mid.push rest[i]!.1
        rest := rest.eraseIdx i
    let c := Node.app op mid
    let mut chain : Array Nat := #[]
    if mid != cs then
      let eq := Node.eqNode a c
      chain := chain.push (← match op with
        | .kind .AND | .kind .OR => push ⟨.aci_norm, [.node eq], [], .step⟩
        | .kind .EQUAL => push ⟨.eq_symm, cs.toList.map .node, [], .step⟩
        | .kind .ADD | .kind .MULT => push ⟨.arith_poly_norm, [.node eq], [], .step⟩
        | .kind .XOR => push ⟨.bool_xor_comm, cs.toList.map .node, [], .step⟩
        | .kind .SET_UNION => push ⟨.sets_union_comm, cs.toList.map .node, [], .step⟩
        | .kind .SET_INTER => push ⟨.sets_inter_comm, cs.toList.map .node, [], .step⟩
        | _ => throw "an operator not reordered")
    if c != b then
      match op with
      | .kind k =>
        if k == .FORALL || k == .EXISTS then
          if mid[0]! != ds[0]! then throw "other variables"
          let some e ← sameSorted mid[1]! ds[1]! | throw "unreachable"
          chain := chain.push (← congStep c op [e])
        else chain := chain.push (← congAll op c mid ds)
      | _ => chain := chain.push (← congAll op c mid ds)
    return some (← closeChain a chain)
  | _, _ => throw "terms that differ"
where
  congAll (op : Op) (c : Node) (cs ds : Array Node) : EmitM Nat := do
    let mut eqs : List Nat := []
    for (x, y) in cs.zip ds do
      let p ← match ← sameSorted x y with
        | some p => pure p
        | none => push ⟨.refl, [.node x], [], .step⟩
      eqs := eqs ++ [p]
    congStep c op eqs

/-- The fact `(= q' q)`, for alpha-equivalent formulas: both renamed to their
canonical variables, then the orders of children and variables. -/
def alphaProof (q' q : Node) : EmitM Nat := do
  let q' := dropPatterns q'
  let q := dropPatterns q
  let rename (r : Node) : EmitM (Node × Nat) := do
    let m := ((Quant.canonical Node.lt (Quant.quantBody r)).run ({}, {})).2.1
    let σ : Std.HashMap Key Node := m.fold (fun σ k v => match k.1 with
      | .boundVar .. => σ.insert k v
      | _ => σ) {}
    let vs := (σ.toList.map (·.1.1)).toArray.qsort Node.lt
    let ts := vs.map fun v => (σ.get? ⟨v⟩).getD v
    let p ← push ⟨.alpha_equiv, [.node r, .term (eoList (vs.toList.map Node.toEo)),
      .term (eoList (ts.toList.map Node.toEo))], [], .step⟩
    return (renameVars σ r, p)
  let (a, pa) ← rename q'
  let (b, pb) ← rename q
  let mut chain := #[pa]
  -- the body of `a`, as that of `b`
  let a1 := match a with
    | .app op cs => Node.app op (cs.set! 1 (Quant.quantBody b))
    | a => a
  if a1 != a then
    if let some e ← sameSorted (Quant.quantBody a) (Quant.quantBody b) then
      chain := chain.push (← congStep a (.kind .FORALL) [e])
  if a1 != b then chain := chain.push (← push ⟨.quant_var_reordering, [.node (Node.eqNode a1 b)], [], .step⟩)
  chain := chain.push (← push ⟨.symm, [], [pb], .step⟩)
  closeChain q' chain

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
  -- by their canonical variables (`alphaProof`)
  if l.id == "QUANTIFIERS_REDUCE_ALPHA_EQ" then
    let .app (.kind .EQUAL) #[q', q] := l.lem | none
    let cmds : List CCmd ← if q'.toEo == q.toEo then
        some [.step .refl (.cons q'.toEo .nil) .nil]
      else
        match (alphaProof q' q).run {} with
        | .ok (_, st) => some (toCmds st.steps)
        | .error _ => none
    let p := EqProof.eqTrue (.valid l.lem cmds)
    if EqProof.check #[] p == some (l.lem, Node.mkTrue) then return p
    none
  if l.skolemize.isSome then
    let .app (.kind .IMPLIES) #[h, c] := l.lem | none
    let p ← underAssumption h c .skolemize []
    return ← DtLemma.forFormula l.lem l.lem p
  none

end Telos.Solver.QuantLemma
