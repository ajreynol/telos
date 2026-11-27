import Telos.Rewriter.Rewrite
import Telos.Rewriter.Theory.Strings

/-!
# Length-based unification of string equalities

cvc5's `rewriteViaStrEqLenUnifyPrefix` (`STR_EQ_CONJ_LEN_ENTAIL`), a case of
`rewriteStrEqualityExt`: for `(= x (str.++ y₁ … yₙ))` where the lengths entail
`(str.len x) ≤ Σᵢ∈K (str.len yᵢ)` for a subset `K` of the components
(`StringsEntail::inferEqsFromContains`, by `ArithEntail::inferZerosInSumGeq`),
the other components are empty:
`(and (= x (str.++ yᵢ…)ᵢ∈K) (= yⱼ "")ⱼ∉K)`.

cvc5 elaborates it with two trusted subgoals (`MACRO_STR_EQ_LEN_UNIFY_PREFIX`).
telos proves it in CPC, both ways, then `bool-dual-impl-eq`:
- under the equality, for each `yⱼ` that is empty: the length entailment of the
  components but `yⱼ`, `(>= Σᵢ≠ⱼ (str.len yᵢ) (str.len x))`, proven by
  `ArithEntail.proveGeq`, with `(str.len x)` replaced by the length of the
  concatenation (congruence), rewrites to `(not (>= (str.len yⱼ) 1))`, which
  is the negation of the rewrite of `(> (str.len yⱼ) 0)`; with
  `string_length_pos`, `yⱼ` is empty. Then the concatenation, with the empty
  components replaced, rewrites to that of the others;
- under the conjunction, the same replacement gives the equality back.

Also `rewriteViaStrEqLenUnify`'s split (`SPLIT_EQ`, `strEqLenUnify`): a semantic
step (`SemProc.strSplit`, `Telos/Core/StrSplit.lean`), proven an equivalence
once, so no checker runs; `strSplitE` prints its CPC proof, as cvc5 elaborates
`MACRO_STR_EQ_LEN_UNIFY`.
-/

namespace Telos.Preprocess

open Node StringsRewriter Proof

def lenNode (t : Node) : Node := mkNode .STRING_LENGTH #[t]

/-- The sum of the terms: `0`, the term, or their `+`. -/
def lenSum : List Node → Node
  | [] => .const (.integer 0)
  | [a] => a
  | ts => mkNode .ADD ts.toArray

/-- `ArithEntail::inferZerosInSumGeq` on the lengths of the components `cs`
(by position): the positions kept, and those whose lengths can be zero while
`Σ ≥ (str.len x)` still holds; `none` if it does not hold at all. -/
def inferZeros (x : Node) (cs : List Node) : Option (List Nat × List Nat) := do
  let lx := lenNode x
  let sumOf (ps : List Nat) : Node := lenSum (ps.map fun p => lenNode cs[p]!)
  let all := List.range cs.length
  if !ArithEntail.check2 (sumOf all) lx then none
  let mut keep := all
  let mut zeros : List Nat := []
  let mut i := 0
  while i < keep.length do
    let p := keep[i]!
    let rest := keep.eraseIdx i
    if ArithEntail.check2 (sumOf rest) lx then
      zeros := zeros ++ [p]
      keep := rest
    else i := i + 1
  return (keep, zeros)

/-- The fact `(= t r)` for `r` the rewrite of `t`, and `r`. -/
def lenRwFact (t : Node) : EmitM (Node × Nat) := do
  let r := Telos.rewriteCert t
  return (r.1, ← closeChain t (← emitChain r.2))

/-- The fact `(= y y')` for the concatenation `y` with the components at the
positions of `zs` replaced by `""`, by the facts `(= yⱼ "")` (`zf`, by
position), then rewritten: `y'`. -/
def lenEmptyComponents (y : Node) (zf : List (Nat × Nat)) : EmitM (Node × Nat) := do
  let cs := y.getChildren
  let mut eqs : List Nat := []
  for j in [0:cs.size] do
    match zf.lookup j with
    | some f => eqs := eqs ++ [f]
    | none => eqs := eqs ++ [← push ⟨.refl, [.node cs[j]!], [], .step⟩]
  let c ← congStep y (.kind .STRING_CONCAT) eqs
  let yc := mkNode .STRING_CONCAT (cs.mapIdx fun j c => if (zf.lookup j).isSome then StringsEntail.mkWord [] else c)
  let (y', r) ← lenRwFact yc
  return (y', ← push ⟨.trans, [], [c, r], .step⟩)

/-- `STR_EQ_CONJ_LEN_ENTAIL` on the equality `n`, with the concatenation as
`node[1-i]`, certified (see the module docstring). -/
def strEqLenUnifyPrefixAt (n : Node) (i : Nat) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  let (x, y) := if i == 0 then (a, b) else (b, a)
  if y.getKind != .STRING_CONCAT then none
  let cs := y.getChildren.toList
  let empty := StringsEntail.mkWord []
  let (keep, zeros) ← if x == empty then some ([], List.range cs.length) else inferZeros x cs
  if zeros.isEmpty then none
  let kept := StringsEntail.mkConcat (keep.map fun p => cs[p]!)
  let mainEq := if i == 0 then eqNode x kept else eqNode kept x
  let conjs := mainEq :: zeros.map fun p => eqNode cs[p]! empty
  let m := mkNode .AND conjs.toArray
  let act : EmitM Unit := do
    -- forward: under `n`, the conjunction
    let h ← push ⟨.refl, [.node n], [], .assume⟩
    let xy ← if i == 0 then pure h else push ⟨.symm, [], [h], .step⟩
    let lxy ← congStep (lenNode x) (.kind .STRING_LENGTH) [xy]
    let mut zf : List (Nat × Nat) := []
    for k in zeros do
      let yk := cs[k]!
      let sk := lenSum ((List.range cs.length).filter (· != k) |>.map fun p => lenNode cs[p]!)
      let g := mkNode .GEQ #[sk, lenNode x]
      let some gr := ArithEntail.proveGeq g | throw "a length entailment without a proof"
      if gr.1 != mkTrue then throw "a length entailment that is not true"
      let some gcs := Proof.cmdsOf gr | throw "a length entailment without CPC steps"
      let gt ← emitCmds (gcs.foldr Eo.CCmdList.cons .nil)
      let gf ← push ⟨.true_elim, [], [gt], .step⟩
      let rsk ← push ⟨.refl, [.node sk], [], .step⟩
      let gg ← congStep g (.kind .GEQ) [rsk, lxy]
      let g' ← push ⟨.eq_resolve, [], [gf, gg], .step⟩
      let (r, rr) ← lenRwFact (mkNode .GEQ #[sk, lenNode y])
      let nr ← push ⟨.eq_resolve, [], [g', rr], .step⟩
      let pos := mkNode .GT #[lenNode yk, .const (.integer 0)]
      let (ar, pa) ← lenRwFact pos
      if r != notNode ar then throw "a length entailment that does not isolate the component"
      -- (not pos), from (not ar)
      let cn ← congStep (notNode pos) (.kind .NOT) [pa]
      let cn' ← push ⟨.symm, [], [cn], .step⟩
      let npos ← push ⟨.eq_resolve, [], [nr, cn'], .step⟩
      let slp ← push ⟨.string_length_pos, [.node yk], [], .step⟩
      let c ← push ⟨.resolution, [.term (Eo.Term.Boolean true), .node pos], [slp, npos], .step⟩
      let ze ← push ⟨.and_elim, [.term (Eo.Term.Numeral 1)], [c], .step⟩
      zf := zf ++ [(k, ze)]
    let (y', yy) ← lenEmptyComponents y zf
    if y' != kept then throw "the concatenation of the other components is another term"
    let main ← push ⟨.trans, [], [xy, yy], .step⟩
    let main ← if i == 0 then pure main else push ⟨.symm, [], [main], .step⟩
    let conj ← push ⟨.and_intro, [], main :: zf.map (·.2), .step⟩
    let impl₁ ← push ⟨.scope, [], [conj], .pop⟩
    -- backward: under the conjunction, `n`
    let h₂ ← push ⟨.refl, [.node m], [], .assume⟩
    let mf ← push ⟨.and_elim, [.term (Eo.Term.Numeral 0)], [h₂], .step⟩
    let mut zf₂ : List (Nat × Nat) := []
    for (k, j) in zeros.zipIdx do
      zf₂ := zf₂ ++ [(k, ← push ⟨.and_elim, [.term (Eo.Term.Numeral (j + 1))], [h₂], .step⟩)]
    let (_, yy₂) ← lenEmptyComponents y zf₂
    let xk ← if i == 0 then pure mf else push ⟨.symm, [], [mf], .step⟩
    let yy₂' ← push ⟨.symm, [], [yy₂], .step⟩
    let xy₂ ← push ⟨.trans, [], [xk, yy₂'], .step⟩
    let n' ← if i == 0 then pure xy₂ else push ⟨.symm, [], [xy₂], .step⟩
    let impl₂ ← push ⟨.scope, [], [n'], .pop⟩
    -- `(= n m)`
    let both ← push ⟨.and_intro, [], [impl₁, impl₂], .step⟩
    let d := mkNode .AND #[mkNode .IMPLIES #[n, m], mkNode .IMPLIES #[m, n]]
    let some dr := byRule "bool-dual-impl-eq" d | throw "no bool-dual-impl-eq"
    let de ← closeChain d (← emitChain dr.2)
    let _ ← push ⟨.eq_resolve, [], [both, de], .step⟩
  match act.run {} with
  | .ok ((), st) => applyCmds ((toCmds st.steps).foldr Eo.CCmdList.cons .nil) n
  | .error _ => none

/-- `rewriteViaStrEqLenUnifyPrefix`: the concatenation on the right, then on
the left. -/
def strEqLenUnifyPrefix (n : Node) : Option (Rw n) :=
  (strEqLenUnifyPrefixAt n 0).orElse fun _ => strEqLenUnifyPrefixAt n 1

/-- The split of `rewriteViaStrEqLenUnify`: the first prefixes, by the number
of components, `(i, j)` whose lengths are entailed equal, in cvc5's order of
search; `none` if there is none, or if cvc5 would first strip a prefix by the
length of the other (`SPLIT_EQ_STRIP_R`, `SPLIT_EQ_STRIP_L`, not ported). -/
def lenUnifySplit (v₀ v₁ : List Node) : Option (Nat × Nat) := Id.run do
  let mut startRhs := 0
  for i in [0:v₀.length + 1] do
    let pfx₀ := v₀.take i
    let len₀ := lenNode (StringsEntail.mkConcat pfx₀)
    for j in [startRhs:v₁.length + 1] do
      if (i == 0 && j == 0) || (i == v₀.length && j == v₁.length) then continue
      let pfx₁ := v₁.take j
      let len₁ := lenNode (StringsEntail.mkConcat pfx₁)
      if ArithEntail.checkEq len₀ len₁ then return some (i, j)
      else if ArithEntail.check2 len₁ len₀ true then
        if let some (_, _, c) := stripSymbolicLength pfx₁ true len₀ then
          if c == ArithEntail.zero then return none
        break
      else if ArithEntail.check2 len₀ len₁ true then
        if let some (_, _, c) := stripSymbolicLength pfx₀ true len₁ then
          if c == ArithEntail.zero then return none
        startRhs := j + 1
  return none

/-- `rewriteViaStrEqLenUnify` (`SPLIT_EQ`): `(= (str.++ x₁ … xₙ) (str.++ y₁ … yₘ))`
is `(and (= P₀ P₁) (= S₀ S₁))` for the prefixes `P₀ = x₁ … xᵢ`, `P₁ = y₁ … yⱼ`
of lengths entailed equal and the suffixes `S₀`, `S₁`: a semantic step
(`SemProc.strSplit`, `Telos/Core/StrSplit.lean`), whose side condition asks
for the lengths' equality for a reason read off the components
(`StrSplit.lenEq`); a split that cvc5 finds by more arithmetic is not taken.
(Only the splits with non-empty prefixes and suffixes.) -/
def strEqLenUnify (n : Node) : Option (Rw n) := do
  let #[a, b] := n.getChildren | none
  if a.getKind != .STRING_CONCAT || b.getKind != .STRING_CONCAT then none
  let v₀ := a.getChildren.toList
  let v₁ := b.getChildren.toList
  let (i, j) ← lenUnifySplit v₀ v₁
  let m := StrSplit.target v₀ v₁ i j
  if h : SemProc.check (.strSplit i j) n m = true then
    some ⟨m, .semantic (.strSplit i j) (SemProc.check_ok h) (.refl m)⟩
  else none

/-- The CPC proof of `(= n m)` for a `SemProc.strSplit` step, as cvc5
elaborates `MACRO_STR_EQ_LEN_UNIFY`: each side regrouped as `(str.++ P S)`
(`aci_norm`); then, under the regrouped equality, `concat_unify` with the
length equality (`ArithEntail.proveEq`) gives `(= P₀ P₁)`, and `concat_eq` the
suffixes; under the conjunction, congruence gives it back;
`bool-dual-impl-eq`. -/
def strSplitE (i j : Nat) (n m : Node) : EmitM Nat := do
  let #[a, b] := n.getChildren | throw "strSplit: not an equality"
  let v₀ := a.getChildren.toList
  let v₁ := b.getChildren.toList
  let p₀ := StrSplit.cat (v₀.take i)
  let s₀ := StrSplit.cat (v₀.drop i)
  let p₁ := StrSplit.cat (v₁.take j)
  let s₁ := StrSplit.cat (v₁.drop j)
  let g₀ := mkNode .STRING_CONCAT #[p₀, s₀]
  let g₁ := mkNode .STRING_CONCAT #[p₁, s₁]
  let ceq := eqNode g₀ g₁
  if m != mkNode .AND #[eqNode p₀ p₁, eqNode s₀ s₁] then throw "strSplit: another conjunction"
  -- the regrouping, `(= n ceq)`
  let ra ← if a == g₀ then push ⟨.refl, [.node a], [], .step⟩
    else push ⟨.aci_norm, [.node (eqNode a g₀)], [], .step⟩
  let rb ← if b == g₁ then push ⟨.refl, [.node b], [], .step⟩
    else push ⟨.aci_norm, [.node (eqNode b g₁)], [], .step⟩
  let rg ← congStep n (.kind .EQUAL) [ra, rb]
  let leq := eqNode (lenNode p₀) (lenNode p₁)
  -- forward: under `ceq`, the conjunction
  let h ← push ⟨.refl, [.node ceq], [], .assume⟩
  let some lr := ArithEntail.proveEq leq | throw "a length equality without a proof"
  if lr.1 != mkTrue then throw "a length equality that is not true"
  let some lcs := Proof.cmdsOf lr | throw "a length equality without CPC steps"
  let lt ← emitCmds (lcs.foldr Eo.CCmdList.cons .nil)
  let lf ← push ⟨.true_elim, [], [lt], .step⟩
  let u ← push ⟨.concat_unify, [.node mkFalse], [h, lf], .step⟩
  let us ← push ⟨.symm, [], [u], .step⟩
  let rs ← push ⟨.refl, [.node s₀], [], .step⟩
  let e ← congStep (mkNode .STRING_CONCAT #[p₁, s₀]) (.kind .STRING_CONCAT) [us, rs]
  let e₂ ← push ⟨.trans, [], [e, h], .step⟩
  let sfx ← push ⟨.concat_eq, [.node mkFalse], [e₂], .step⟩
  let conj ← push ⟨.and_intro, [], [u, sfx], .step⟩
  let impl₁ ← push ⟨.scope, [], [conj], .pop⟩
  -- backward: under the conjunction, `ceq`
  let h₂ ← push ⟨.refl, [.node m], [], .assume⟩
  let e₀ ← push ⟨.and_elim, [.term (Eo.Term.Numeral 0)], [h₂], .step⟩
  let e₁ ← push ⟨.and_elim, [.term (Eo.Term.Numeral 1)], [h₂], .step⟩
  let c ← congStep g₀ (.kind .STRING_CONCAT) [e₀, e₁]
  let impl₂ ← push ⟨.scope, [], [c], .pop⟩
  let both ← push ⟨.and_intro, [], [impl₁, impl₂], .step⟩
  let d := mkNode .AND #[mkNode .IMPLIES #[ceq, m], mkNode .IMPLIES #[m, ceq]]
  let some dr := byRule "bool-dual-impl-eq" d | throw "no bool-dual-impl-eq"
  let de ← closeChain d (← emitChain dr.2)
  let cm ← push ⟨.eq_resolve, [], [both, de], .step⟩
  push ⟨.trans, [], [rg, cm], .step⟩

end Telos.Preprocess
