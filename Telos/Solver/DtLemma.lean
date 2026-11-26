import Telos.Solver.EqProofCpc
import Telos.Solver.Theory.DtType

/-!
# Certificates of the datatypes lemmas

A lemma of the theory of datatypes is valid. `prove id lem` gives an
`EqProof` of `(lem, true)` from no assumptions, by its CPC rule, for the lemmas
the theory sends (`TheoryDatatypes`'s inferences that are lemmas):
- `DATATYPES_SPLIT`, `(or (is-C₁ x) … (is-Cₙ x))`: `dt_split`;
- `DATATYPES_PURIFY`, `(= k t)` for `k` the purification skolem of `t`:
  `skolem_intro`;
- `DATATYPES_INST` of a constructor term `t = (C a₁ … aₙ)`, `(= t (C (s₁ k)
  … (sₙ k)))` for `k` the purification skolem of `t`: `skolem_intro`, then for
  each argument congruence and `dt-collapse-selector` (`(sᵢ k) = (sᵢ t) = aᵢ`),
  then congruence;
- `DATATYPES_INST` from a tester, `(=> (is-C x) (= x (C (s₁ x) …)))`: under the
  assumption of the tester, `dt-inst`, then `scope`;
- `DATATYPES_COLLAPSE_SEL` (a lemma when the selector's type is not a
  datatype), `(=> (= a c) (= (s a) r))` for a constructor term `c`: under the
  assumption, congruence and `dt-collapse-selector`, then `scope`.

The implications are CPC proofs with an assumption, closed by `scope`: the
proof under the assumption is an `EqProof` from it, printed as CPC
(`emitEq`), which `EqProof.valid` then checks with Logos's checker.

The lemma the SAT solver gets is rewritten (cvc5's `TheoryPreprocessor`), and
oriented as cvc5's node ids would: `forFormula` relates the two by `rw`, when
they have the same rewrite. The clauses of the formula are then justified by
`SatProof.Just.lemma`.
-/

open Eo

namespace Telos.Solver.DtLemma

open Proof

/-- A proof of `(= (sⱼ t) aⱼ)`, for `sⱼ` the selector of the argument `j` of the
constructor term `t = (C a₁ … aₙ)`. -/
def collapse (T : TypeNode) (i j : Nat) (t a : Node) : EqProof :=
  let lem := Node.eqNode (DT.mkSel T i j t) a
  .valid lem [DT.ruleStep .dt_collapse_selector lem]

/-- The CPC proof of `(=> h F)`, from a proof `q` of what `F` gives as an
assumption (`EqProof.assumptionEq F`) under the assumption `h`: the assumption,
the steps of `q`, then `scope`. -/
def underScope (h F : Node) (q : EqProof) : Option (List CCmd) :=
  if EqProof.check #[h] q != some (EqProof.assumptionEq F) then none else
  let act : EmitM Unit := do
    let p ← push ⟨.refl, [.node h], [], .assume⟩
    let c ← emitEq #[h] #[p] q
    -- the fact `F`, from `(= F true)` unless `F` is an equality
    let c ← match F with
      | .app (.kind .EQUAL) #[_, _] => pure c
      | _ => push ⟨.true_elim, [], [c], .step⟩
    let _ ← push ⟨.scope, [], [c], .pop⟩
  match act.run {} with
  | .ok ((), st) => some (toCmds st.steps)
  | .error _ => none

/-- An implication `(=> h F)` proven by `q` under `h`. -/
def implies (h F : Node) (q : EqProof) : Option EqProof := do
  let cs ← underScope h F q
  some (.valid (.app (.kind .IMPLIES) #[h, F]) cs)

/-! ## Relating formulas -/

/-- `t` with its arithmetic equalities in normal form
(`Arith.normalizeEquality`: the rewriter only orients them), below Boolean
connectives, and a proof of `(t, t')` if it differs. -/
partial def normEqualities (t : Node) : Node × Option EqProof :=
  match t with
  | .app (.kind .EQUAL) #[_, _] =>
    match Arith.normalizeEquality t with
    | some r => match Proof.cmdsOf r with
      | some cs => (r.1, some (.valid (Node.eqNode t r.1) cs))
      | none => (t, none)
    | none => below t
  | .app (.kind .NOT) _ | .app (.kind .AND) _ | .app (.kind .OR) _ | .app (.kind .IMPLIES) _
  | .app (.kind .ITE) _ => below t
  | _ => (t, none)
where
  below (t : Node) : Node × Option EqProof :=
    match t with
    | .app op cs =>
      let rs := cs.map normEqualities
      if rs.all (·.2.isNone) then (t, none)
      else (.app op (rs.map (·.1)), some (.congAt t (rs.map (·.2))))
    | t => (t, none)

/-- `t` rewritten, with its arithmetic equalities in normal form, and a proof of
`(t, t')`. -/
def normalForm (t : Node) : Node × EqProof :=
  let r := Telos.rewrite t
  match normEqualities r with
  | (_, none) => (r, .rw t)
  | (r', some p) => (Telos.rewrite r', .trans (.rw t) (.trans p (.rw r')))

/-- A proof of `(a, b)`, for formulas with the same rewrite or normal form. -/
def sameForm (a b : Node) : Option EqProof :=
  if Telos.rewrite a == Telos.rewrite b then some (.trans (.rw a) (.symm (.rw b))) else
  let (a', pa) := normalForm a
  let (b', pb) := normalForm b
  if a' == b' then some (.trans pa (.symm pb)) else none

/-- A proof of `(a, b)`, for an equality of integers `a` and its copy between
reals `b` (or conversely): by `arith_poly_norm_rel`. -/
def sameCast (a b : Node) : Option EqProof := do
  let .app (.kind .EQUAL) #[a₁, a₂] := a | none
  let .app (.kind .EQUAL) #[b₁, b₂] := b | none
  let x := Arith.toReal (Node.mkNode .SUB #[a₁, a₂])
  let y := Arith.toReal (Node.mkNode .SUB #[b₁, b₂])
  let r ← Arith.polyNormRel a 1 1 x y b
  some (.valid (Node.eqNode a b) (← Proof.cmdsOf r))

/-- A proof of `(t, true)`, for `t` with normal form `true` or a disjunction of
two complementary literals. -/
def byNormalForm (t : Node) : Option EqProof :=
  let (t', p) := normalForm t
  if t' == Node.mkTrue then some p else
  match t' with
  | .app (.kind .OR) #[l, r] =>
    let taut (x : Node) : Option EqProof :=
      let act : EmitM Unit := do
        let s ← push ⟨.split, [.node x], [], .step⟩
        if t' != Node.orNode x (Node.notNode x) then
          let _ ← push ⟨.reordering, [.node t'], [s], .step⟩
      match act.run {} with
      | .ok ((), st) => some (.trans p (.valid t' (toCmds st.steps)))
      | .error _ => none
    if r == Node.notNode l then taut l else if l == Node.notNode r then taut r else none
  | _ => none

/-- **A proof of `(lem, true)`** from no assumptions, for the lemma `lem` sent
with the identifier `id`. -/
def prove (id : String) (lem : Node) : Option EqProof := do
  match id, lem with
  | "DATATYPES_SPLIT", .app (.kind .OR) ls =>
    let (_, x) ← DT.isTester? (← ls[0]?)
    some (.valid lem [DT.argStep .dt_split x])
  | "DATATYPES_PURIFY", .app (.kind .EQUAL) #[k, t] =>
    if k != Node.mkPurifySkolem t then none
    some (.eqTrue (.valid lem [DT.argStep .skolem_intro k]))
  | "DATATYPES_INST", .app (.kind .EQUAL) #[t, r] =>
    -- a tuple and the tuple of its fields: `dt_inst`, with no tester
    if let some T := DT.dtType? t then
      if DT.isTupleType T && (DT.consApp? t).isNone then
        if r != DT.getInstCons t T 0 then none
        let eq := Node.eqNode Node.mkTrue lem
        return .symm (.valid eq [DT.ruleStep .dt_inst eq])
    -- `t` is a constructor term, `r` its instantiation with its skolem
    let (T, i, as) ← DT.consApp? t
    let (T', i', ss) ← DT.consApp? r
    if T != T' || i != i' || as.size != ss.size || as.size == 0 then none
    let k := Node.mkPurifySkolem t
    let pk : EqProof := .valid (Node.eqNode k t) [DT.argStep .skolem_intro k]
    let mut args : Array (Option EqProof) := #[]
    for j in [0:as.size] do
      let s := ss[j]!
      -- (an internal fact may have the selectors of the term itself)
      if s == DT.mkSel T i j t then
        args := args.push (some (collapse T i j t as[j]!))
        continue
      if s == as[j]! then
        args := args.push none
        continue
      if s != DT.mkSel T i j k then none
      -- `(sⱼ k) = (sⱼ t) = aⱼ`
      args := args.push (some (.trans (.congAt s #[some pk]) (collapse T i j t as[j]!)))
    some (.eqTrue (.symm (.congAt r args)))
  | "DATATYPES_INST", .app (.kind .IMPLIES) #[h, conc] =>
    -- `(= h conc)` by `dt-inst`, and `h`
    let eq := Node.eqNode h conc
    let v : EqProof := .valid eq [DT.ruleStep .dt_inst eq]
    implies h conc (.fromTrue (.trans (.symm v) (.assume 0)))
  | "DATATYPES_COLLAPSE_SEL", .app (.kind .IMPLIES) #[h@(.app (.kind .EQUAL) #[_, c]), conc@(.app (.kind .EQUAL) #[s, r])] =>
    let (T, i, j, _) ← DT.selApp? s
    let (_, ci, cs) ← DT.consApp? c
    if ci != i || cs[j]? != some r then none
    implies h conc (.trans (.congAt s #[some (.assume 0)]) (collapse T i j c r))
  | _, _ => none

/-- A proof of `(F, true)` for the formula `F` given to the SAT solver for the
lemma `lem`, from `p : (lem, true)`: `F` is `lem` rewritten (and oriented), so
the two have the same rewrite. -/
def forFormula (lem F : Node) (p : EqProof) (checked : Bool := false) : Option EqProof :=
  -- (`p`, when its producer has checked it; the certificate is checked again)
  if checked && F == lem then some p else
  let q := if F == lem then p else .trans (.rw F) (.trans (.symm (.rw lem)) p)
  if EqProof.check #[] q == some (F, Node.mkTrue) then some q else none

end Telos.Solver.DtLemma
