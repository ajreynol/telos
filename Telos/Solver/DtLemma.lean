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
    -- `t` is a constructor term, `r` its instantiation with its skolem
    let (T, i, as) ← DT.consApp? t
    let (T', i', ss) ← DT.consApp? r
    if T != T' || i != i' || as.size != ss.size || as.size == 0 then none
    let k := Node.mkPurifySkolem t
    let pk : EqProof := .valid (Node.eqNode k t) [DT.argStep .skolem_intro k]
    let mut args : Array (Option EqProof) := #[]
    for j in [0:as.size] do
      let s := ss[j]!
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
def forFormula (lem F : Node) (p : EqProof) : Option EqProof :=
  let q := if F == lem then p else .trans (.rw F) (.trans (.symm (.rw lem)) p)
  if EqProof.check #[] q == some (F, Node.mkTrue) then some q else none

end Telos.Solver.DtLemma
