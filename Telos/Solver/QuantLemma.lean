import Telos.Solver.DtLemma
import Telos.Solver.Theory.QuantState

/-!
# Certificates of the quantifier lemmas

The lemmas of the quantifiers engine (`Telos/Solver/Theory/Quantifiers.lean`)
are valid. `prove l` gives an `EqProof` of `(l.lem, true)` from no assumptions:
- an instance `(=> q body)`, `body` the body of `q` with its variables replaced
  by the terms: under `q`, `instantiate` with the terms, then `scope`; then
  the rewrite of the lemma (`DtLemma.forFormula`);
- a skolemization `(=> (not q) (not body[k]))` for the skolems
  `(@quantifiers_skolemize q i)`: under `(not q)`, `skolemize`, then `scope`.

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
    return ← DtLemma.forFormula lem₀ l.lem p
  if l.skolemize.isSome then
    let .app (.kind .IMPLIES) #[h, c] := l.lem | none
    let p ← underAssumption h c .skolemize []
    return ← DtLemma.forFormula l.lem l.lem p
  none

end Telos.Solver.QuantLemma
