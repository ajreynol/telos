import Telos.Core.Proof.Emit
import Telos.Preprocess.SkolemSteps

/-!
# Proofs about the pipeline's conjunction

Combinators for one CPC proof that two conjunctions are equal, as non-clausal
simplification needs: each direction assumes one side (`assume_push`), takes
out its conjuncts (`and_elim`), derives the facts it needs, and rebuilds the
other side (`and_intro`), under `scope`; the two implications give the
equality by resolution (`equivOf`). The facts are positions in the proof
(`Proof.EmitM`).

The derived facts are, mostly, equalities `(= a b)` for an assertion `a` and
its simplified form `b`: substitutions (`substFact`, congruence whose leaves
are the facts `(= x t)` of the substitution), and certified rewrites embedded
as they are (`rwFact`). `eq_resolve` turns a fact `a` and `(= a b)` into `b`.

The proof is run by Logos's checker (`applyCmds`), so nothing here needs a
proof.
-/

namespace Telos.Preprocess

open Eo Node Proof

/-- Push a step. -/
def stepE (r : CRule) (args : List Term) (prems : List Nat) : EmitM Nat :=
  push ⟨r, args.map .term, prems, .step⟩

/-- Push a step whose arguments may be nodes (`PArg`). -/
def stepN (r : CRule) (args : List PArg) (prems : List Nat) : EmitM Nat :=
  push ⟨r, args, prems, .step⟩

/-- `assume_push t`. -/
def assumeE (t : Node) : EmitM Nat := push ⟨.refl, [.node t], [], .assume⟩

/-- `scope` over the fact at `p`: `(=> A p)` for the last assumption `A`. -/
def scopeE (p : Nat) : EmitM Nat := push ⟨.scope, [], [p], .pop⟩

/-- The conjuncts of the fact `n` at `pos`, by `and_elim`, with their positions
(the fact itself if it is not a conjunction). -/
def conjunctsE (pos : Nat) (n : Node) : EmitM (List (Node × Nat)) := do
  match n with
  | .app (.kind .AND) cs =>
    let mut out := []
    for h : i in [0:cs.size] do
      let p ← stepE .and_elim [.Numeral (Int.ofNat i)] [pos]
      out := out ++ [(cs[i], p)]
    return out
  | _ => return [(n, pos)]

/-- The fact `(= a b)` for a certified rewrite of `a` to `b` (its steps
embedded), or `none` when it does not change `a`. -/
def rwFact {a : Node} (r : Rw a) : EmitM (Option Nat) := do
  if r.1 == a then return none
  let ch ← emitChain r.2
  return some (← closeChain a ch)

/-- `(= a c)` from `(= a b)` and `(= b c)`, each optional (`none` for no
change). -/
def transOpt (p q : Option Nat) : EmitM (Option Nat) :=
  match p, q with
  | none, q => pure q
  | p, none => pure p
  | some p, some q => some <$> stepE .trans [] [p, q]

/-- A substitution, as facts: for a term `t`, the position of the fact
`(= t s)` and `s`. -/
abbrev SubstFacts := Node → Option (Nat × Node)

/-- `SubstitutionMap::apply` of the substitution `σ` to `n`, with its proof: the
result and the fact `(= n result)` (`none` if unchanged). A term of `σ` is
replaced by its value, which is substituted again (fixed point); otherwise the
children are, by congruence (`cong`, `nary_cong`), and a rebuilt term of `σ` is
replaced too. Skolems and variables are atomic; binders are entered through
their body. `fuel` bounds the depth. -/
partial def substFact (σ : SubstFacts) (fuel : Nat) (n : Node) : EmitM (Node × Option Nat) := do
  if fuel == 0 then return (n, none)
  if let some (p, s) := σ n then
    let (s', q) ← substFact σ (fuel - 1) s
    return (s', ← transOpt (some p) q)
  match n with
  | .app op cs =>
    let isBinder := op.getKind.isQuantifier
    let rs ← if isBinder then
        match cs[1]? with
        | some body => do
          let r ← substFact σ (fuel - 1) body
          pure (cs.toList.zipIdx.map fun (c, i) => if i == 1 then r else (c, none))
        | none => pure (cs.toList.map fun c => (c, none))
      else cs.toList.mapM (substFact σ (fuel - 1))
    if rs.all (·.2.isNone) then return (n, none)
    let n' : Node := .app op (rs.map (·.1)).toArray
    let eqs ← if isBinder then
        match rs[1]? with
        | some (_, some e) => pure [e]
        | _ => pure []
      else (rs.zip cs.toList).mapM fun ((_, e), c) =>
        match e with
        | some e => pure e
        | none => closeChain c #[]
    let p ← congStep n op eqs
    -- a rebuilt term of `σ`
    if let some (q, s) := σ n' then
      let (s', r) ← substFact σ (fuel - 1) s
      return (s', ← transOpt (← transOpt (some p) (some q)) r)
    return (n', some p)
  | _ => return (n, none)

/-- `eq_resolve`: the fact `b` from the fact `a` (at `pa`) and `(= a b)`. -/
def eqResolveE (pa : Nat) (pe : Option Nat) : EmitM Nat :=
  match pe with
  | none => pure pa
  | some pe => stepE .eq_resolve [] [pa, pe]

/-- `symm` of an optional equality. -/
def symmOpt (p : Option Nat) : EmitM (Option Nat) :=
  match p with
  | none => pure none
  | some p => some <$> stepE .symm [] [p]

/-- The fact `true`: `refl`, then `true_elim`. -/
def trueE : EmitM Nat := do
  let p ← stepE .refl [mkTrue.toEo] []
  stepE .true_elim [] [p]

/-- The conjunction of the facts at `ps` (`and_intro`); a single fact is
itself. -/
def andIntroE (ps : List Nat) : EmitM Nat :=
  match ps with
  | [p] => pure p
  | ps => stepE .and_intro [] ps

/-- `(= a b)` from the facts `(=> a b)` at `i₁` and `(=> b a)` at `i₂`: as in
`andReorg`, `implies_elim`, `cnf_equiv_neg1/2` and resolution. -/
def equivOfE (ta tb : Term) (i₁ i₂ : Nat) : EmitM Nat := do
  let c₄ ← stepE .implies_elim [] [i₁]
  let c₂ ← stepE .implies_elim [] [i₂]
  let e := eoApp2 UserOp.eq ta tb
  let c₁ ← stepE .cnf_equiv_neg2 [e] []
  let c₃ ← stepE .cnf_equiv_neg1 [e] []
  let r₁ ← stepE .resolution [.Boolean false, ta] [c₁, c₂]
  let f₁ ← stepE .factoring [] [r₁]
  let r₂ ← stepE .resolution [.Boolean true, ta] [c₃, c₄]
  let f₂ ← stepE .factoring [] [r₂]
  let r₃ ← stepE .resolution [.Boolean false, tb] [f₁, f₂]
  stepE .factoring [] [r₃]

/-- `equivOfE`, with the formulas as nodes. -/
def equivOfN (a b : Node) (i₁ i₂ : Nat) : EmitM Nat := do
  let c₄ ← stepE .implies_elim [] [i₁]
  let c₂ ← stepE .implies_elim [] [i₂]
  let e := eqNode a b
  let c₁ ← stepN .cnf_equiv_neg2 [.node e] []
  let c₃ ← stepN .cnf_equiv_neg1 [.node e] []
  let r₁ ← stepN .resolution [.term (.Boolean false), .node a] [c₁, c₂]
  let f₁ ← stepE .factoring [] [r₁]
  let r₂ ← stepN .resolution [.term (.Boolean true), .node a] [c₃, c₄]
  let f₂ ← stepE .factoring [] [r₂]
  let r₃ ← stepN .resolution [.term (.Boolean false), .node b] [f₁, f₂]
  stepE .factoring [] [r₃]

/-- `(= a false)` from the fact `(=> a false)` at `i`: `implies_elim` gives the
clause `(or (not a) false)`, from which resolution with `(not false)` (by
`refl` and `false_elim`) leaves `(not a)`, then `false_intro`. -/
def falseOfE (i : Nat) : EmitM Nat := do
  let c ← stepE .implies_elim [] [i]
  let r ← stepE .refl [mkFalse.toEo] []
  let nf ← stepE .false_elim [] [r]
  let na ← stepE .resolution [.Boolean true, mkFalse.toEo] [c, nf]
  stepE .false_intro [] [na]

/-- Run a proof whose last fact is `(= n m)`, as a certified rewrite of `n`. -/
def runE (n : Node) (prf : EmitM Nat) : Option (Rw n) :=
  match prf.run {} with
  | .ok (_, st) => applyCmds (cmdList (toCmds st.steps)) n
  | .error _ => none

end Telos.Preprocess
