import Telos.Core.Proof.Emit
import Telos.Core.Proof.Eunoia
import Telos.Solver.EqProof

/-!
# CPC proofs of conflicts

The CPC refutation of a checked conflict (`EqProof.checkConflict A p`): the
assumptions `A`, then the steps of `p`, then `false`. A conclusion `(a, b)` of
the certificate is the CPC fact `(= a b)`:
- `assume i`: the assumption itself for `(= a b)`, by `false_intro` for
  `(not x)` (giving `(= x false)`), by `true_intro` otherwise (`(= l true)`);
- `symm`, `trans`: the CPC rules of the same names;
- `cong`: `cong` (or `nary_cong`) on the application, with `refl` for the
  arguments without a proof (`Proof.congStep`);
- `eqTrue`: `true_intro` on `(= a b)`;
- `valid F cs`: the steps of `cs` (which prove `F`), then as `assume`;
- `fromTrue`: `true_elim`, then as `assume`;
- `andElim i`: `true_elim`, `and_elim i`, `true_intro`;
- `orElim k`: `true_elim`, then `resolution` with each `(not lᵢ)` (from
  `false_elim`), and `true_intro`;
- `congAt t`: as `cong`.
The last fact is `(= true false)`, and `false` follows by `symm` and
`true_elim`. The last step states its conclusion, `false`, so that a checker
that accepts the proof has checked a refutation.

The proof is printed with its terms as trees, which is fine for the
explanations of conflicts. telos does not check it: Ethos does
(`scripts/fuzz-solve.py --proofs`).
-/

open Eo

namespace Telos.Solver

open Proof

/-- The fact `(= a b)` for what the literal `l` at position `p` gives as an
assumption. -/
def asEq (l : Node) (p : Nat) : EmitM Nat := do
  let rule : Option CRule := match l with
    | .app (.kind .EQUAL) cs => if cs.size = 2 then none else some .true_intro
    | .app (.kind .NOT) cs => if cs.size = 1 then some .false_intro else some .true_intro
    | _ => some .true_intro
  match rule with
  | none => return p
  | some r => push ⟨r, [], [p], .step⟩

/-- The steps of the CPC commands `cs` (steps without premises). -/
def emitCmds : List CCmd → EmitM Nat
  | [] => throw "an empty proof"
  | [.step r as _] => push ⟨r, argList as, [], .step⟩
  | .step r as _ :: rest => do let _ ← push ⟨r, argList as, [], .step⟩; emitCmds rest
  | _ => throw "a proof that is not of steps"
where
  argList : CArgList → List PArg
    | .nil => []
    | .cons a rest => .term a :: argList rest

/-- The steps of a certificate's facts, given the positions of the assumptions. -/
partial def emitEq (A : Array Node) (pos : Array Nat) : EqProof → EmitM Nat
  | .assume i => do
    let some l := A[i]? | throw "an assumption out of range"
    let some p := pos[i]? | throw "an assumption out of range"
    let rule : Option CRule := match l with
      | .app (.kind .EQUAL) cs => if cs.size = 2 then none else some .true_intro
      | .app (.kind .NOT) cs => if cs.size = 1 then some .false_intro else some .true_intro
      | _ => some .true_intro
    match rule with
    | none => return p
    | some r => push ⟨r, [], [p], .step⟩
  | .symm p => do let q ← emitEq A pos p; push ⟨.symm, [], [q], .step⟩
  | .trans p q => do
    let a ← emitEq A pos p
    let b ← emitEq A pos q
    push ⟨.trans, [], [a, b], .step⟩
  | .cong src args => do
    let some root := A[src.root]? | throw "a path out of range"
    let some t := EqProof.follow root src.path | throw "a path that leads nowhere"
    let .app op cs := t | throw "a congruence on a non-application"
    let eqs ← emitArgs A pos cs args.toList 0
    congStep t op eqs
  | .eqTrue p => do let q ← emitEq A pos p; push ⟨.true_intro, [], [q], .step⟩
  | .valid F cs => do let q ← emitCmds cs; asEq F q
  | .fromTrue p => do
    let some (F, _) := EqProof.check A p | throw "a step that does not check"
    let q ← emitEq A pos p
    match F with
    | .app (.kind .EQUAL) _ | .app (.kind .NOT) _ =>
      asEq F (← push ⟨.true_elim, [], [q], .step⟩)
    | _ => return q
  | .andElim i p => do
    let q ← emitEq A pos p
    let f ← push ⟨.true_elim, [], [q], .step⟩
    let l ← push ⟨.and_elim, [.term (Term.Numeral i)], [f], .step⟩
    push ⟨.true_intro, [], [l], .step⟩
  | .orElim k p qs => do
    let some (.app (.kind .OR) ls, _) := EqProof.check A p | throw "a step that does not check"
    let q ← emitEq A pos p
    let mut c ← push ⟨.true_elim, [], [q], .step⟩
    let others := (List.range ls.size).filter (· != k)
    for (i, qi) in others.zip qs do
      let e ← emitEq A pos qi
      let n ← push ⟨.false_elim, [], [e], .step⟩
      c ← push ⟨.resolution, [.term (Term.Boolean true), .node ls[i]!], [c, n], .step⟩
    push ⟨.true_intro, [], [c], .step⟩
  | .congAt t args => do
    let .app op cs := t | throw "a congruence on a non-application"
    let eqs ← emitArgs A pos cs args.toList 0
    congStep t op eqs
where
  emitArgs (A : Array Node) (pos : Array Nat) (cs : Array Node) :
      List (Option EqProof) → Nat → EmitM (List Nat)
    | [], _ => pure []
    | none :: rest, i => do
      let c := cs[i]!
      let p ← push ⟨.refl, [.node c], [], .step⟩
      return p :: (← emitArgs A pos cs rest (i + 1))
    | some q :: rest, i => do
      let p ← emitEq A pos q
      return p :: (← emitArgs A pos cs rest (i + 1))

/-- The steps of the refutation of `A` by `p`: the assumptions (as steps of
kind `assume`), the facts, and `false`. -/
def refutationSteps (A : Array Node) (p : EqProof) : Except String (Array Step) := do
  let act : EmitM Unit := do
    let mut pos := #[]
    for l in A do
      pos := pos.push (← push ⟨.refl, [.node l], [], .assume⟩)
    let c ← emitEq A pos p
    let s ← push ⟨.symm, [], [c], .step⟩
    let _ ← push ⟨.true_elim, [], [s], .step⟩
  let ((), st) ← act.run {}
  return st.steps

/-- The refutation of `A` by `p` as a Eunoia proof, in parentheses as cvc5's
`get-proof` prints one, after the declarations `decls`. -/
def renderRefutation (N : Eunoia.Names) (decls : List String) (A : Array Node) (p : EqProof) :
    Except String String := do
  let steps ← refutationSteps A p
  let name (i : Nat) := s!"@p{i}"
  let lines := steps.toList.zipIdx.map fun (st, i) =>
    let args := st.args.map fun a => Eunoia.print N a.toEo
    match st.kind with
    | .assume => s!"(assume {name i} {args.headD "true"})"
    | _ =>
      let prems := if st.premises.isEmpty then ""
        else s!" :premises ({" ".intercalate (st.premises.map name)})"
      let argStr := if args.isEmpty then "" else s!" :args ({" ".intercalate args})"
      -- the last step states its conclusion, `false`, which Ethos checks
      let concl := if i + 1 == steps.size then " false" else ""
      s!"(step {name i}{concl} :rule {ruleName st.rule}{prems}{argStr})"
  return "(\n" ++ "\n".intercalate (decls ++ lines) ++ "\n)\n"

end Telos.Solver
