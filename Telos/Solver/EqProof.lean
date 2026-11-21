import Telos.Core.Tri
import Telos.Core.Node.DecEq
import Telos.Core.Certified
import Telos.Rewriter.Rewrite

/-!
# Equality proofs

A certificate for the equality engine's reasoning: a proof tree whose
conclusions are equations `(a, b)` between nodes, from assumptions that are
literals. It plays the role of cvc5's `eq::EqProof`, and is built from the
equality engine's graph after the fact (`Telos/Solver/EqualityEngine.lean`,
`EE.proveEq`).

`EqProof.check A p` computes the conclusion of `p` from the assumptions `A`, or
fails. It is a small function on nodes, linear in the proof: it never calls
Logos's checker. A conflict is a proof of `(true, false)`
(`EqProof.checkConflict`). If the assumptions are closed Boolean literals, a
conclusion `(a, b)` means that `(= a b)` is well typed and true in every
well-formed model of the assumptions, so a conflict means that the assumptions
are unsatisfiable (`verification/TelosProofs/Solver/EqProof.lean`).

The rules, with the conclusion each gives:
- `assume i`: the `i`-th assumption `l`: `(a, b)` if `l` is `(= a b)`,
  `(x, false)` if it is `(not x)`, and `(l, true)` otherwise;
- `symm p`: `(b, a)` from `p : (a, b)`;
- `trans p q`: `(a, c)` from `p : (a, b)` and `q : (b, c)`;
- `cong src args`: `(t, s)` for `t = (op c₁ … cₙ)` the node at the path `src`
  below an assumption, and `s = (op d₁ … dₙ)`, where `dᵢ = cᵢ` if the `i`-th
  argument proof is `none`, and `p : (cᵢ, dᵢ)` if it is `some p`. The path makes
  `t` a subterm of a well-typed assumption, through operators whose children are
  well typed when they are, so `t` is well typed. `op` must allow congruence
  (`AppShape.substCongruent`), and its children must be well typed when the
  application is (`Op.childrenTypedOfParent`), for the arguments without a
  proof;
- `eqTrue p`: `((= a b), true)` from `p : (a, b)`;
- `valid F cs`: what `F` gives as an assumption, for a formula `F` that the CPC
  proof `cs` proves, as Logos's checker finds when it runs `cs` from the empty
  state. `F` is then valid (Logos's `proven_from_empty_valid`), so this holds
  in every model: it brings theory reasoning, such as a datatypes rule
  (`dt-cons-eq`, `dt-inst`, ...), into the proof;
- `fromTrue p`: what `F` gives as an assumption, from `p : (F, true)`;
- `andElim i p`: `(lᵢ, true)` from `p : ((and l₁ … lₙ), true)`;
- `orElim k p qs`: `(lₖ, true)` from `p : ((or l₁ … lₙ), true)` and, in order,
  proofs `qs` of `(lᵢ, false)` for each `i ≠ k`;
- `congAt t args`: `cong` for the application `t` given as such, rather than by
  a path, when it is well typed (which is then checked);
- `rw t`: `(t, s)` for `s` the rewrite of `t` (`Telos.rewrite`), when `t` is
  well typed. The rewriter is verified (`rewrite_correct`), so this holds in
  every model. It relates a lemma, as a theory states it, to its rewritten form,
  which the SAT solver gets (`Telos/Solver/DtLemma.lean`).
-/

open Eo

namespace Telos.Solver

/-- A path to a subterm: an assumption, and child indices from it. -/
structure SubPath where
  root : Nat
  path : List Nat
  deriving Inhabited, Repr

inductive EqProof where
  | assume (i : Nat)
  | symm (p : EqProof)
  | trans (p q : EqProof)
  | cong (src : SubPath) (args : Array (Option EqProof))
  | eqTrue (p : EqProof)
  | valid (F : Node) (cs : List CCmd)
  | fromTrue (p : EqProof)
  | andElim (i : Nat) (p : EqProof)
  | orElim (k : Nat) (p : EqProof) (qs : List EqProof)
  | congAt (t : Node) (args : Array (Option EqProof))
  | rw (t : Node)
  deriving Inhabited

namespace EqProof

/-- What an assumption gives. -/
def assumptionEq (l : Node) : Node × Node :=
  match l with
  | .app (.kind .EQUAL) cs => if h : cs.size = 2 then (cs[0], cs[1]) else (l, Node.mkTrue)
  | .app (.kind .NOT) cs => if h : cs.size = 1 then (cs[0], Node.mkFalse) else (l, Node.mkTrue)
  | _ => (l, Node.mkTrue)

/-- The subterm at `path` below `t`, through operators whose children are well
typed when they are. -/
def follow : Node → List Nat → Option Node
  | t, [] => some t
  | .app op cs, i :: is =>
    if op.childrenTypedOfParent then
      match cs[i]? with
      | some c => follow c is
      | none => none
    else none
  | _, _ :: _ => none

/-- The conclusion of `p` from the assumptions `A`. -/
def check (A : Array Node) : EqProof → Option (Node × Node)
  | .assume i => A[i]?.map assumptionEq
  | .symm p => (check A p).map fun (a, b) => (b, a)
  | .trans p q => do
    let (a, b) ← check A p
    let (b', c) ← check A q
    if b == b' then some (a, c) else none
  | .cong src args => do
    let root ← A[src.root]?
    let t ← follow root src.path
    let .app op cs := t | none
    if !op.eoShape.substCongruent || !op.childrenTypedOfParent then none
    if args.size != cs.size then none
    let ds ← checkArgs A cs args.toList 0
    some (t, .app op ds.toArray)
  | .eqTrue p => (check A p).map fun (a, b) => (Node.eqNode a b, Node.mkTrue)
  | .valid F cs =>
    let cmds := cs.foldr CCmdList.cons CCmdList.nil
    if decide (CmdListTranslationOk cmds) && __eo_state_is_closed (runFromEmpty cmds) &&
        decide (__eo_state_proven_nth (runFromEmpty cmds) 0 = F.toEo) then
      some (assumptionEq F)
    else none
  | .fromTrue p => do
    let (F, t) ← check A p
    if t == Node.mkTrue then some (assumptionEq F) else none
  | .andElim i p => do
    let (F, t) ← check A p
    if t != Node.mkTrue then none
    let .app (.kind .AND) ls := F | none
    if ls.size < 2 then none
    let l ← ls[i]?
    some (l, Node.mkTrue)
  | .orElim k p qs => do
    let (F, t) ← check A p
    if t != Node.mkTrue then none
    let .app (.kind .OR) ls := F | none
    if ls.size < 2 then none
    let l ← ls[k]?
    if checkFalses A (ls.toList.eraseIdx k) qs then some (l, Node.mkTrue) else none
  | .congAt t args => do
    if !decide t.WellTyped then none
    let .app op cs := t | none
    if !op.eoShape.substCongruent || !op.childrenTypedOfParent then none
    if args.size != cs.size then none
    let ds ← checkArgs A cs args.toList 0
    some (t, .app op ds.toArray)
  | .rw t => if decide t.WellTyped then some (t, Telos.rewrite t) else none
where
  /-- Each proof proves its literal false. -/
  checkFalses (A : Array Node) : List Node → List EqProof → Bool
    | [], [] => true
    | l :: ls, q :: qs => check A q == some (l, Node.mkFalse) && checkFalses A ls qs
    | _, _ => false
  /-- The right-hand sides of the argument proofs, from argument `i` on. -/
  checkArgs (A : Array Node) (cs : Array Node) : List (Option EqProof) → Nat → Option (List Node)
    | [], _ => some []
    | none :: rest, i => do
      let c ← cs[i]?
      let ds ← checkArgs A cs rest (i + 1)
      some (c :: ds)
    | some p :: rest, i => do
      let c ← cs[i]?
      let (a, d) ← check A p
      if a != c then none
      let ds ← checkArgs A cs rest (i + 1)
      some (d :: ds)

/-- The assumptions are closed (for the stability of the condition that they
hold, under which congruence holds). -/
def closedAssumptions (A : Array Node) : Bool :=
  A.all fun l => __eo_is_closed l.toEo == Term.Boolean true

/-- `p` proves `true = false` from the closed assumptions `A`: they are
contradictory. -/
def checkConflict (A : Array Node) (p : EqProof) : Bool :=
  closedAssumptions A && check A p == some (Node.mkTrue, Node.mkFalse)

end EqProof

/-- The literal that makes `lit` false: its negation. -/
def negate (lit : Node) : Node :=
  match lit with
  | .app (.kind .NOT) cs => if h : cs.size = 1 then cs[0] else Node.notNode lit
  | _ => Node.notNode lit

end Telos.Solver
