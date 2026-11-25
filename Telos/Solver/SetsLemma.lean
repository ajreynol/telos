import Telos.Solver.DtLemma

/-!
# Certificates of the sets lemmas

A lemma of the theory of sets is valid. `prove id lem` gives an `EqProof` of
`(lem, true)` from no assumptions, for the lemmas the theory sends
(`Telos/Solver/Theory/Sets.lean`):
- `SETS_PROXY`, `(= k t)` for `k` the purification skolem of `t`:
  `skolem_intro`;
- `SETS_PROXY_SINGLETON`, `(set.member e k)` for `k` the purification skolem of
  `(set.singleton e)`: congruence with `skolem_intro`, `sets-member-singleton`,
  then the rewriter (`(= e e)` is `true`);
- `SETS_UP_CLOSURE` and `SETS_UP_CLOSURE_2`, `(=> exp (set.member x k))` for `k`
  the purification skolem of `(op a b)`: under `exp`, congruence with
  `skolem_intro`, the rule of membership in `op` (`sets-union-member`,
  `sets-inter-member`, `sets-minus-member`), then the memberships of `x` in `a`
  and `b` from the literals of `exp` (`atomProof`), and the rewriter;
- `SETS_DOWN_CLOSURE`, `(=> exp r)` for `r` the rewrite of `(set.member x s)`:
  under `exp`, the membership from the literals of `exp`, then the rewrite;
- `SETS_DEQ`, `(=> (not (= a b)) (not (= (set.member k a) (set.member k b))))`
  for `k` the skolem `(@sets_deq_diff a b)`: `sets_ext`, under the assumption;
- `SETS_CHOOSE_MEMBER`, `(or (= A empty) (set.member (set.choose A) A))`:
  `sets_choose_member`.

The proofs are checked when they are made (`EqProof.check`, and Logos's checker
for their CPC steps); a lemma without one is not certified, and a refutation
that needs it leaves the answer `unknown`.
-/

open Eo

namespace Telos.Solver.SetsLemma

open Proof

/-- `(= k t)` for the purification skolem `k` of `t`. -/
def purifyEq (k : Node) : Option EqProof :=
  match k with
  | .skolem .PURIFY #[t] => some (.valid (Node.eqNode k t) [DT.argStep .skolem_intro k])
  | _ => none

/-- `(= lhs rhs)` by one step of the rule `r` with the arguments `args`. -/
def ruleEq (r : CRule) (args : List Node) (lhs rhs : Node) : EqProof :=
  .valid (Node.eqNode lhs rhs) [.step r (toArgList (args.map Node.toEo)) .nil]

/-- The membership of `x` in `(op a b)`, by its rule: the equation. -/
def memberRule (x s : Node) : Option EqProof :=
  let mem := fun (y t : Node) => Node.mkNode .SET_MEMBER #[y, t]
  match s with
  | .app (.kind .SET_UNION) #[a, b] =>
    some (ruleEq .sets_union_member [x, a, b] (mem x s) (Node.mkNode .OR #[mem x a, mem x b]))
  | .app (.kind .SET_INTER) #[a, b] =>
    some (ruleEq .sets_inter_member [x, a, b] (mem x s) (Node.mkNode .AND #[mem x a, mem x b]))
  | .app (.kind .SET_MINUS) #[a, b] =>
    some (ruleEq .sets_minus_member [x, a, b] (mem x s)
      (Node.mkNode .AND #[mem x a, Node.notNode (mem x b)]))
  | _ => none

/-- The literals of an explanation, and the proof of each from the assumption
of the explanation (the only assumption, `0`): `(a, b)` for `(= a b)`,
`(a, false)` for `(not a)`, `(a, true)` for an atom. -/
def lits (h : Node) : Array (Node × EqProof) :=
  match h with
  | .app (.kind .AND) cs =>
    if cs.size ≥ 2 then (cs.mapIdx fun i l => (l, EqProof.fromTrue (.andElim i (.assume 0))))
    else #[(h, .assume 0)]
  | _ => #[(h, .assume 0)]

/-- A proof of `(= a b)` from the literals: `a` is `b`, or an equality literal
relates them. -/
def eqProof (L : Array (Node × EqProof)) (a b : Node) : Option (Option EqProof) :=
  if a == b then some none else
  L.findSome? fun (l, p) =>
    match EqProof.assumptionEq l with
    | (x, y) => if x == a && y == b then some (some p) else if x == b && y == a then some (some (.symm p)) else none

/-- A proof of `(= t v)`, `v` a Boolean constant, from the literals: `t` is an
atom of one of them, or a membership congruent to one (by equality literals
between their arguments). -/
def atomProof (L : Array (Node × EqProof)) (t : Node) : Option EqProof :=
  let isBool (v : Node) := v == Node.mkTrue || v == Node.mkFalse
  match L.findSome? fun (l, p) =>
      match EqProof.assumptionEq l with
      | (a, v) => if a == t && isBool v then some p else none with
  | some p => some p
  | none =>
    match t with
    | .app (.kind .SET_MEMBER) #[x, s] =>
      L.findSome? fun (l, p) =>
        match EqProof.assumptionEq l with
        | (.app (.kind .SET_MEMBER) #[x', s'], v) =>
          if !isBool v then none else do
            let px ← eqProof L x x'
            let ps ← eqProof L s s'
            if px.isNone && ps.isNone then none
            some (.trans (.congAt t #[px, ps]) p)
        | _ => none
    | _ => none

/-- A proof of `(= t c)` for a Boolean constant `c`, from the literals (under
the assumptions `A`): the atoms of `t` that they decide, then the rewriter on
what is left. -/
partial def boolProof (A : Array Node) (L : Array (Node × EqProof)) (t : Node) : Option EqProof :=
  match atomProof L t with
  | some p => some p
  | none =>
    match t with
    | .app (.kind k) cs =>
      if k == .AND || k == .OR || k == .NOT then do
        let args := cs.map (boolProof A L)
        if args.all (·.isNone) then none
        let q : EqProof := .congAt t args
        let (_, t') ← EqProof.check A q
        some (.trans q (.rw t'))
      else none
    | _ => none

/-- Check a proof of `(lem, true)`. -/
def checked (lem : Node) (p : EqProof) : Option EqProof :=
  if EqProof.check #[] p == some (lem, Node.mkTrue) then some p else none

/-- **A proof of `(lem, true)`** from no assumptions, for the lemma `lem` sent
with the identifier `id`. -/
def prove (id : String) (lem : Node) (o : NodeOrder := {}) : Option EqProof := do
  match id, lem with
  | "SETS_PROXY", .app (.kind .EQUAL) #[k, _] => checked lem (.eqTrue (← purifyEq k))
  | "SETS_PROXY_SINGLETON", .app (.kind .SET_MEMBER) #[e, k] =>
    let pk ← purifyEq k
    let s := Node.mkNode .SET_SINGLETON #[e]
    let p1 : EqProof := .congAt lem #[none, some pk]
    let p2 := ruleEq .sets_member_singleton [e, e] (Node.mkNode .SET_MEMBER #[e, s]) (Node.eqNode e e)
    checked lem (.trans p1 (.trans p2 (.rw (Node.eqNode e e))))
  | "SETS_CHOOSE_MEMBER", .app (.kind .OR) #[_, .app (.kind .SET_MEMBER) #[c, _]] =>
    checked lem (.valid lem [DT.argStep .sets_choose_member c])
  | "SETS_DEQ", .app (.kind .IMPLIES) #[h, conc] =>
    let act : EmitM Unit := do
      let p ← push ⟨.refl, [.node h], [], .assume⟩
      let c ← push ⟨.sets_ext, [], [p], .step⟩
      let _ ← push ⟨.scope, [], [c], .pop⟩
    match act.run {} with
    | .ok ((), st) => checked lem (.valid (.app (.kind .IMPLIES) #[h, conc]) (toCmds st.steps))
    | .error _ => none
  | _, .app (.kind .IMPLIES) #[h, conc] =>
    let L := lits h
    let q : EqProof ← match id, conc with
      | "SETS_UP_CLOSURE", .app (.kind .SET_MEMBER) #[x, k]
      | "SETS_UP_CLOSURE_2", .app (.kind .SET_MEMBER) #[x, k] => do
        let pk ← purifyEq k
        let .skolem .PURIFY #[s] := k | none
        let pr ← memberRule x s
        let some (_, R) := EqProof.check #[h] pr | none
        let pb ← boolProof #[h] L R
        some (.trans (.congAt conc #[none, some pk]) (.trans pr pb))
      | "SETS_DOWN_CLOSURE", _ =>
        -- `conc` is the rewrite of a membership in a set of the explanation
        L.findSome? fun (l, _) =>
          match l with
          | .app (.kind .EQUAL) #[_, nv] => do
            let .app (.kind .SET_MEMBER) #[x, _] ← L.findSome? fun (m, _) =>
              match m with | .app (.kind .SET_MEMBER) _ => some m | _ => none
              | none
            let mem := Node.mkNode .SET_MEMBER #[x, nv]
            let p ← atomProof L mem
            -- `conc` is `mem` rewritten in the node order `o`
            if Telos.rewrite mem o != conc then none
            some (.trans (.symm (.rwAt o mem)) p)
          | _ => none
      | _, _ => none
    let p ← DtLemma.implies h conc (.fromTrue q)
    checked lem p
  | _, _ => none

end Telos.Solver.SetsLemma
