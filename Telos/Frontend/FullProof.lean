import Telos.Frontend.Solve
import Telos.Core.Proof.Shared
import Telos.Preprocess.ProofExt

/-!
# Full CPC proofs of `unsat`

The CPC proof of an `unsat` answer, from the input assertions to `false`, as
cvc5's `get-proof` prints one (`--dump-proofs`, `(get-proof)`). It connects
the certificates that telos checks, each turned into CPC steps:

1. **The input.** Each assertion `aᵢ` is an `assume`; `and_intro` gives the
   input node `I = (and a₁ … aₙ true true)` (`Preprocess.inputNode`).
2. **Preprocessing.** The certified pipeline's proof of `(= I O)`
   (`Proof.emitChainWith Preprocess.preprocessExt`, as `--post-asserts
   --proof` prints it), then `eq_resolve` gives `O`, and `and_elim` each
   preprocessed assertion. The pipeline is recomputed (proofs are post hoc:
   solving does not depend on them), and must give the assertions the solver
   was given.
3. **A refutation of the engine alone** (a conjunction of literals): its
   certificate `(A, p)` (`EqProof`), from the literals of `A` (`and_elim`s of
   the preprocessed assertions), as `Telos/Solver/EqProofCpc.lean` does.
4. **A refutation of the SAT solver** (`Telos/Solver/SatProof.lean`): each
   clause of the certificate by its justification,
   - an input clause by the elimination rules of the connectives above it
     (`and_elim`, `not_or_elim`, `implies_elim`, `xor_elim1`, `ite_elim2`, …,
     the top level of the CNF stream's `convertAndAssert`);
   - a definition clause by the CNF rule of its connective (`cnf_and_pos`,
     `cnf_or_neg`, …, the CNF stream's `handle*`);
   - a theory conflict `(A, p)` by a refutation of `A` under the scopes of
     its literals, then `process_scope` and `not_and`: `(or (not a₁) …)`;
   - a lemma `F`, from its proof of `(F, true)`, then as an input clause;
   the literals with double negations, which telos's literals take off
   (`SatProof.litOf`), by resolution with `(or (not (not (not l))) l)`-like
   clauses (`not_not_elim` under a scope). Then each learned clause, and the
   empty clause, by `chain_m_resolution` from the trace of unit propagation
   that the certificate's reverse unit propagation (`rup`) finds: trivial
   resolution, from the conflict back through the reasons.

What has no CPC proof yet is reported, and no proof is printed: the
certificates of linear arithmetic (`LinCert`), and rewrites by semantic steps.
telos does not check the proof (the answer is certified without it); Ethos
does.
-/

open Eo

namespace Telos.Frontend

open Proof Solver SatProof

/-- A clause of the refutation: its literals (as the certificate has them) and
the position of its CPC fact (`(or l₁ … lₙ)`, `l₁` for one literal, `false`
for none). -/
structure DClause where
  lits : Array Node
  pos : Nat
  deriving Inhabited

/-- The CPC formula of a clause. -/
def clauseNode (ls : Array Node) : Node :=
  if ls.size == 0 then Node.mkFalse
  else if ls.size == 1 then ls[0]!
  else Node.mkNode .OR ls

def numArg (i : Nat) : PArg := .term (Term.Numeral i)

/-- A fact `true`. -/
def factTrue : EmitM Nat := do
  let r ← push ⟨.refl, [.node Node.mkTrue], [], .step⟩
  push ⟨.true_elim, [], [r], .step⟩

/-- A fact `(not false)`. -/
def factNotFalse : EmitM Nat := do
  let e ← push ⟨.evaluate, [.node (Node.notNode Node.mkFalse)], [], .step⟩
  push ⟨.true_elim, [], [e], .step⟩

/-- `(not (not t))`'s `t`. -/
def strip2 : Node → Option Node
  | .app (.kind .NOT) #[.app (.kind .NOT) #[t]] => some t
  | _ => none

/-- The clause at `q`, whose literals are `rs` as CPC has them, with each
literal as telos has it (`litOf`, without double negations): a literal `r`
that is not is resolved with `(or (not r) r')`, proved by `not_not_elim`s
under the scope of `r`. -/
def normalize (q : Nat) (rs : List Node) : EmitM DClause := do
  let mut cur := q
  let mut lits := rs.toArray
  for r in rs do
    let n := litOf r false
    if n == r then continue
    let a ← push ⟨.refl, [.node r], [], .assume⟩
    let mut f := a
    let mut t := r
    for _ in [0:64] do
      if t == n then break
      let some t' := strip2 t | throw "a literal that is not a double negation"
      f ← push ⟨.not_not_elim, [], [f], .step⟩
      t := t'
    let imp ← push ⟨.scope, [], [f], .pop⟩
    let cl ← push ⟨.implies_elim, [], [imp], .step⟩
    cur ← push ⟨.resolution, [.term (Term.Boolean true), .node r], [cur, cl], .step⟩
    lits := (lits.erase r).push n
  -- (a literal twice: `factoring`)
  let dedup := lits.foldl (fun acc l => if acc.contains l then acc else acc.push l) #[]
  if dedup.size != lits.size then
    cur ← push ⟨.factoring, [], [cur], .step⟩
    lits := dedup
  return ⟨lits, cur⟩

/-- A boolean equality. -/
def isBoolEq : Node → Bool
  | .app (.kind .EQUAL) #[a, _] => a.typeHint == some .boolean
  | _ => false

/-- **The clauses of an input formula** `f` (with `neg`, of `(not f)`), whose
fact is at `q`, as `inputClauses f neg` has them: by the elimination rules of
the connectives above them. -/
partial def inputClausesOf (f : Node) (neg : Bool) (q : Nat) : EmitM (List DClause) := do
  let one (r : CRule) (raw : List Node) : EmitM (List DClause) := do
    let c ← push ⟨r, [], [q], .step⟩
    return [← normalize c raw]
  let unit : EmitM (List DClause) := do
    return [← normalize q [if neg then Node.notNode f else f]]
  match f with
  | .app (.kind .AND) cs =>
    if !neg then
      let mut out := []
      for h : j in [0:cs.size] do
        let c ← push ⟨.and_elim, [numArg j], [q], .step⟩
        out := out ++ (← inputClausesOf cs[j] false c)
      return out
    else if cs.size ≥ 2 then one .not_and (cs.toList.map Node.notNode)
    else unit
  | .app (.kind .OR) cs =>
    if !neg then return [← normalize q cs.toList]
    else
      let mut out := []
      for h : j in [0:cs.size] do
        let c ← push ⟨.not_or_elim, [numArg j], [q], .step⟩
        out := out ++ (← inputClausesOf cs[j] true c)
      return out
  | .app (.kind .XOR) #[a, b] =>
    if !neg then return (← one .xor_elim2 [Node.notNode a, Node.notNode b]) ++ (← one .xor_elim1 [a, b])
    else return (← one .not_xor_elim2 [Node.notNode a, b]) ++ (← one .not_xor_elim1 [a, Node.notNode b])
  | .app (.kind .IMPLIES) #[a, b] =>
    if !neg then one .implies_elim [Node.notNode a, b]
    else
      let qa ← push ⟨.not_implies_elim1, [], [q], .step⟩
      let qb ← push ⟨.not_implies_elim2, [], [q], .step⟩
      return (← inputClausesOf a false qa) ++ (← inputClausesOf b true qb)
  | .app (.kind .ITE) #[c, t, e] =>
    if !neg then return (← one .ite_elim1 [Node.notNode c, t]) ++ (← one .ite_elim2 [c, e])
    else return (← one .not_ite_elim1 [Node.notNode c, Node.notNode t]) ++ (← one .not_ite_elim2 [c, Node.notNode e])
  | .app (.kind .NOT) #[x] =>
    if !neg then inputClausesOf x true q
    else
      let qx ← push ⟨.not_not_elim, [], [q], .step⟩
      inputClausesOf x false qx
  | e@(.app (.kind .EQUAL) #[a, b]) =>
    if !isBoolEq e then unit
    else if !neg then return (← one .equiv_elim1 [Node.notNode a, b]) ++ (← one .equiv_elim2 [a, Node.notNode b])
    else return (← one .not_equiv_elim2 [Node.notNode a, Node.notNode b]) ++ (← one .not_equiv_elim1 [a, b])
  | _ => unit

/-- **The definition clauses of the connective `n`** (`defClauses n`): the CNF
rules of its connective, each without premises. -/
def defClausesOf (n : Node) : EmitM (List DClause) := do
  let nn := Node.notNode n
  let ax (r : CRule) (args : List PArg) (raw : List Node) : EmitM DClause := do
    let c ← push ⟨r, args, [], .step⟩
    normalize c raw
  match n with
  | .app (.kind .AND) cs =>
    let mut out := []
    for h : i in [0:cs.size] do
      out := out ++ [← ax .cnf_and_pos [.node n, numArg i] [nn, cs[i]]]
    return out ++ [← ax .cnf_and_neg [.node n] (n :: cs.toList.map Node.notNode)]
  | .app (.kind .OR) cs =>
    let mut out := [← ax .cnf_or_pos [.node n] (nn :: cs.toList)]
    for h : i in [0:cs.size] do
      out := out ++ [← ax .cnf_or_neg [.node n, numArg i] [n, Node.notNode cs[i]]]
    return out
  | .app (.kind .XOR) #[a, b] =>
    return [← ax .cnf_xor_pos1 [.node n] [nn, a, b],
            ← ax .cnf_xor_pos2 [.node n] [nn, Node.notNode a, Node.notNode b],
            ← ax .cnf_xor_neg1 [.node n] [n, Node.notNode a, b],
            ← ax .cnf_xor_neg2 [.node n] [n, a, Node.notNode b]]
  | e@(.app (.kind .EQUAL) #[a, b]) =>
    if !isBoolEq e then return [] else
    return [← ax .cnf_equiv_pos1 [.node n] [nn, Node.notNode a, b],
            ← ax .cnf_equiv_pos2 [.node n] [nn, a, Node.notNode b],
            ← ax .cnf_equiv_neg1 [.node n] [n, a, b],
            ← ax .cnf_equiv_neg2 [.node n] [n, Node.notNode a, Node.notNode b]]
  | .app (.kind .IMPLIES) #[a, b] =>
    return [← ax .cnf_implies_pos [.node n] [nn, Node.notNode a, b],
            ← ax .cnf_implies_neg1 [.node n] [n, a],
            ← ax .cnf_implies_neg2 [.node n] [n, Node.notNode b]]
  | .app (.kind .ITE) #[c, t, e] =>
    return [← ax .cnf_ite_pos1 [.node n] [nn, Node.notNode c, t],
            ← ax .cnf_ite_pos2 [.node n] [nn, c, e],
            ← ax .cnf_ite_pos3 [.node n] [nn, t, e],
            ← ax .cnf_ite_neg1 [.node n] [n, Node.notNode c, Node.notNode t],
            ← ax .cnf_ite_neg2 [.node n] [n, c, Node.notNode e],
            ← ax .cnf_ite_neg3 [.node n] [n, Node.notNode t, Node.notNode e]]
  | _ => return []

/-- `false`, from the facts `(= true false)`. -/
def falseOf (c : Nat) : EmitM Nat := do
  let s ← push ⟨.symm, [], [c], .step⟩
  push ⟨.true_elim, [], [s], .step⟩

/-! ## Linear arithmetic

A certificate of linear arithmetic (`LinCert`) refutes its literals:
- a Farkas combination `Σ qᵢ · (aᵢ - bᵢ) ⋈ 0`: each literal is restated as a
  bound `bᵢ ≤ aᵢ` (`bᵢ < aᵢ`, `bᵢ = aᵢ`; for integers, a strict bound as
  `bᵢ + 1 ≤ aᵢ`; over reals, with `to_real`, when the combination has reals)
  by rewriting both to the same form; scaled by `arith_mult_pos` (the
  coefficients made integers); summed by `arith_sum_ub`; and the sum rewritten
  to `false`, as the certificate's check rewrites its comparison;
- a split of `(not (= a b))` into `(< a b)` and `(> a b)`, a cut on `l`, the
  cases of `(not (and c₁ … cₙ))`: each case refuted under its scope, then
  `process_scope`, and `arith_trichotomy`, `contra` or `and_intro`.
-/

/-- The fact of the formula `G`, from the fact of `F` at `q`, when they rewrite
to the same formula: `eq_resolve` with `(= F G)`. -/
def byRewrite (F G : Node) (q : Nat) : EmitM Nat := do
  if F == G then return q
  if Telos.rewrite F != Telos.rewrite G then
    throw s!"a bound that does not rewrite as its literal: {F.toSmtLib} and {G.toSmtLib}"
  let e ← emitEq #[] #[] (.trans (.rw F) (.symm (.rw G)))
  push ⟨.eq_resolve, [], [q, e], .step⟩

def lcmDen (qs : List Rat) : Nat := qs.foldl (fun k q => Nat.lcm k q.den) 1

/-- **A Farkas combination**, refuted: see above. -/
def farkasFalse (A : Array Node) (pos : Array Nat) (cs : Array (Node × Rat)) : EmitM Nat := do
  let cs := cs.filter fun (_, q) => q != 0
  if cs.isEmpty then throw "an empty Farkas combination"
  let k : Rat := lcmDen (cs.toList.map (·.2))
  let useReal := cs.any fun (l, _) => match linParts l with
    | some (a, b, _) => isRealTerm a || isRealTerm b
    | none => false
  let toR (t : Node) : Node := if useReal && isIntTerm t then Node.mkNode .TO_REAL #[t] else t
  let mut scaled : Array (Nat × Node) := #[]
  for (l, q) in cs do
    let some (a, b, r) := linParts l | throw "a Farkas entry that is not a bound"
    let some i := A.idxOf? l | throw "a Farkas entry that is not a literal of the conflict"
    let isInt := isIntTerm a && isIntTerm b
    -- the bound `(rel lo hi)`, `lo ≤ hi`, and its positive coefficient
    let (lo, hi, rel, m) : Node × Node × Kind × Rat := match r with
      | .ge => (b, a, .LEQ, q * k)
      | .gt => if isInt then (Node.mkNode .ADD #[b, .const (.integer 1)], a, .LEQ, q * k) else (b, a, .LT, q * k)
      | .eq => if q < 0 then (a, b, .EQUAL, -q * k) else (b, a, .EQUAL, q * k)
    let (lo, hi) := (toR lo, toR hi)
    let L := Node.mkNode rel #[lo, hi]
    let qL ← byRewrite l L pos[i]!
    let mNode : Node := if useReal || !isInt then .const (.rational m) else .const (.integer m.num)
    let zero : Node := if useReal || !isInt then .const (.rational 0) else .const (.integer 0)
    let gt0 := Node.mkNode .GT #[mNode, zero]
    let e ← push ⟨.evaluate, [.node gt0], [], .step⟩
    let qm ← push ⟨.true_elim, [], [e], .step⟩
    let imp ← push ⟨.arith_mult_pos, [.node mNode, .node L], [], .step⟩
    let conj ← push ⟨.and_intro, [], [qm, qL], .step⟩
    let sq ← push ⟨.modus_ponens, [], [conj, imp], .step⟩
    let scaledRel := Node.mkNode rel #[Node.mkNode .MULT #[mNode, lo], Node.mkNode .MULT #[mNode, hi]]
    scaled := scaled.push (sq, scaledRel)
  -- the sum, as `arith_sum_ub` forms it: `<` if a bound is, else `<=`
  let (qS, S) ← if h : scaled.size = 1 then pure scaled[0] else do
    let q ← push ⟨.arith_sum_ub, [], scaled.toList.map (·.1), .step⟩
    let rels := scaled.map fun (_, f) => f.getKind
    let rel := if rels.contains .LT then Kind.LT else .LEQ
    let side (j : Nat) := Node.mkNode .ADD (scaled.map fun (_, f) => f.getChildren[j]!)
    pure (q, Node.mkNode rel #[side 0, side 1])
  if Telos.rewrite S != Node.mkFalse then throw s!"a Farkas sum that does not rewrite to false: {S.toSmtLib}"
  let e ← emitEq #[] #[] (.rw S)
  -- `(= S false)`: `S` and `(not S)` from `false_elim`
  let nS ← push ⟨.false_elim, [], [e], .step⟩
  push ⟨.contra, [], [qS, nS], .step⟩

mutual
/-- **A refutation of linear arithmetic** of the literals `A` (with facts at
`pos`): the position of `false`. -/
partial def refuteLin (A : Array Node) (pos : Array Nat) : LinCert → EmitM Nat
  | .farkas cs => farkasFalse A pos cs
  | .split l lt gt => do
    let some (a, b) := diseqParts l | throw "a split of a literal that is not a disequality"
    let some i := A.idxOf? l | throw "a split of a literal that is not asserted"
    let n1 ← underScope A pos (Node.mkNode .LT #[a, b]) lt
    let n2 ← underScope A pos (Node.mkNode .GT #[a, b]) gt
    let eq ← push ⟨.arith_trichotomy, [], [n1, n2], .step⟩
    push ⟨.contra, [], [eq, pos[i]!], .step⟩
  | .cut l p n => do
    let n1 ← underScope A pos l p
    let n2 ← underScope A pos (negate l) n
    match l with
    | .app (.kind .NOT) #[_] => push ⟨.contra, [], [n2, n1], .step⟩
    | _ => push ⟨.contra, [], [n1, n2], .step⟩
  | .cases l subs => do
    let some cs := notAndParts l | throw "cases of a literal that is not a negated conjunction"
    let some i := A.idxOf? l | throw "cases of a literal that is not asserted"
    let mut facts := #[]
    for c in cs do
      let some (_, sub) := subs.find? (·.1 == c) | throw "a case without a refutation"
      let n ← underScope A pos (negate c) sub
      match c with
      | .app (.kind .NOT) #[_] => facts := facts.push n
      | _ => facts := facts.push (← push ⟨.not_not_elim, [], [n], .step⟩)
    let conj ← push ⟨.and_intro, [], facts.toList, .step⟩
    push ⟨.contra, [], [conj, pos[i]!], .step⟩

/-- `(not lit)`: the refutation `c` of `A` with `lit`, under the scope of `lit`,
then `process_scope`. -/
partial def underScope (A : Array Node) (pos : Array Nat) (lit : Node) (c : LinCert) : EmitM Nat := do
  let q ← push ⟨.refl, [.node lit], [], .assume⟩
  let f ← refuteLin (A.push lit) (pos.push q) c
  let imp ← push ⟨.scope, [], [f], .pop⟩
  push ⟨.process_scope, [.node Node.mkFalse], [imp], .step⟩
end

/-- **The clause of a theory conflict** `A`, refuted by `refute` (from the
facts of `A`): under the scopes of the literals of `A`, the refutation; then
`process_scope` gives `(not (and a₁ … aₖ))` (`(not a₁)` for one), and
`not_and` the clause. -/
def conflictClauseBy (A : Array Node) (refute : Array Nat → EmitM Nat) : EmitM DClause := do
  if A.isEmpty then
    return ⟨#[], ← refute #[]⟩
  let mut pos := #[]
  for a in A do
    pos := pos.push (← push ⟨.refl, [.node a], [], .assume⟩)
  let mut f ← refute pos
  for _ in A do
    f ← push ⟨.scope, [], [f], .pop⟩
  let n ← push ⟨.process_scope, [.node Node.mkFalse], [f], .step⟩
  if A.size == 1 then normalize n [Node.notNode A[0]!]
  else
    let cl ← push ⟨.not_and, [], [n], .step⟩
    normalize cl (A.toList.map Node.notNode)

/-- The clause of a conflict `(A, p)` of the equality engine. -/
def conflictClause (A : Array Node) (p : EqProof) : EmitM DClause :=
  conflictClauseBy A fun pos => do falseOf (← emitEq A pos p)

/-- The pivot of a propagated literal `x`, as `chain_m_resolution` takes it:
its atom, and whether `x` is its negation (the earlier clause has the atom). -/
def pivotOf : Node → Node × Bool
  | .app (.kind .NOT) #[a] => (a, true)
  | a => (a, false)

/-- **A clause by trivial resolution**: unit propagation from the negations of
the literals of `c` over the clauses `db` (as `rup` does), then
`chain_m_resolution` from the conflict back through the reasons of the
literals it needs; `none` if propagation finds no conflict. The clause
derived is the part of `c` that the resolution keeps (a subset: CPC's
`chain_m_resolution` weakens to a clause of two literals or more only). -/
def resolveRup (db : Array DClause) (c : Array Node) : EmitM (Option DClause) := do
  -- the true literals, with the clause that propagated each (`none`: assumed)
  let mut val : Std.HashMap Key (Option Nat) := {}
  for l in c do val := val.insert ⟨negate l⟩ none
  let mut trail : Array (Node × Nat) := #[]
  let mut conflict : Option Nat := none
  let mut changed := true
  while changed && conflict.isNone do
    changed := false
    for h : k in [0:db.size] do
      let d := db[k]
      let open_ := d.lits.filter fun l => !val.contains ⟨negate l⟩
      if open_.isEmpty then
        conflict := some k
        break
      if open_.size == 1 && !val.contains ⟨open_[0]!⟩ then
        val := val.insert ⟨open_[0]!⟩ (some k)
        trail := trail.push (open_[0]!, k)
        changed := true
  let some k := conflict | return none
  -- backwards through the trail: the literals whose negations are needed
  let mut need : Std.HashSet Key := db[k]!.lits.foldl (fun s l => s.insert ⟨l⟩) {}
  let mut prems := #[db[k]!.pos]
  let mut pols : Array Term := #[]
  let mut lits : Array Node := #[]
  for (x, r) in trail.reverse do
    if !need.contains ⟨negate x⟩ then continue
    let (L, pol) := pivotOf x
    prems := prems.push db[r]!.pos
    pols := pols.push (Term.Boolean pol)
    lits := lits.push L
    for l in db[r]!.lits do
      if l != x then need := need.insert ⟨l⟩
  -- the literals left: those of `c` that are needed
  let kept := c.filter fun l => need.contains ⟨l⟩
  let target := clauseNode kept
  if pols.isEmpty then
    -- the conflict clause is in `c`
    return some db[k]!
  let listOf (xs : List Term) : Term := xs.foldr (fun x t => Term.Apply (Term.Apply .__eo_List_cons x) t) .__eo_List_nil
  return some ⟨kept, ← push ⟨.chain_m_resolution,
    [.node target, .term (listOf pols.toList), .term (listOf (lits.toList.map Node.toEo))], prems.toList, .step⟩⟩

/-- The facts of the literals of the conjunction-of-literals assertions `out`
at `qs`, by `and_elim`. -/
def literalFacts (out : List Node) (qs : List Nat) : EmitM (Std.HashMap Key Nat) := do
  let mut m : Std.HashMap Key Nat := {}
  for (o, q) in out.zip qs do
    m := m.insert ⟨o⟩ q
    if let .app (.kind .AND) cs := o then
      for h : j in [0:cs.size] do
        if !m.contains ⟨cs[j]⟩ then
          m := m.insert ⟨cs[j]⟩ (← push ⟨.and_elim, [numArg j], [q], .step⟩)
  return m

/-- **The steps of the full proof**, and the number of input assumptions at
their head. -/
def fullSteps (sc : Script) (u : Preprocess.UserOptions) (out : List Node) (r : Solver.Result) :
    Except String (Array Step × Nat × Std.HashMap Nat Node) := do
  let (opts, as) ← ppInput sc u
  if as.isEmpty then throw "no assertions"
  let p := Preprocess.preprocessCert as opts (inputOrder sc as)
  let I := Preprocess.inputNode as
  let O := p.1
  let outs := match O with
    | .app (.kind .AND) cs => if 2 ≤ cs.size then cs.toList.dropLast else [O]
    | n => [n]
  if outs != out then throw "the preprocessed assertions are not the solver's"
  let act : EmitM (Array DClause) := do
    -- 1. the input
    let mut aq := #[]
    for a in as do aq := aq.push (← push ⟨.refl, [.node a], [], .step⟩)
    let t1 ← factTrue
    let t2 ← factTrue
    let qI ← push ⟨.and_intro, [], aq.toList ++ [t1, t2], .step⟩
    -- 2. preprocessing
    let qeq ← closeChain I (← emitChainWith Preprocess.preprocessExt p.2)
    let qO ← push ⟨.eq_resolve, [], [qI, qeq], .step⟩
    let mut oq := #[]
    match O with
    | .app (.kind .AND) cs =>
      if 2 ≤ cs.size then
        for j in [0:cs.size - 1] do oq := oq.push (← push ⟨.and_elim, [numArg j], [qO], .step⟩)
      else oq := #[qO]
    | _ => oq := #[qO]
    -- 3. a refutation of the engine
    if let some (A, ep) := r.cert then
      let m ← literalFacts out oq.toList
      let pos ← A.mapM fun a => match m.get? ⟨a⟩ with
        | some q => pure q
        | none => throw s!"a literal of the refutation that is not asserted: {a.toSmtLib}"
      let c ← emitEq A pos ep
      let _ ← falseOf c
      return #[]
    -- 4. a refutation of the SAT solver
    let some (inputs, cert) := r.satCert | throw "an unsat answer without a certificate"
    let mut inputFacts : Std.HashMap Nat Nat := {}
    for (o, q) in out.zip oq.toList do
      let i := 2 + inputFacts.size
      let _ := o
      inputFacts := inputFacts.insert i q
    let mut db : Array DClause := #[]
    let mut doneInputs : Std.HashSet Nat := {}
    let mut doneDefs : Std.HashSet Key := {}
    for (_, j) in cert.clauses do
      match j with
      | .input i =>
        if doneInputs.contains i then continue
        doneInputs := doneInputs.insert i
        let some f := inputs[i]? | throw "an input out of range"
        let q ← if i == 0 then factTrue else if i == 1 then factNotFalse else
          match inputFacts.get? i with
          | some q => pure q
          | none => throw "an input formula without a fact"
        db := db ++ (← inputClausesOf f false q).toArray
      | .defn n =>
        if doneDefs.contains ⟨n⟩ then continue
        doneDefs := doneDefs.insert ⟨n⟩
        db := db ++ (← defClausesOf n).toArray
      | .theory A ep => db := db.push (← conflictClause A ep)
      | .lemma F ep =>
        let c ← emitEq #[] #[] ep
        let q ← push ⟨.true_elim, [], [c], .step⟩
        db := db ++ (← inputClausesOf F false q).toArray
      | .arith A lc => db := db.push (← conflictClauseBy A fun pos => refuteLin A pos lc)
    for c in cert.learned do
      let some d ← resolveRup db c | throw "a learned clause that does not follow by unit propagation"
      db := db.push d
      -- (the empty clause already)
      if d.lits.isEmpty then break
    let some ⟨_, q⟩ ← resolveRup db #[] | throw "the empty clause does not follow by unit propagation"
    -- (the last step concludes `false`)
    let st ← get
    if st.steps.size == 0 || q + 1 != st.steps.size then
      let _ ← push ⟨.reordering, [.node Node.mkFalse], [q], .step⟩
    return db
  let (db, st) ← act.run {}
  -- the clauses' conclusions, as telos has them (stated with `conclusions`)
  let concls := db.foldl (fun m d => m.insert d.pos (clauseNode d.lits)) {}
  return (st.steps, as.length, concls)

/-- **The CPC proof of an `unsat` answer** `r` of the script `sc`, from its
input assertions to `false`, printed as cvc5's `get-proof` prints one. -/
def fullProof (sc : Script) (u : Preprocess.UserOptions) (out : List Node) (r : Solver.Result)
    (conclusions : Bool := false) : Except String String := do
  let (steps, n, concls) ← fullSteps sc u out r
  return Proof.renderRefutation sc.names sc.decls steps n (if conclusions then concls else {})

end Telos.Frontend
