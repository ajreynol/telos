import Std.Data.HashMap
import Telos.Core.Certified
import Telos.Rewriter.Rewrite

/-!
# Building triangular substitution steps

The data of a `Certified.tri` step (`Telos/Core/Tri.lean`), built by
non-clausal simplification: entries read off conjuncts of the result, the
justifications of substitutions, the ground order of the conjuncts the entries
come from, the certified rewrites, and the chain of each conjunct.

`substJ` is `SubstitutionMap::apply` (as `substFact`, `ConjProof.lean`), with a
justification in place of a proof: a term of the substitution is replaced by
its value, which is substituted again (fixed point), and otherwise its children
are, by congruence. Justifications are shared, as terms are, so the step is
linear in the size of the terms as DAGs. Substitution goes below every operator
kind and indexed operator: by congruence below those of `Op.substOk`, and into the
body of a quantifier. Below an application of a function that is not a declared
one, or of a constructor or selector of a type that is not a datatype, it does
not; if it would change something there, building fails, and the caller falls
back.

Nothing here needs a proof: the step is checked (`TriPlan.Ok`) before use.
-/

namespace Telos.Preprocess

open Node

/-- The `minPos` of a justification that uses no entry. -/
def noPos : Nat := 1 <<< 60

/-- The data of a `TriPlan` being built. -/
structure TriB where
  entries : Array Entry := #[]
  justs : Array Just := #[]
  ground : Array GroundItem := #[]
  groundIdx : Std.HashMap Key Nat := {}
  rws : Array ((a : Node) × Rw a) := #[]
  reflIdx : Std.HashMap Key Nat := {}
  /-- The rewriter's cache, kept between the rewrites of a pass. -/
  rwCache : Cache := {}

abbrev TriM := StateT TriB (Except String)

namespace TriM

def addJust (J : Just) : TriM Nat :=
  modifyGet fun s => (s.justs.size, { s with justs := s.justs.push J })

def just (j : Nat) : TriM Just := do
  match (← get).justs[j]? with
  | some J => return J
  | none => throw "tri: no justification"

/-- The reflexive justification of `n`. -/
def refl (n : Node) : TriM Nat := do
  if let some j := (← get).reflIdx.get? ⟨n⟩ then return j
  let j ← addJust ⟨n, n, noPos, .refl⟩
  modify fun s => { s with reflIdx := s.reflIdx.insert ⟨n⟩ j }
  return j

/-- `n` and its subterms in the ground order, children first. -/
partial def ground (n : Node) : TriM Nat := do
  if let some g := (← get).groundIdx.get? ⟨n⟩ then return g
  if !n.groundLocal then throw s!"tri: not ground ({repr n.getKind})"
  let kids ← n.getChildren.mapM ground
  modifyGet fun s =>
    (s.ground.size, { s with ground := s.ground.push ⟨n, kids⟩,
                             groundIdx := s.groundIdx.insert ⟨n⟩ s.ground.size })

/-- The entry `lhs ↦ rhs`, read off the conjunct `conj` of the result at `pos`. -/
def entry (lhs rhs : Node) (pos : Nat) (conj : Node) : TriM Nat := do
  let g ← ground conj
  modifyGet fun s => (s.entries.size, { s with entries := s.entries.push ⟨lhs, rhs, pos, g⟩ })

/-- A certified rewrite, as a chain step. -/
def rw {a : Node} (r : Rw a) : TriM ChainStep :=
  modifyGet fun s => (.rw s.rws.size, { s with rws := s.rws.push ⟨a, r⟩ })

end TriM

/-- A substitution: the entry of each term. -/
abbrev TSubst := Std.HashMap Key Nat

/-- Results of `substJ`, by term: the justification, or `none` (unchanged). -/
abbrev SubstCache := Std.HashMap Key (Option Nat)

abbrev SubstM := StateT SubstCache TriM

/-- `SubstitutionMap::apply` of `σ` to `n`: the justification relating `n` to
the result, or `none` if `n` is unchanged. -/
partial def substJ (σ : TSubst) (n : Node) : SubstM (Option Nat) := do
  if let some r := (← get).get? ⟨n⟩ then return r
  let r ← match σ.get? ⟨n⟩ with
    | some e => some <$> entryJ e
    | none =>
      match n with
      | .app op cs =>
        if op.substOk then do
          let ks ← cs.mapM (substJ σ)
          if ks.all (·.isNone) then pure none
          else
            let kids ← (cs.zip ks).mapM fun (c, k) => match k with
              | some j => pure j
              | none => liftM (TriM.refl c)
            let Js ← kids.mapM fun j => liftM (TriM.just j)
            let n' : Node := .app op (Js.map (·.b))
            if σ.contains ⟨n'⟩ then throw "tri: rebuilt term of the substitution"
            let minPos := Js.foldl (fun m J => min m J.minPos) noPos
            some <$> liftM (TriM.addJust ⟨n, n', minPos, .congr kids⟩)
        else if op == .kind .FORALL || op == .kind .EXISTS then do
          -- only the body: the variables and patterns are left as they are
          let some body := cs[1]? | pure none
          let some j ← substJ σ body | pure none
          let J ← liftM (TriM.just j)
          let n' : Node := .app op (cs.set! 1 J.b)
          if σ.contains ⟨n'⟩ then throw "tri: rebuilt term of the substitution"
          some <$> liftM (TriM.addJust ⟨n, n', J.minPos, .body j⟩)
        else do
          let ks ← cs.mapM (substJ σ)
          if ks.any (·.isSome) then throw "tri: substitution below an operator"
          pure none
      | _ => pure none
  modify (·.insert ⟨n⟩ r)
  return r
where
  entryJ (e : Nat) : SubstM Nat := do
    let some E := (← liftM (get : TriM TriB)).entries[e]? | throw "tri: no entry"
    let kj ← match ← substJ σ E.rhs with
      | some j => pure j
      | none => liftM (TriM.refl E.rhs)
    let K ← liftM (TriM.just kj)
    liftM (TriM.addJust ⟨E.lhs, K.b, min E.pos K.minPos, .entry e kj⟩)

/-- `applyTrusted(n, rw)` of a substitution: its application to `n`, then the
rewrite; the result and the chain steps (none when the result is `n`). -/
def applyRwJ (σ : TSubst) (n : Node) : SubstM (Node × Array ChainStep) := do
  let some j ← substJ σ n | return (n, #[])
  let n₁ := (← liftM (TriM.just j)).b
  let r ← liftM (modifyGet fun s : TriB =>
    let (r, c) := rewriteCertCached s.rwCache n₁
    (r, { s with rwCache := c }) : TriM (Rw n₁))
  if r.1 == n then return (n, #[])
  if r.1 == n₁ then return (n₁, #[.subst j])
  return (r.1, #[.subst j, ← liftM (TriM.rw r)])

/-- `processLearnedLit` (and the simplification of an assertion): the
substitution `σn`, then `σc` to a fixed point, each followed by the rewriter.
The caches are those of `σn` and `σc`. -/
def simplifyJ (σn σc : TSubst) (cn cc : SubstCache) (n : Node) :
    TriM ((Node × Array ChainStep) × SubstCache × SubstCache) := do
  let ((n₁, st₁), cn) ← (applyRwJ σn n).run cn
  let mut cur := n₁
  let mut steps := st₁
  let mut cc := cc
  for _ in [0:1000] do
    let ((n₂, st₂), cc') ← (applyRwJ σc cur).run cc
    cc := cc'
    if st₂.isEmpty then break
    steps := steps ++ st₂
    cur := n₂
  return ((cur, steps), cn, cc)

/-- The `Certified.tri` step from `n` to `k`, if its side condition holds. -/
def triRw (n k : Node) (B : TriB) (chains : Array (Array ChainStep)) : Option (Rw n) :=
  let P : TriPlan := { entries := B.entries, justs := B.justs, ground := B.ground,
                       rws := B.rws.map (fun r => (r.1, r.2.1)), chains }
  if h : P.Ok n k = true then
    some ⟨k, .tri P h (fun r hr =>
      have hr' : r < B.rws.size := by simpa [P] using hr
      cast (by simp [P]) (B.rws[r]'hr').2.2) (.refl k)⟩
  else none

end Telos.Preprocess
