import Telos.Solver.StringsCore

/-!
# Certificates of the strings lemmas

A lemma of the theory of strings is valid. `prove id lem o` gives an `EqProof`
of `(lem, true)` from no assumptions, for the lemmas the theory sends
(`Telos/Solver/Theory/Strings.lean`), `o` being the node order in which the
theory rewrote its parts:
- `STRINGS_REGISTER_TERM`, `(and eq ceq)` for `eq` the rewrite of `(= k t)`
  and `ceq` that of `(= (str.len k) l)`, `k` the purification skolem of `t` and
  `l` the rewrite of the length of `t`: `skolem_intro`, congruence for the
  length, and the rewriter (cvc5's `MACRO_SR_PRED_INTRO`);
- `STRINGS_REGISTER_TERM_ATOMIC`, the split of the length of a term:
  `string_length_pos`. The lemmas of the skolems of length at least one, or one,
  are not proven (as in cvc5, whose lemma has no proof generator);
- the splits on a literal (`STRINGS_LEN_SPLIT`, `STRINGS_LEN_SPLIT_EMP`,
  `STRINGS_DEQ_LENGTH_SP`), `(or l (not l))`: the rewriter;
- a core inference sent as a lemma, `(=> h conc)`: its CPC proof
  (`Telos/Solver/StringsCore.lean`).

The proofs are checked when they are made (`EqProof.check`, and Logos's checker
for their CPC steps); a lemma without one is not certified, and a refutation
that needs it leaves the answer `unknown`.
-/

open Eo

namespace Telos.Solver.StringsLemma

open Proof

/-- `(k, t)` for the purification skolem `k` of `t`. -/
def purify? (k : Node) : Option (Node × EqProof) :=
  match k with
  | .skolem .PURIFY #[t] => some (t, .valid (Node.eqNode k t) [DT.argStep .skolem_intro k])
  | _ => none

/-- A proof of `(B, true)` from one `p` of `(A, true)`, for `A` and `B` with
the same rewrite (in the order `o`, or the default one). -/
def viaRw (o : NodeOrder) (A B : Node) (p : EqProof) : Option EqProof :=
  if A == B then some p
  else if Telos.rewrite A o == Telos.rewrite B o then some (.trans (.rwAt o B) (.trans (.symm (.rwAt o A)) p))
  else if Telos.rewrite A == Telos.rewrite B then some (.trans (.rw B) (.trans (.symm (.rw A)) p))
  else none

/-- A proof of `((and l₁ … lₙ), true)` from proofs of each `(lᵢ, true)`:
congruence, then the rewrite of `(and true … true)`. -/
def andIntro (F : Node) (ps : Array EqProof) : Option EqProof := do
  let .app (.kind .AND) ls := F | none
  if ls.size != ps.size then none
  let t := Node.mkNode .AND (ls.map fun _ => Node.mkTrue)
  some (.trans (.congAt F (ps.map some)) (.rw t))

/-- Check a proof of `(lem, true)`. -/
def checked (lem : Node) (p : EqProof) : Option EqProof :=
  if EqProof.check #[] p == some (lem, Node.mkTrue) then some p else none

/-- The purification skolem a side of an equality is. -/
def skolemOfEq? (e : Node) : Option Node :=
  match e with
  | .app (.kind .EQUAL) #[a, b] =>
    match a, b with
    | .skolem .PURIFY _, _ => some a
    | _, .skolem .PURIFY _ => some b
    | _, _ => none
  | _ => none

/-- The CPC proof of `(=> h F)` by one rule from the assumption `h`. -/
def underAssumption (h F : Node) (r : CRule) (args : List PArg) : Option EqProof :=
  let act : EmitM Unit := do
    let p ← push ⟨.refl, [.node h], [], .assume⟩
    let c ← push ⟨r, args, [p], .step⟩
    let _ ← push ⟨.scope, [], [c], .pop⟩
  match act.run {} with
  | .ok ((), st) => some (.valid (Node.mkNode .IMPLIES #[h, F]) (toCmds st.steps))
  | .error _ => none

/-- The term of an eager reduction lemma (`utils::eagerReduce`). -/
def eagerTerm? (lem : Node) : Option Node :=
  match lem with
  | .app (.kind .ITE) #[_, _, .app (.kind .EQUAL) #[t, _]] => some t
  | .app (.kind .AND) #[.app (.kind .OR) #[.app (.kind .EQUAL) #[t, _], _], _] => some t
  | .app (.kind .GEQ) #[t, _] => some t
  | _ => none

/-- The purification skolems of constants in a node. -/
partial def constPurifies (n : Node) (acc : Array Node := #[]) : Array Node :=
  match n with
  | .skolem .PURIFY #[t] => if t.isConst && !acc.contains n then acc.push n else acc
  | .app _ cs => cs.foldl (fun a c => constPurifies c a) acc
  | _ => acc

/-- A proof of `(lem, true)` for a lemma that, with its purification skolems
of constants replaced by the constants (`skolem_intro`), rewrites to `true`
(the symbolic definitions of `checkExtfEval`). -/
def bySymbolic (lem : Node) : Option EqProof := do
  let mut cur := lem
  let mut acc : Option EqProof := none
  for k in constPurifies lem do
    let (t, pk) ← purify? k
    let some q := StringsCore.substOne k t pk cur | continue
    let some (_, cur') := EqProof.check #[] q | none
    cur := cur'
    acc := some (match acc with | some a => .trans a q | none => q)
  if Telos.rewrite cur != Node.mkTrue then none
  let p := match acc with | some a => .trans a (.rw cur) | none => .rw cur
  checked lem p

/-- **A proof of `(lem, true)`** from no assumptions, for the lemma `lem` sent
with the identifier `id`. -/
def prove (id : String) (lem : Node) (o : NodeOrder := {}) : Option EqProof := do
  match id, lem with
  -- an eager reduction (`STRING_EAGER_REDUCTION`)
  | "STRINGS_REGISTER_TERM", l@(.app (.kind .ITE) _) | "STRINGS_REGISTER_TERM", l@(.app (.kind .GEQ) _)
  | "STRINGS_REGISTER_TERM", l@(.app (.kind .AND) #[.app (.kind .OR) _, _]) =>
    let t ← eagerTerm? l
    checked lem (.valid lem [DT.argStep .string_eager_reduction t])
  | "STRINGS_RE_UNFOLD_POS", .app (.kind .IMPLIES) #[h, c] =>
    checked lem (← underAssumption h c .re_unfold_pos [])
  | "STRINGS_CODE_INJ", .app (.kind .OR) #[.app (.kind .EQUAL) #[.app (.kind .STRING_TO_CODE) #[t], _], _,
      .app (.kind .EQUAL) #[_, s']] =>
    checked lem (.valid lem [.step .string_code_inj (.cons t.toEo (.cons s'.toEo .nil)) .nil])
  | "STRINGS_EXTF", l@(.app (.kind .STRING_IN_REGEXP) _) | "STRINGS_EXTF_N", l@(.app (.kind .STRING_IN_REGEXP) _)
  | "STRINGS_EXTF", l@(.app (.kind .NOT) _) | "STRINGS_EXTF_N", l@(.app (.kind .NOT) _) =>
    bySymbolic l
  | "STRINGS_REGISTER_TERM", .app (.kind .AND) #[eq, ceq] =>
    let k ← skolemOfEq? eq
    let (t, pk) ← purify? k
    let p1 ← viaRw o (Node.eqNode k t) eq (.eqTrue pk)
    let lk := Node.mkNode .STRING_LENGTH #[k]
    let lt := Node.mkNode .STRING_LENGTH #[t]
    let p2 ← viaRw o (Node.eqNode lk lt) ceq (.eqTrue (.congAt lk #[some pk]))
    checked lem (← andIntro lem #[p1, p2])
  | "STRINGS_REGISTER_TERM_ATOMIC", .app (.kind .OR) #[.app (.kind .AND) #[_, .app (.kind .EQUAL) #[n, _]], _] =>
    checked lem (.valid lem [DT.argStep .string_length_pos n])
  -- a split on a literal, `(or l (not l))`: `split` (or the rewriter)
  | "STRINGS_LEN_SPLIT", _ | "STRINGS_LEN_SPLIT_EMP", _ | "STRINGS_DEQ_LENGTH_SP", _ =>
    match lem with
    | .app (.kind .OR) #[l, .app (.kind .NOT) #[l']] =>
      if l == l' then checked lem (.valid lem [DT.argStep .split l])
      else if Telos.rewrite lem == Node.mkTrue then checked lem (.rw lem) else none
    | _ => if Telos.rewrite lem == Node.mkTrue then checked lem (.rw lem) else none
  -- a core inference, `(=> h conc)`
  | _, .app (.kind .IMPLIES) #[h, conc] =>
    let P := match h with
      | .app (.kind .AND) cs => cs
      | l => #[l]
    let (F, cs) ← StringsCore.prove id P conc
    if F != lem then none
    checked lem (.valid lem cs)
  | _, _ => none

end Telos.Solver.StringsLemma
