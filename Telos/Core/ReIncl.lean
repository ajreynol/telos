import Std.Data.HashMap
import Cpc.Logos
import Telos.Core.Node.SmtTypeFast

/-!
# Inclusion of regular expressions

CPC's `re-inter-inclusion` and `re-union-inclusion` hold when one regular
expression includes another by `$str_re_includes`, a search over the components
of the two, which is exponential for Logos: a pair is searched each time it is
reached. `ReIncl.rec` is the same search with a cache of the pairs decided, as
cvc5's `RegExpEntail::regExpIncludes` has. The step is then `StaticProc.reIncl`
(`Telos/Core/Static.lean`), and `verification/TelosProofs/Core/ReIncl.lean`
proves that a result `some b` is the value Logos computes.

The terms searched are flattened (`$re_flatten`), and the leaves (a constant
string in a regular expression, two ranges) are evaluated, by Logos's programs.
-/

open Eo

namespace Telos.ReIncl

/-- A hash of a term's outer constructors, up to the depth given. -/
def hashTerm : Nat → Term → UInt64
  | 0, _ => 3
  | n + 1, .Apply f x => mixHash (hashTerm n f) (hashTerm n x)
  | _, .UOp op => mixHash 5 (UInt64.ofNat op.ctorIdx)
  | _, .String s => mixHash 7 (hash s)
  | _, .UConst i _ => mixHash 11 (UInt64.ofNat i)
  | _, _ => 13

/-- A pair of terms as a hash-map key. -/
structure Pair where
  fst : Term
  snd : Term

/-- Equality of terms, in constant time for terms that are the same in memory. -/
def eqTerm (a b : Term) : Bool := @decide (a = b) (withPtrEqDecEq a b fun _ => inferInstance)

instance : BEq Pair := ⟨fun p q => eqTerm p.fst q.fst && eqTerm p.snd q.snd⟩
instance : Hashable Pair := ⟨fun p => mixHash (hashTerm 14 p.fst) (hashTerm 14 p.snd)⟩

theorem eqTerm_iff {a b : Term} : eqTerm a b = true ↔ a = b := by simp [eqTerm]

instance : LawfulBEq Pair where
  eq_of_beq {p q} h := by
    cases p; cases q
    simp only [BEq.beq, Bool.and_eq_true, eqTerm_iff] at h
    rw [h.1, h.2]
  rfl {p} := by simp [BEq.beq, eqTerm_iff]

instance : LawfulHashable Pair where
  hash_eq {p q} h := by rw [eq_of_beq h]

/-- The pairs decided: whether the first includes the second. -/
abbrev Cache := Std.HashMap Pair Bool

/-- A search, with its cache. The result is `none` when it is not known. -/
abbrev M := Cache → Option Bool × Cache

/-- The Boolean `b`. -/
def ret (b : Bool) : M := fun c => (some b, c)

/-- `x`, or `y` if it is false. -/
@[inline] def orElse (x y : M) : M := fun c =>
  match x c with
  | (some true, c) => (some true, c)
  | (some false, c) => y c
  | r => r

/-- `x`, and `y` if it is true. -/
@[inline] def andThen (x y : M) : M := fun c =>
  match x c with
  | (some true, c) => y c
  | (some false, c) => (some false, c)
  | r => r

/-- The value of a term Logos has computed. -/
def ofTerm : Term → M
  | .Boolean b => ret b
  | _ => fun c => (none, c)

/-- The empty string's regular expression. -/
def emp : Term := .Apply (.UOp .str_to_re) (.String [])
/-- `(re.++ a b)`. -/
def cat (a b : Term) : Term := .Apply (.Apply (.UOp .re_concat) a) b
/-- `(re.* re.allchar)`, flattened. -/
def sigmaStar : Term := .Apply (.UOp .re_mult) (cat (.UOp .re_allchar) emp)

/-- Whether two terms are equal (Logos's is stuck on a stuck term). -/
def eqv (a b : Term) : M := fun c =>
  match a, b with
  | .Stuck, _ | _, .Stuck => (none, c)
  | a, b => (some (eqTerm a b), c)

/-- `x`, if `a` is not stuck. -/
@[inline] def nonStuck (a : Term) (x : M) : M :=
  match a with
  | .Stuck => fun c => (none, c)
  | _ => x

/-- The components of a concatenation. -/
def asCat : Term → Option (Term × Term)
  | .Apply (.Apply (.UOp .re_concat) a) b => some (a, b)
  | _ => none

mutual

/-- `__str_re_includes_rec`, by the cache. -/
def recF : Nat → Term → Term → M
  | 0, _, _ => fun c => (none, c)
  | n + 1, a, b => fun c =>
    match c[(⟨a, b⟩ : Pair)]? with
    | some r => (some r, c)
    | none =>
      match recBody n a b c with
      | (some r, c) => (some r, c.insert ⟨a, b⟩ r)
      | r => r

/-- The step of `__str_re_includes_rec`. -/
def recBody : Nat → Term → Term → M
  | 0, _, _ => fun c => (none, c)
  | n + 1, a, b =>
    match asCat a, asCat b with
    | some (r1, r2), some (r3, r4) =>
      if eqTerm r2 emp then
        if eqTerm r4 emp then orElse (eqv r1 r3) (baseF n r1 r3)
        else orElse (eqv r1 b) (baseF n r1 b)
      else if eqTerm r4 emp then
        orElse (orElse (eqv a r3) (baseF n a r3)) (concatF n r1 r2 r3 emp)
      else concatF n r1 r2 r3 r4
    | some (r1, r2), none =>
      if eqTerm r2 emp then orElse (eqv r1 b) (baseF n r1 b)
      else ofTerm (__str_re_includes_rec a b)
    | none, some (r3, r4) =>
      if eqTerm r4 emp then orElse (eqv a r3) (baseF n a r3) else ofTerm (__str_re_includes_rec a b)
    | none, none => ofTerm (__str_re_includes_rec a b)

/-- `__str_re_includes_concat`. -/
def concatF : Nat → Term → Term → Term → Term → M
  | 0, _, _, _, _ => fun c => (none, c)
  | n + 1, r1, r2, r3, r4 => nonStuck r1 <| nonStuck r2 <| nonStuck r3 <| nonStuck r4 <|
    orElse (andThen (orElse (eqv r1 r3) (baseF n r1 r3)) (orElse (eqv r2 r4) (recF n r2 r4)))
      (orElse (andThen (ofTerm (__re_is_unbound_wildcard (cat r1 r2)))
          (orElse (eqv (cat r1 r2) r4) (recF n (cat r1 r2) r4)))
        (andThen (eqv r1 sigmaStar) (orElse (eqv r2 (cat r3 r4)) (recF n r2 (cat r3 r4)))))

/-- `__str_re_includes_base_rec`. -/
def baseF : Nat → Term → Term → M
  | 0, _, _ => fun c => (none, c)
  | n + 1, a, b => nonStuck a <| nonStuck b <|
    match a, b with
    | a, .Apply (.UOp .str_to_re) s => ofTerm (__str_re_includes_base_rec a (.Apply (.UOp .str_to_re) s))
    | .Apply (.UOp .str_to_re) _, _ => ret false
    | .Apply (.Apply (.UOp .re_range) s1) s2, .Apply (.Apply (.UOp .re_range) s3) s4 =>
      ofTerm (__str_re_includes_base_rec (.Apply (.Apply (.UOp .re_range) s1) s2) (.Apply (.Apply (.UOp .re_range) s3) s4))
    | a, b => orElse (unionF n a b) (orElse (interF n a b) (starF n a b))

/-- `__str_re_includes_lhs_union`. -/
def unionF : Nat → Term → Term → M
  | 0, _, _ => fun c => (none, c)
  | n + 1, a, b => nonStuck a <| nonStuck b <|
    match a with
    | .Apply (.Apply (.UOp .re_union) r1) r2 => orElse (orElse (eqv r1 b) (recF n r1 b)) (unionF n r2 b)
    | _ => ret false

/-- `__str_re_includes_rhs_inter`. -/
def interF : Nat → Term → Term → M
  | 0, _, _ => fun c => (none, c)
  | n + 1, a, b => nonStuck a <| nonStuck b <|
    match b with
    | .Apply (.Apply (.UOp .re_inter) r3) r2 => orElse (orElse (eqv a r3) (recF n a r3)) (interF n a r2)
    | _ => ret false

/-- `__str_re_includes_lhs_star`. -/
def starF : Nat → Term → Term → M
  | 0, _, _ => fun c => (none, c)
  | n + 1, a, b => nonStuck a <| nonStuck b <|
    match a with
    | .Apply (.UOp .re_mult) r1 =>
      if eqTerm r1 (cat (.UOp .re_allchar) emp) then ret true else
      match b with
      | .Apply (.UOp .re_mult) r2 => orElse (eqv r1 r2) (recF n r1 r2)
      | b => orElse (eqv r1 b) (recF n r1 b)
    | _ => ret false

end

/-- The bound on the depth of the search (which a search does not reach). -/
def fuel : Nat := 1000000000

/-- Whether `a` includes `b`, for `re-inter-inclusion` and `re-union-inclusion`:
Logos's `$str_re_includes` of their flattened forms. -/
def includes (a b : Term) : Bool :=
  let fa := __re_flatten (.Boolean true) a
  let fb := __re_flatten (.Boolean true) b
  (orElse (eqv fa fb) (recF fuel fa fb) {}).1 == some true

/-- The rule, the node and the result of the inclusion of `s` in `r`. -/
def rule (inter : Bool) : CRule := if inter then .re_inter_inclusion else .re_union_inclusion

/-- `(re.inter r (re.comp s))`, or `(re.union r (re.comp s))`. -/
def node (inter : Bool) (r s : Node) : Node :=
  Node.mkNode (if inter then .REGEXP_INTER else .REGEXP_UNION) #[r, Node.mkNode .REGEXP_COMPLEMENT #[s]]

/-- `re.none`, or `(re.* re.allchar)`. -/
def result (inter : Bool) : Node :=
  if inter then Node.mkNode .REGEXP_NONE #[]
  else Node.mkNode .REGEXP_STAR #[Node.mkNode .REGEXP_ALLCHAR #[]]

/-- The side condition of a step from `n` to `m`: `r` is included in `s`, resp.
includes it. -/
def Ok (inter : Bool) (r s n m : Node) : Prop :=
  n = node inter r s ∧ m = result inter ∧ (Node.eqNode n m).smtTypeF = .Bool ∧
    (if inter then includes s.toEo r.toEo else includes r.toEo s.toEo) = true

instance (inter : Bool) (r s n m : Node) : Decidable (Ok inter r s n m) := by
  unfold Ok; infer_instance

end Telos.ReIncl
