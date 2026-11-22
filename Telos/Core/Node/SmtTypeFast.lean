import Telos.Core.Node.ToEo

/-!
# SMT types without translating to Logos

`Node.smtType t` is Logos's type of `t`'s translation: it builds the Logos term
`t.toEo`, translates it to an SMT term and types that. `Node.smtTypeF` computes
the same type on the node itself, for the common kinds, by the same rules as
Logos's `__smtx_typeof`, applied to the types of the children. On any other
node it falls back to `smtType`, for that node only.

`smtTypeF_eq` proves that the two are equal, so `smtTypeF` can replace
`smtType` in anything decided at run time. The instance `decWellTyped` below
does so for `WellTyped`, which the rewriter decides at every step.
-/

open Eo
open Smtm
open SmtEval

namespace Telos

/-- `T` is `Bool`, and then `Bool`. -/
def boolTy1 (T : SmtType) : SmtType :=
  native_ite (native_Teq T SmtType.Bool) SmtType.Bool SmtType.None

/-- `T` and `U` are `Bool`, and then `Bool` (`and`, `or`, `=>`, `xor`). -/
def boolTy2 (T U : SmtType) : SmtType :=
  native_ite (native_Teq T SmtType.Bool)
    (native_ite (native_Teq U SmtType.Bool) SmtType.Bool SmtType.None) SmtType.None

/-- The type of the nil of `+` or `*` for a first element of type `T`
(`typedNilOfType`): `0` or `1` of type `T` if it is arithmetic. -/
def arithNilTy : SmtType → SmtType
  | .Int => .Int
  | .Real => .Real
  | _ => .None

/-- The type of an application of the kind `k` to children of types `ts`, by
Logos's typing rules, for the kinds it covers. -/
def kindTy : Kind → List SmtType → Option SmtType
  | .NOT, [T] => some (boolTy1 T)
  | .IMPLIES, [T, U] | .XOR, [T, U] => some (boolTy2 T U)
  | .AND, ts@(_ :: _ :: _) | .OR, ts@(_ :: _ :: _) => some (ts.foldr boolTy2 .Bool)
  | .EQUAL, [T, U] => some (__smtx_typeof_eq T U)
  | .ITE, [C, T, U] => some (__smtx_typeof_ite C T U)
  | .ADD, ts@(T :: _ :: _) | .MULT, ts@(T :: _ :: _) =>
    some (ts.foldr __smtx_typeof_arith_overload_op_2 (arithNilTy T))
  | .SUB, [T, U] => some (__smtx_typeof_arith_overload_op_2 T U)
  | .NEG, [T] => some (__smtx_typeof_arith_overload_op_1 T)
  | .LT, [T, U] | .LEQ, [T, U] | .GT, [T, U] | .GEQ, [T, U] =>
    some (__smtx_typeof_arith_overload_op_2_ret T U .Bool)
  | .DIVISION, [T, U] => some (__smtx_typeof_arith_overload_op_2_ret T U .Real)
  | .TO_REAL, [T] => some (native_ite (native_Teq T .Int) .Real .None)
  | _, _ => none

namespace Node

/-- `smtType`, computed on the node (see the module docstring). -/
def smtTypeF (t : Node) : SmtType :=
  match t with
  | .const (.boolean _) => .Bool
  | .const (.integer _) => .Int
  | .const (.rational _) => .Real
  | .var _ .boolean => .Bool
  | .var _ .integer => .Int
  | .var _ .real => .Real
  | .app (.kind k) cs =>
    match kindTy k (cs.attach.toList.map fun ⟨c, _⟩ => c.smtTypeF) with
    | some T => T
    | none => t.smtType
  | _ => t.smtType

/-! ## `smtTypeF` is `smtType`

Logos's typing rule of each operator, as the translation writes the
application: `termTy_*` for the operators, `app_*` for the shapes of the kinds
(`Kind.eoShape`), and `kindTy_sound` for `kindTy`. -/

/-- The SMT type of a Logos term's translation. -/
def termTy (t : Term) : SmtType := __smtx_typeof (__eo_to_smt t)
theorem termTy_toEo (a : Node) : termTy a.toEo = a.smtType := rfl
theorem termTy_imp (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) = boolTy2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) = SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_xor (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) = boolTy2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) = SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_and (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) = boolTy2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) = SmtTerm.and (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_or (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) = boolTy2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) = SmtTerm.or (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_eq (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) = __smtx_typeof_eq (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) = SmtTerm.eq (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_plus (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) = __smtx_typeof_arith_overload_op_2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) a) b) = SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_mult (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) = __smtx_typeof_arith_overload_op_2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) a) b) = SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_neg (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) = __smtx_typeof_arith_overload_op_2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) = SmtTerm.neg (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_lt (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) = SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_leq (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) = SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_gt (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) = SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_geq (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b) = SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_qdiv (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) a) b) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Real := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) a) b) = SmtTerm.qdiv (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_not (a : Term) : termTy (Term.Apply (Term.UOp UserOp.not) a) = boolTy1 (termTy a) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.not) a) = SmtTerm.not (__eo_to_smt a) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_eoo_neg_2 (a : Term) : termTy (Term.Apply (Term.UOp UserOp.__eoo_neg_2) a) = __smtx_typeof_arith_overload_op_1 (termTy a) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) a) = SmtTerm.uneg (__eo_to_smt a) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_to_real (a : Term) : termTy (Term.Apply (Term.UOp UserOp.to_real) a) = native_ite (native_Teq (termTy a) .Int) .Real .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) a) = SmtTerm.to_real (__eo_to_smt a) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_ite (c a b : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b) = __smtx_typeof_ite (termTy c) (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b) = SmtTerm.ite (__eo_to_smt c) (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl
theorem termTy_true : termTy (Term.Boolean true) = .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true from rfl, __smtx_typeof.eq_def]
theorem termTy_false : termTy (Term.Boolean false) = .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false from rfl, __smtx_typeof.eq_def]
theorem termTy_nil_plus (T : SmtType) : termTy (typedNilOfType .plus T) = arithNilTy T := by
  cases T <;> simp only [typedNilOfType, arithNilTy, termTy] <;> first | rfl | (rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl, __smtx_typeof.eq_def]) | skip
theorem termTy_nil_mult (T : SmtType) : termTy (typedNilOfType .mult T) = arithNilTy T := by
  cases T <;> simp only [typedNilOfType, arithNilTy, termTy] <;> first | rfl | (rw [show __eo_to_smt Term.Stuck = SmtTerm.None from rfl, __smtx_typeof.eq_def]) | skip

theorem termTy_ra (op : UserOp) (f : SmtType → SmtType → SmtType)
    (hop : ∀ a b, termTy (eoApp2 op a b) = f (termTy a) (termTy b)) (nil : Term) :
    ∀ xs : List Term, termTy (eoRightAssocNil op nil xs) = (xs.map termTy).foldr f (termTy nil)
  | [] => rfl
  | x :: xs => by simp only [eoRightAssocNil, hop, termTy_ra op f hop nil xs, List.map, List.foldr]

theorem map_one {l : List Node} {x : SmtType} (h : l.map smtType = [x]) : ∃ a, l = [a] ∧ a.smtType = x := by
  match l, h with | [a], h => exact ⟨a, rfl, by simpa using h⟩
theorem map_two {l : List Node} {x y : SmtType} (h : l.map smtType = [x, y]) :
    ∃ a b, l = [a, b] ∧ a.smtType = x ∧ b.smtType = y := by
  match l, h with | [a, b], h => simp at h; exact ⟨a, b, rfl, h.1, h.2⟩
theorem map_three {l : List Node} {x y z : SmtType} (h : l.map smtType = [x, y, z]) :
    ∃ a b c, l = [a, b, c] ∧ a.smtType = x ∧ b.smtType = y ∧ c.smtType = z := by
  match l, h with | [a, b, c], h => simp at h; exact ⟨a, b, c, rfl, h.1, h.2.1, h.2.2⟩
theorem map_ge2 {l : List Node} {x y : SmtType} {r : List SmtType} (h : l.map smtType = x :: y :: r) :
    ∃ a b rest, l = a :: b :: rest ∧ a.smtType = x := by
  match l, h with | a :: b :: rest, h => simp at h; exact ⟨a, b, rest, rfl, h.1⟩

theorem app_NOT (a : Term) : termTy (Kind.NOT.eoShape.toEo [a]) = boolTy1 (termTy a) := by
  show termTy (Term.Apply (Term.UOp UserOp.not) a) = _; exact termTy_not a

theorem app_NEG (a : Term) : termTy (Kind.NEG.eoShape.toEo [a]) = __smtx_typeof_arith_overload_op_1 (termTy a) := by
  show termTy (Term.Apply (Term.UOp UserOp.__eoo_neg_2) a) = _; exact termTy_eoo_neg_2 a

theorem app_TO_REAL (a : Term) : termTy (Kind.TO_REAL.eoShape.toEo [a]) = native_ite (native_Teq (termTy a) .Int) .Real .None := by
  show termTy (Term.Apply (Term.UOp UserOp.to_real) a) = _; exact termTy_to_real a

theorem app_IMPLIES (a b : Term) : termTy (Kind.IMPLIES.eoShape.toEo [a, b]) = boolTy2 (termTy a) (termTy b) := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) = _; exact termTy_imp a b

theorem app_XOR (a b : Term) : termTy (Kind.XOR.eoShape.toEo [a, b]) = boolTy2 (termTy a) (termTy b) := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) = _; exact termTy_xor a b

theorem app_EQUAL (a b : Term) : termTy (Kind.EQUAL.eoShape.toEo [a, b]) = __smtx_typeof_eq (termTy a) (termTy b) := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) = _; exact termTy_eq a b

theorem app_SUB (a b : Term) : termTy (Kind.SUB.eoShape.toEo [a, b]) = __smtx_typeof_arith_overload_op_2 (termTy a) (termTy b) := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.neg) a) b) = _; exact termTy_neg a b

theorem app_LT (a b : Term) : termTy (Kind.LT.eoShape.toEo [a, b]) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Bool := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b) = _; exact termTy_lt a b

theorem app_LEQ (a b : Term) : termTy (Kind.LEQ.eoShape.toEo [a, b]) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Bool := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b) = _; exact termTy_leq a b

theorem app_GT (a b : Term) : termTy (Kind.GT.eoShape.toEo [a, b]) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Bool := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b) = _; exact termTy_gt a b

theorem app_GEQ (a b : Term) : termTy (Kind.GEQ.eoShape.toEo [a, b]) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Bool := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b) = _; exact termTy_geq a b

theorem app_DIVISION (a b : Term) : termTy (Kind.DIVISION.eoShape.toEo [a, b]) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Real := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) a) b) = _; exact termTy_qdiv a b

theorem app_ITE (c a b : Term) : termTy (Kind.ITE.eoShape.toEo [c, a, b]) = __smtx_typeof_ite (termTy c) (termTy a) (termTy b) := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) a) b) = _; exact termTy_ite c a b

theorem app_AND (a b : Term) (r : List Term) : termTy (Kind.AND.eoShape.toEo (a :: b :: r)) = ((a :: b :: r).map termTy).foldr boolTy2 .Bool := by
  show termTy (eoRightAssocNil .and (Term.Boolean true) (a :: b :: r)) = _
  rw [termTy_ra .and boolTy2 termTy_and, termTy_true]
theorem app_OR (a b : Term) (r : List Term) : termTy (Kind.OR.eoShape.toEo (a :: b :: r)) = ((a :: b :: r).map termTy).foldr boolTy2 .Bool := by
  show termTy (eoRightAssocNil .or (Term.Boolean false) (a :: b :: r)) = _
  rw [termTy_ra .or boolTy2 termTy_or, termTy_false]
theorem app_ADD (a b : Term) (r : List Term) : termTy (Kind.ADD.eoShape.toEo (a :: b :: r)) =
    ((a :: b :: r).map termTy).foldr __smtx_typeof_arith_overload_op_2 (arithNilTy (termTy a)) := by
  show termTy (eoRightAssocNil .plus (typedNilOfType .plus (termTy a)) (a :: b :: r)) = _
  rw [termTy_ra .plus _ termTy_plus, termTy_nil_plus]
theorem app_MULT (a b : Term) (r : List Term) : termTy (Kind.MULT.eoShape.toEo (a :: b :: r)) =
    ((a :: b :: r).map termTy).foldr __smtx_typeof_arith_overload_op_2 (arithNilTy (termTy a)) := by
  show termTy (eoRightAssocNil .mult (typedNilOfType .mult (termTy a)) (a :: b :: r)) = _
  rw [termTy_ra .mult _ termTy_mult, termTy_nil_mult]

theorem map_toEo_ty (l : List Node) : (l.map toEo).map termTy = l.map smtType := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map, termTy_toEo, ih]

theorem kindTy_sound {k : Kind} {l : List Node} {T : SmtType} (h : kindTy k (l.map smtType) = some T) :
    termTy (k.eoShape.toEo (l.map toEo)) = T := by
  unfold kindTy at h
  split at h
  all_goals first
    | (rename_i heq
       obtain ⟨a, rfl, rfl⟩ := map_one heq
       obtain rfl := Option.some.inj h
       first | exact app_NOT _ | exact app_NEG _ | exact app_TO_REAL _)
    | (rename_i heq
       obtain ⟨a, b, rfl, rfl, rfl⟩ := map_two heq
       obtain rfl := Option.some.inj h
       first | exact app_IMPLIES _ _ | exact app_XOR _ _ | exact app_EQUAL _ _ | exact app_SUB _ _ | exact app_LT _ _ | exact app_LEQ _ _ | exact app_GT _ _ | exact app_GEQ _ _ | exact app_DIVISION _ _)
    | (rename_i heq
       obtain ⟨a, b, c, rfl, rfl, rfl, rfl⟩ := map_three heq
       obtain rfl := Option.some.inj h
       exact app_ITE _ _ _)
    | (rename_i heq
       obtain ⟨a, b, rest, rfl, rfl⟩ := map_ge2 heq
       obtain rfl := Option.some.inj h
       rw [← heq]
       first
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_AND, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_OR, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_ADD, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_MULT, ← map_toEo_ty]; rfl))
    | cases h

theorem smtType_bool (b : Bool) : (Node.const (.boolean b)).smtType = .Bool := by
  simp only [smtType, toSmt, toEo, Const.toEo]
  rw [show __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b from rfl, __smtx_typeof.eq_def]
theorem smtType_int (n : Int) : (Node.const (.integer n)).smtType = .Int := by
  simp only [smtType, toSmt, toEo, Const.toEo]
  rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n from rfl, __smtx_typeof.eq_def]
theorem smtType_rat (q : Rat) : (Node.const (.rational q)).smtType = .Real := by
  simp only [smtType, toSmt, toEo, Const.toEo]
  rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q from rfl, __smtx_typeof.eq_def]
theorem smtType_var_integer (x : String) : (Node.var x .integer).smtType = .Int := by
  simp only [smtType, toSmt, toEo, TypeNode.toEo]
  rw [show __eo_to_smt (Term.UConst (constId x) (Term.UOp UserOp.Int)) = SmtTerm.UConst (native_uconst_id (constId x)) SmtType.Int from rfl, __smtx_typeof.eq_def]
  simp only
  rw [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_component, __smtx_inhabited_type, __smtx_type_wf_rec] <;> first | rfl | (intros; contradiction) | simp
theorem smtType_var_boolean (x : String) : (Node.var x .boolean).smtType = .Bool := by
  simp only [smtType, toSmt, toEo, TypeNode.toEo]
  rw [show __eo_to_smt (Term.UConst (constId x) (Term.Bool)) = SmtTerm.UConst (native_uconst_id (constId x)) SmtType.Bool from rfl, __smtx_typeof.eq_def]
  simp only
  rw [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_component, __smtx_inhabited_type, __smtx_type_wf_rec] <;> first | rfl | (intros; contradiction) | simp
theorem smtType_var_real (x : String) : (Node.var x .real).smtType = .Real := by
  simp only [smtType, toSmt, toEo, TypeNode.toEo]
  rw [show __eo_to_smt (Term.UConst (constId x) (Term.UOp UserOp.Real)) = SmtTerm.UConst (native_uconst_id (constId x)) SmtType.Real from rfl, __smtx_typeof.eq_def]
  simp only
  rw [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_component, __smtx_inhabited_type, __smtx_type_wf_rec] <;> first | rfl | (intros; contradiction) | simp

theorem smtTypeF_eq (t : Node) : t.smtTypeF = t.smtType := by
  match t with
  | .const (.boolean b) => rw [smtType_bool, smtTypeF]
  | .const (.integer n) => rw [smtType_int, smtTypeF]
  | .const (.rational q) => rw [smtType_rat, smtTypeF]
  | .const (.bitVector _ _) | .const (.string _) | .const (.emptySet _) | .const (.dtCons _ _)
  | .const (.dtSel _ _ _) => rw [smtTypeF] <;> (intros; simp_all)
  | .var x T =>
    cases T
    case boolean => rw [smtType_var_boolean, smtTypeF]
    case integer => rw [smtType_var_integer, smtTypeF]
    case real => rw [smtType_var_real, smtTypeF]
    all_goals (rw [smtTypeF] <;> (intros; simp_all))
  | .boundVar _ _ | .skolem _ _ | .app (.indexed _ _) _ | .app (.node _ _) _ => rw [smtTypeF] <;> (intros; simp_all)
  | .app (.kind k) cs =>
    have ih : cs.attach.toList.map (fun ⟨c, _⟩ => c.smtTypeF) = cs.toList.map smtType := by
      have hc : ∀ c ∈ cs, c.smtTypeF = c.smtType := fun c _ => smtTypeF_eq c
      have key : ∀ (l : List Node) (H : ∀ x ∈ l, x ∈ cs),
          (l.attachWith (· ∈ cs) H).map (fun ⟨c, _⟩ => c.smtTypeF) = l.map smtType := by
        intro l
        induction l with
        | nil => intro; rfl
        | cons a l ih =>
          intro H
          simp only [List.attachWith_cons, List.map_cons]
          rw [hc a (H a (by simp)), ih]
      rw [Array.toList_attach]
      exact key _ _
    rw [smtTypeF]
    rw [ih]
    split
    · rename_i T hT
      show _ = termTy (Node.app (.kind k) cs).toEo
      rw [toEo_app]
      exact (kindTy_sound hT).symm
    · rfl

/-- The type of an equation, from the types of its sides. -/
theorem typeof_eqFormula (a b : Node) :
    __smtx_typeof (__eo_to_smt (eqFormula a b)) = __smtx_typeof_eq a.smtType b.smtType :=
  termTy_eq a.toEo b.toEo

/-- `WellTyped`, decided by `smtTypeF` (`smtTypeF_eq`): no translation to Logos
for the kinds `kindTy` covers. -/
instance (priority := high) decWellTyped (t : Node) : Decidable t.WellTyped :=
  decidable_of_iff (t.smtTypeF ≠ SmtType.None) (by rw [smtTypeF_eq]; rfl)

/-- `getType`, by `smtTypeF`. -/
def getTypeF (t : Node) : Option TypeNode := TypeNode.ofSmt t.smtTypeF

theorem getTypeF_eq (t : Node) : t.getTypeF = t.getType := by
  rw [getTypeF, smtTypeF_eq]; rfl

end Node

end Telos
