import Telos.Core.Node.ToEo
import Telos.Core.Node.KindTy
import Telos.Core.Node.TermTyDefs

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

namespace Node

/-- `smtType` computed on the node, for the nodes that `fastTy` does not cover
(see the module docstring): the children by their kept types when they have
them. -/
def smtTypeR (t : Node) : SmtType :=
  match t with
  | .const (.boolean _) => .Bool
  | .const (.integer _) => .Int
  | .const (.rational _) => .Real
  | .var _ .boolean => .Bool
  | .var _ .integer => .Int
  | .var _ .real => .Real
  | .app (.kind k) cs =>
    match kindTy k (cs.attach.toList.map fun ⟨c, _⟩ => c.fastTy.getD c.smtTypeR) with
    | some T => T
    | none => termTyF t.toEo
  | _ => termTyF t.toEo

/-- `smtType`, computed on the node: its kept type (`fastTy`), else `smtTypeR`. -/
def smtTypeF (t : Node) : SmtType := t.fastTy.getD t.smtTypeR

/-! ## `smtTypeF` is `smtType`

Logos's typing rule of each operator, as the translation writes the
application: `termTy_*` for the operators, `app_*` for the shapes of the kinds
(`Kind.eoShape`), and `kindTy_sound` for `kindTy`. -/

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
theorem termTy_str_len (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_len) a) = __smtx_typeof_seq_op_1_ret (termTy a) .Int := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) a) = SmtTerm.str_len (__eo_to_smt a) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_str_substr (a b c : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) a) b) c) = __smtx_typeof_str_substr (termTy a) (termTy b) (termTy c) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) a) b) c) = SmtTerm.str_substr (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_str_concat (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) = __smtx_typeof_seq_op_2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) b) = SmtTerm.str_concat (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem termTy_string (w : native_String) : termTy (Term.String w) = native_ite (native_string_valid w) (.Seq .Char) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.String w) = SmtTerm.String w from rfl, __smtx_typeof.eq_def]

theorem termTy_purify (a : Term) : termTy (Term.Apply (Term.UOp UserOp._at_purify) a) = termTy a := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp._at_purify) a) = SmtTerm._at_purify (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem termTy_nil_str_concat : termTy (typedNilOfType .str_concat (.Seq .Char)) = .Seq .Char := by
  simp only [typedNilOfType]; rw [termTy_string]; rfl

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


theorem typeof_none : __smtx_typeof SmtTerm.None = .None := by
  rw [__smtx_typeof.eq_def]

theorem typeof_split (a b c : SmtTerm) : __smtx_typeof (SmtTerm.str_indexof_re_split a b c) =
    splitTy (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c) := by
  rw [__smtx_typeof.eq_def]; rfl

theorem typeof_substr (a b c : SmtTerm) : __smtx_typeof (SmtTerm.str_substr a b c) =
    __smtx_typeof_str_substr (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_neg (a b : SmtTerm) : __smtx_typeof (SmtTerm.neg a b) =
    __smtx_typeof_arith_overload_op_2 (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_len (a : SmtTerm) : __smtx_typeof (SmtTerm.str_len a) =
    __smtx_typeof_seq_op_1_ret (__smtx_typeof a) .Int := by
  rw [__smtx_typeof.eq_def]

theorem typeof_numeral (i : native_Int) : __smtx_typeof (SmtTerm.Numeral i) = .Int := by
  rw [__smtx_typeof.eq_def]

theorem compTy_eq : ∀ (n : Nat) (S R : SmtTerm),
    __smtx_typeof (__eo_to_smt_re_unfold_pos_component S R n) = compTy (__smtx_typeof S) R n := by
  intro n
  induction n with
  | zero =>
    intro S R
    cases R <;> simp only [__eo_to_smt_re_unfold_pos_component, compTy, typeof_none, typeof_substr,
      typeof_split, typeof_numeral]
  | succ n ih =>
    intro S R
    cases R <;> simp only [__eo_to_smt_re_unfold_pos_component, compTy, typeof_none, ih, typeof_substr,
      typeof_split, typeof_neg, typeof_len]

theorem termTy_comp (x₁ x₂ x₃ : Term) :
    termTy (Term.UOp3 UserOp3._at_re_unfold_pos_component x₁ x₂ x₃) =
      native_ite (__eo_to_smt_nat_is_valid x₃) (compTy (termTy x₁) (__eo_to_smt x₂) (__eo_to_smt_nat x₃)) .None := by
  unfold termTy
  rw [show __eo_to_smt (Term.UOp3 UserOp3._at_re_unfold_pos_component x₁ x₂ x₃) =
    native_ite (__eo_to_smt_nat_is_valid x₃)
      (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x₁) (__eo_to_smt x₂) (__eo_to_smt_nat x₃)) SmtTerm.None
    from rfl]
  cases __eo_to_smt_nat_is_valid x₃ <;> simp [native_ite, compTy_eq, typeof_none]

theorem termTy_str_in_re (a b : Term) :
    termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) a) b) =
      native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) .RegLan) .Bool .None) .None := by
  unfold termTy
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) a) b) =
    SmtTerm.str_in_re (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_to_code (a : Term) :
    termTy (Term.Apply (Term.UOp UserOp.str_to_code) a) =
      native_ite (native_Teq (termTy a) (.Seq .Char)) .Int .None := by
  unfold termTy
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_code) a) =
    SmtTerm.str_to_code (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_contains (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) a) b) =
    __smtx_typeof_seq_op_2_ret (termTy a) (termTy b) .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) a) b) = (SmtTerm.str_contains (__eo_to_smt a) (__eo_to_smt b)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_prefixof (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) a) b) =
    __smtx_typeof_seq_op_2_ret (termTy a) (termTy b) .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) a) b) = (SmtTerm.str_prefixof (__eo_to_smt a) (__eo_to_smt b)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_suffixof (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) a) b) =
    __smtx_typeof_seq_op_2_ret (termTy a) (termTy b) .Bool := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) a) b) = (SmtTerm.str_suffixof (__eo_to_smt a) (__eo_to_smt b)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_at (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) a) b) =
    __smtx_typeof_str_at (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) a) b) = (SmtTerm.str_at (__eo_to_smt a) (__eo_to_smt b)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_indexof (a b c : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) a) b) c) =
    __smtx_typeof_str_indexof (termTy a) (termTy b) (termTy c) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) a) b) c) = (SmtTerm.str_indexof (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_replace (a b c : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) a) b) c) =
    __smtx_typeof_seq_op_3 (termTy a) (termTy b) (termTy c) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) a) b) c) = (SmtTerm.str_replace (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_replace_all (a b c : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) a) b) c) =
    __smtx_typeof_seq_op_3 (termTy a) (termTy b) (termTy c) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) a) b) c) = (SmtTerm.str_replace_all (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_to_re (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_to_re) a) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) .RegLan .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) a) = (SmtTerm.str_to_re (__eo_to_smt a)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_to_int (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_to_int) a) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) .Int .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) a) = (SmtTerm.str_to_int (__eo_to_smt a)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_from_int (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_from_int) a) =
    native_ite (native_Teq (termTy a) .Int) (.Seq .Char) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_int) a) = (SmtTerm.str_from_int (__eo_to_smt a)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_from_code (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_from_code) a) =
    native_ite (native_Teq (termTy a) .Int) (.Seq .Char) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_from_code) a) = (SmtTerm.str_from_code (__eo_to_smt a)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_is_digit (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_is_digit) a) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) .Bool .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_is_digit) a) = (SmtTerm.str_is_digit (__eo_to_smt a)) from rfl, __smtx_typeof.eq_def]

theorem termTy_str_rev (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_rev) a) =
    __smtx_typeof_seq_op_1 (termTy a) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_rev) a) = (SmtTerm.str_rev (__eo_to_smt a)) from rfl, __smtx_typeof.eq_def]

theorem termTyF_eq (t : Term) : termTyF t = termTy t := by
  fun_induction termTyF t <;>
    simp_all only [termTy_comp, termTy_str_in_re, termTy_str_to_code, termTy_eq, termTy_and,
      termTy_or, termTy_not, termTy_str_concat, termTy_str_len, termTy_purify,
      termTy_plus, termTy_geq, termTy_ite, termTy_mult, termTy_neg, termTy_eoo_neg_2, termTy_lt, termTy_leq, termTy_gt,
      termTy_to_real, termTy_imp, termTy_xor, termTy_str_substr, termTy_str_contains, termTy_str_prefixof, termTy_str_suffixof, termTy_str_at, termTy_str_indexof, termTy_str_replace, termTy_str_replace_all, termTy_str_to_re, termTy_str_to_int, termTy_str_from_int, termTy_str_from_code, termTy_str_is_digit, termTy_str_rev]

theorem typedNil_eq (op : UserOp) (x : Term) : typedNil op x = typedNilOfType op (termTy x) := rfl


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
  show termTy (eoRightAssocNil .plus (typedNil .plus a) (a :: b :: r)) = _
  rw [typedNil_eq]
  rw [termTy_ra .plus _ termTy_plus, termTy_nil_plus]
theorem app_MULT (a b : Term) (r : List Term) : termTy (Kind.MULT.eoShape.toEo (a :: b :: r)) =
    ((a :: b :: r).map termTy).foldr __smtx_typeof_arith_overload_op_2 (arithNilTy (termTy a)) := by
  show termTy (eoRightAssocNil .mult (typedNil .mult a) (a :: b :: r)) = _
  rw [typedNil_eq]
  rw [termTy_ra .mult _ termTy_mult, termTy_nil_mult]

theorem app_STRING_LENGTH (a : Term) : termTy (Kind.STRING_LENGTH.eoShape.toEo [a]) = __smtx_typeof_seq_op_1_ret (termTy a) .Int := by
  show termTy (Term.Apply (Term.UOp UserOp.str_len) a) = _; exact termTy_str_len a

theorem app_STRING_SUBSTR (a b c : Term) : termTy (Kind.STRING_SUBSTR.eoShape.toEo [a, b, c]) = __smtx_typeof_str_substr (termTy a) (termTy b) (termTy c) := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) a) b) c) = _; exact termTy_str_substr a b c

theorem app_STRING_CONCAT (a b : Term) (r : List Term) (h : termTy a = .Seq .Char) :
    termTy (Kind.STRING_CONCAT.eoShape.toEo (a :: b :: r)) =
      ((a :: b :: r).map termTy).foldr __smtx_typeof_seq_op_2 (.Seq .Char) := by
  show termTy (eoRightAssocNil .str_concat (typedNil .str_concat a) (a :: b :: r)) = _
  rw [typedNil_eq]
  rw [termTy_ra .str_concat _ termTy_str_concat, h, termTy_nil_str_concat]

theorem map_toEo_ty (l : List Node) : (l.map toEo).map termTy = l.map smtType := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map, termTy_toEo, ih]

theorem termTy_abs (a : Term) : termTy (Term.Apply (Term.UOp UserOp.abs) a) =
    __smtx_typeof_arith_overload_op_1 (termTy a) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.abs) a) = SmtTerm.abs (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_ABS (a : Term) : termTy (Kind.ABS.eoShape.toEo [a]) =
    __smtx_typeof_arith_overload_op_1 (termTy a) := by
  show termTy (Term.Apply (Term.UOp UserOp.abs) a) = _; exact termTy_abs a

theorem termTy_to_int (a : Term) : termTy (Term.Apply (Term.UOp UserOp.to_int) a) =
    native_ite (native_Teq (termTy a) .Real) .Int .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.to_int) a) = SmtTerm.to_int (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_TO_INTEGER (a : Term) : termTy (Kind.TO_INTEGER.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) .Real) .Int .None := by
  show termTy (Term.Apply (Term.UOp UserOp.to_int) a) = _; exact termTy_to_int a

theorem termTy_is_int (a : Term) : termTy (Term.Apply (Term.UOp UserOp.is_int) a) =
    native_ite (native_Teq (termTy a) .Real) .Bool .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.is_int) a) = SmtTerm.is_int (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_IS_INTEGER (a : Term) : termTy (Kind.IS_INTEGER.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) .Real) .Bool .None := by
  show termTy (Term.Apply (Term.UOp UserOp.is_int) a) = _; exact termTy_is_int a

theorem termTy_div (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Int .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) = SmtTerm.div (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_INTS_DIVISION (a b : Term) : termTy (Kind.INTS_DIVISION.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Int .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b) = _; exact termTy_div a b

theorem termTy_mod (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Int .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) = SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_INTS_MODULUS (a b : Term) : termTy (Kind.INTS_MODULUS.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Int .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b) = _; exact termTy_mod a b

theorem termTy_div_total (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Int .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) = SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_INTS_DIVISION_TOTAL (a b : Term) : termTy (Kind.INTS_DIVISION_TOTAL.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Int .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b) = _; exact termTy_div_total a b

theorem termTy_mod_total (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Int .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) = SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_INTS_MODULUS_TOTAL (a b : Term) : termTy (Kind.INTS_MODULUS_TOTAL.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Int .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b) = _; exact termTy_mod_total a b

theorem termTy_divisible (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) a) b) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Bool .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) a) b) = SmtTerm.divisible (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_DIVISIBLE (a b : Term) : termTy (Kind.DIVISIBLE.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) .Int) (native_ite (native_Teq (termTy b) .Int) .Bool .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) a) b) = _; exact termTy_divisible a b

theorem termTy_str_update (a b c : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) a) b) c) =
    __smtx_typeof_str_update (termTy a) (termTy b) (termTy c) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) a) b) c) = SmtTerm.str_update (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c) from rfl, __smtx_typeof.eq_def]

theorem app_STRING_UPDATE (a b c : Term) : termTy (Kind.STRING_UPDATE.eoShape.toEo [a, b, c]) =
    __smtx_typeof_str_update (termTy a) (termTy b) (termTy c) := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) a) b) c) = _; exact termTy_str_update a b c

theorem app_STRING_CHARAT (a b : Term) : termTy (Kind.STRING_CHARAT.eoShape.toEo [a, b]) =
    __smtx_typeof_str_at (termTy a) (termTy b) := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) a) b) = _; exact termTy_str_at a b

theorem app_STRING_CONTAINS (a b : Term) : termTy (Kind.STRING_CONTAINS.eoShape.toEo [a, b]) =
    __smtx_typeof_seq_op_2_ret (termTy a) (termTy b) .Bool := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) a) b) = _; exact termTy_str_contains a b

theorem app_STRING_PREFIX (a b : Term) : termTy (Kind.STRING_PREFIX.eoShape.toEo [a, b]) =
    __smtx_typeof_seq_op_2_ret (termTy a) (termTy b) .Bool := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) a) b) = _; exact termTy_str_prefixof a b

theorem app_STRING_SUFFIX (a b : Term) : termTy (Kind.STRING_SUFFIX.eoShape.toEo [a, b]) =
    __smtx_typeof_seq_op_2_ret (termTy a) (termTy b) .Bool := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) a) b) = _; exact termTy_str_suffixof a b

theorem termTy_str_lt (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) a) b) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) (.Seq .Char)) .Bool .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) a) b) = SmtTerm.str_lt (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_STRING_LT (a b : Term) : termTy (Kind.STRING_LT.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) (.Seq .Char)) .Bool .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) a) b) = _; exact termTy_str_lt a b

theorem termTy_str_leq (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) a) b) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) (.Seq .Char)) .Bool .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) a) b) = SmtTerm.str_leq (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_STRING_LEQ (a b : Term) : termTy (Kind.STRING_LEQ.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) (.Seq .Char)) .Bool .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) a) b) = _; exact termTy_str_leq a b

theorem app_STRING_INDEXOF (a b c : Term) : termTy (Kind.STRING_INDEXOF.eoShape.toEo [a, b, c]) =
    __smtx_typeof_str_indexof (termTy a) (termTy b) (termTy c) := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) a) b) c) = _; exact termTy_str_indexof a b c

theorem termTy_str_indexof_re (a b c : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) a) b) c) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) .RegLan) (native_ite (native_Teq (termTy c) .Int) .Int .None) .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) a) b) c) = SmtTerm.str_indexof_re (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c) from rfl, __smtx_typeof.eq_def]

theorem app_STRING_INDEXOF_RE (a b c : Term) : termTy (Kind.STRING_INDEXOF_RE.eoShape.toEo [a, b, c]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) .RegLan) (native_ite (native_Teq (termTy c) .Int) .Int .None) .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) a) b) c) = _; exact termTy_str_indexof_re a b c

theorem app_STRING_REPLACE (a b c : Term) : termTy (Kind.STRING_REPLACE.eoShape.toEo [a, b, c]) =
    __smtx_typeof_seq_op_3 (termTy a) (termTy b) (termTy c) := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) a) b) c) = _; exact termTy_str_replace a b c

theorem app_STRING_REPLACE_ALL (a b c : Term) : termTy (Kind.STRING_REPLACE_ALL.eoShape.toEo [a, b, c]) =
    __smtx_typeof_seq_op_3 (termTy a) (termTy b) (termTy c) := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) a) b) c) = _; exact termTy_str_replace_all a b c

theorem termTy_str_replace_re (a b c : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) a) b) c) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) .RegLan) (native_ite (native_Teq (termTy c) (.Seq .Char)) ((.Seq .Char)) .None) .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) a) b) c) = SmtTerm.str_replace_re (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c) from rfl, __smtx_typeof.eq_def]

theorem app_STRING_REPLACE_RE (a b c : Term) : termTy (Kind.STRING_REPLACE_RE.eoShape.toEo [a, b, c]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) .RegLan) (native_ite (native_Teq (termTy c) (.Seq .Char)) ((.Seq .Char)) .None) .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) a) b) c) = _; exact termTy_str_replace_re a b c

theorem termTy_str_replace_re_all (a b c : Term) : termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) a) b) c) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) .RegLan) (native_ite (native_Teq (termTy c) (.Seq .Char)) ((.Seq .Char)) .None) .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) a) b) c) = SmtTerm.str_replace_re_all (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c) from rfl, __smtx_typeof.eq_def]

theorem app_STRING_REPLACE_RE_ALL (a b c : Term) : termTy (Kind.STRING_REPLACE_RE_ALL.eoShape.toEo [a, b, c]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) .RegLan) (native_ite (native_Teq (termTy c) (.Seq .Char)) ((.Seq .Char)) .None) .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) a) b) c) = _; exact termTy_str_replace_re_all a b c

theorem app_STRING_IS_DIGIT (a : Term) : termTy (Kind.STRING_IS_DIGIT.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) .Bool .None := by
  show termTy (Term.Apply (Term.UOp UserOp.str_is_digit) a) = _; exact termTy_str_is_digit a

theorem app_STRING_ITOS (a : Term) : termTy (Kind.STRING_ITOS.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) .Int) ((.Seq .Char)) .None := by
  show termTy (Term.Apply (Term.UOp UserOp.str_from_int) a) = _; exact termTy_str_from_int a

theorem app_STRING_STOI (a : Term) : termTy (Kind.STRING_STOI.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) .Int .None := by
  show termTy (Term.Apply (Term.UOp UserOp.str_to_int) a) = _; exact termTy_str_to_int a

theorem app_STRING_TO_CODE (a : Term) : termTy (Kind.STRING_TO_CODE.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) .Int .None := by
  show termTy (Term.Apply (Term.UOp UserOp.str_to_code) a) = _; exact termTy_str_to_code a

theorem app_STRING_FROM_CODE (a : Term) : termTy (Kind.STRING_FROM_CODE.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) .Int) ((.Seq .Char)) .None := by
  show termTy (Term.Apply (Term.UOp UserOp.str_from_code) a) = _; exact termTy_str_from_code a

theorem termTy_str_to_lower (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_to_lower) a) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) ((.Seq .Char)) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_lower) a) = SmtTerm.str_to_lower (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_STRING_TO_LOWER (a : Term) : termTy (Kind.STRING_TO_LOWER.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) ((.Seq .Char)) .None := by
  show termTy (Term.Apply (Term.UOp UserOp.str_to_lower) a) = _; exact termTy_str_to_lower a

theorem termTy_str_to_upper (a : Term) : termTy (Term.Apply (Term.UOp UserOp.str_to_upper) a) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) ((.Seq .Char)) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_upper) a) = SmtTerm.str_to_upper (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_STRING_TO_UPPER (a : Term) : termTy (Kind.STRING_TO_UPPER.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) ((.Seq .Char)) .None := by
  show termTy (Term.Apply (Term.UOp UserOp.str_to_upper) a) = _; exact termTy_str_to_upper a

theorem app_STRING_REV (a : Term) : termTy (Kind.STRING_REV.eoShape.toEo [a]) =
    __smtx_typeof_seq_op_1 (termTy a) := by
  show termTy (Term.Apply (Term.UOp UserOp.str_rev) a) = _; exact termTy_str_rev a

theorem app_STRING_TO_REGEXP (a : Term) : termTy (Kind.STRING_TO_REGEXP.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) .RegLan .None := by
  show termTy (Term.Apply (Term.UOp UserOp.str_to_re) a) = _; exact termTy_str_to_re a

theorem app_STRING_IN_REGEXP (a b : Term) : termTy (Kind.STRING_IN_REGEXP.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) .RegLan) .Bool .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) a) b) = _; exact termTy_str_in_re a b

theorem termTy_re_none : termTy (Term.UOp UserOp.re_none) =
    .RegLan := by
  unfold termTy; rw [show __eo_to_smt (Term.UOp UserOp.re_none) = SmtTerm.re_none from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_NONE : termTy (Kind.REGEXP_NONE.eoShape.toEo []) =
    .RegLan := by
  show termTy (Term.UOp UserOp.re_none) = _; exact termTy_re_none

theorem termTy_re_all : termTy (Term.UOp UserOp.re_all) =
    .RegLan := by
  unfold termTy; rw [show __eo_to_smt (Term.UOp UserOp.re_all) = SmtTerm.re_all from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_ALL : termTy (Kind.REGEXP_ALL.eoShape.toEo []) =
    .RegLan := by
  show termTy (Term.UOp UserOp.re_all) = _; exact termTy_re_all

theorem termTy_re_allchar : termTy (Term.UOp UserOp.re_allchar) =
    .RegLan := by
  unfold termTy; rw [show __eo_to_smt (Term.UOp UserOp.re_allchar) = SmtTerm.re_allchar from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_ALLCHAR : termTy (Kind.REGEXP_ALLCHAR.eoShape.toEo []) =
    .RegLan := by
  show termTy (Term.UOp UserOp.re_allchar) = _; exact termTy_re_allchar

theorem termTy_re_diff (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) a) b) =
    native_ite (native_Teq (termTy a) .RegLan) (native_ite (native_Teq (termTy b) .RegLan) .RegLan .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) a) b) = SmtTerm.re_diff (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_DIFF (a b : Term) : termTy (Kind.REGEXP_DIFF.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) .RegLan) (native_ite (native_Teq (termTy b) .RegLan) .RegLan .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) a) b) = _; exact termTy_re_diff a b

theorem termTy_re_mult (a : Term) : termTy (Term.Apply (Term.UOp UserOp.re_mult) a) =
    native_ite (native_Teq (termTy a) .RegLan) .RegLan .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) a) = SmtTerm.re_mult (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_STAR (a : Term) : termTy (Kind.REGEXP_STAR.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) .RegLan) .RegLan .None := by
  show termTy (Term.Apply (Term.UOp UserOp.re_mult) a) = _; exact termTy_re_mult a

theorem termTy_re_plus (a : Term) : termTy (Term.Apply (Term.UOp UserOp.re_plus) a) =
    native_ite (native_Teq (termTy a) .RegLan) .RegLan .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.re_plus) a) = SmtTerm.re_plus (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_PLUS (a : Term) : termTy (Kind.REGEXP_PLUS.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) .RegLan) .RegLan .None := by
  show termTy (Term.Apply (Term.UOp UserOp.re_plus) a) = _; exact termTy_re_plus a

theorem termTy_re_opt (a : Term) : termTy (Term.Apply (Term.UOp UserOp.re_opt) a) =
    native_ite (native_Teq (termTy a) .RegLan) .RegLan .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.re_opt) a) = SmtTerm.re_opt (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_OPT (a : Term) : termTy (Kind.REGEXP_OPT.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) .RegLan) .RegLan .None := by
  show termTy (Term.Apply (Term.UOp UserOp.re_opt) a) = _; exact termTy_re_opt a

theorem termTy_re_range (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) a) b) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) (.Seq .Char)) .RegLan .None) .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) a) b) = SmtTerm.re_range (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_RANGE (a b : Term) : termTy (Kind.REGEXP_RANGE.eoShape.toEo [a, b]) =
    native_ite (native_Teq (termTy a) (.Seq .Char)) (native_ite (native_Teq (termTy b) (.Seq .Char)) .RegLan .None) .None := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) a) b) = _; exact termTy_re_range a b

theorem termTy_re_comp (a : Term) : termTy (Term.Apply (Term.UOp UserOp.re_comp) a) =
    native_ite (native_Teq (termTy a) .RegLan) .RegLan .None := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.re_comp) a) = SmtTerm.re_comp (__eo_to_smt a) from rfl, __smtx_typeof.eq_def]

theorem app_REGEXP_COMPLEMENT (a : Term) : termTy (Kind.REGEXP_COMPLEMENT.eoShape.toEo [a]) =
    native_ite (native_Teq (termTy a) .RegLan) .RegLan .None := by
  show termTy (Term.Apply (Term.UOp UserOp.re_comp) a) = _; exact termTy_re_comp a

theorem termTy_re_concat (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) = reTy2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b) = SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]; rfl

theorem app_REGEXP_CONCAT (a b : Term) (r : List Term) : termTy (Kind.REGEXP_CONCAT.eoShape.toEo (a :: b :: r)) =
    ((a :: b :: r).map termTy).foldr reTy2 .RegLan := by
  show termTy (eoRightAssocNil .re_concat (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) (a :: b :: r)) = _
  rw [termTy_ra .re_concat reTy2 termTy_re_concat, show termTy (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) = SmtType.RegLan by rw [termTy_str_to_re, termTy_string]; rfl]

theorem termTy_re_inter (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b) = reTy2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b) = SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]; rfl

theorem app_REGEXP_INTER (a b : Term) (r : List Term) : termTy (Kind.REGEXP_INTER.eoShape.toEo (a :: b :: r)) =
    ((a :: b :: r).map termTy).foldr reTy2 .RegLan := by
  show termTy (eoRightAssocNil .re_inter (Term.UOp UserOp.re_all) (a :: b :: r)) = _
  rw [termTy_ra .re_inter reTy2 termTy_re_inter, termTy_re_all]

theorem termTy_re_union (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b) = reTy2 (termTy a) (termTy b) := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b) = SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def]; rfl

theorem app_REGEXP_UNION (a b : Term) (r : List Term) : termTy (Kind.REGEXP_UNION.eoShape.toEo (a :: b :: r)) =
    ((a :: b :: r).map termTy).foldr reTy2 .RegLan := by
  show termTy (eoRightAssocNil .re_union (Term.UOp UserOp.re_none) (a :: b :: r)) = _
  rw [termTy_ra .re_union reTy2 termTy_re_union, termTy_re_none]

theorem map_zero {l : List Node} (h : l.map smtType = []) : l = [] := by simpa using h

set_option maxHeartbeats 2000000 in
theorem kindTy_sound {k : Kind} {l : List Node} {T : SmtType} (h : kindTy k (l.map smtType) = some T) :
    termTy (k.eoShape.toEo (l.map toEo)) = T := by
  unfold kindTy at h
  split at h
  all_goals first
    | (rename_i heq
       obtain ⟨a, rfl, rfl⟩ := map_one heq
       obtain rfl := Option.some.inj h
       simp only [List.map_cons, List.map_nil, ← termTy_toEo]
       first | with_reducible exact app_NOT _ | with_reducible exact app_NEG _ | with_reducible exact app_TO_REAL _ | with_reducible exact app_STRING_LENGTH _ | with_reducible exact app_ABS _ | with_reducible exact app_TO_INTEGER _ | with_reducible exact app_IS_INTEGER _ | with_reducible exact app_STRING_IS_DIGIT _ | with_reducible exact app_STRING_ITOS _ | with_reducible exact app_STRING_STOI _ | with_reducible exact app_STRING_TO_CODE _ | with_reducible exact app_STRING_FROM_CODE _ | with_reducible exact app_STRING_TO_LOWER _ | with_reducible exact app_STRING_TO_UPPER _ | with_reducible exact app_STRING_REV _ | with_reducible exact app_STRING_TO_REGEXP _ | with_reducible exact app_REGEXP_STAR _ | with_reducible exact app_REGEXP_PLUS _ | with_reducible exact app_REGEXP_OPT _ | with_reducible exact app_REGEXP_COMPLEMENT _)
    | (rename_i heq
       obtain ⟨a, b, rfl, rfl, rfl⟩ := map_two heq
       obtain rfl := Option.some.inj h
       simp only [List.map_cons, List.map_nil, ← termTy_toEo]
       first | with_reducible exact app_IMPLIES _ _ | with_reducible exact app_XOR _ _ | with_reducible exact app_EQUAL _ _ | with_reducible exact app_SUB _ _ | with_reducible exact app_LT _ _ | with_reducible exact app_LEQ _ _ | with_reducible exact app_GT _ _ | with_reducible exact app_GEQ _ _ | with_reducible exact app_DIVISION _ _ | with_reducible exact app_INTS_DIVISION _ _ | with_reducible exact app_INTS_MODULUS _ _ | with_reducible exact app_INTS_DIVISION_TOTAL _ _ | with_reducible exact app_INTS_MODULUS_TOTAL _ _ | with_reducible exact app_DIVISIBLE _ _ | with_reducible exact app_STRING_CHARAT _ _ | with_reducible exact app_STRING_CONTAINS _ _ | with_reducible exact app_STRING_PREFIX _ _ | with_reducible exact app_STRING_SUFFIX _ _ | with_reducible exact app_STRING_LT _ _ | with_reducible exact app_STRING_LEQ _ _ | with_reducible exact app_STRING_IN_REGEXP _ _ | with_reducible exact app_REGEXP_DIFF _ _ | with_reducible exact app_REGEXP_RANGE _ _)
    | (rename_i heq
       obtain ⟨a, b, c, rfl, rfl, rfl, rfl⟩ := map_three heq
       obtain rfl := Option.some.inj h
       simp only [List.map_cons, List.map_nil, ← termTy_toEo]
       first | with_reducible exact app_ITE _ _ _ | with_reducible exact app_STRING_SUBSTR _ _ _ | with_reducible exact app_STRING_UPDATE _ _ _ | with_reducible exact app_STRING_INDEXOF _ _ _ | with_reducible exact app_STRING_INDEXOF_RE _ _ _ | with_reducible exact app_STRING_REPLACE _ _ _ | with_reducible exact app_STRING_REPLACE_ALL _ _ _ | with_reducible exact app_STRING_REPLACE_RE _ _ _ | with_reducible exact app_STRING_REPLACE_RE_ALL _ _ _)
    | (rename_i heq
       obtain ⟨a, b, rest, rfl, rfl⟩ := map_ge2 heq
       obtain rfl := Option.some.inj h
       rw [← heq]
       first
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_AND, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_OR, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_ADD, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_REGEXP_CONCAT, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_REGEXP_INTER, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_REGEXP_UNION, ← map_toEo_ty]; rfl)
         | (rw [show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl, app_MULT, ← map_toEo_ty]; rfl))
    | (rename_i heq
       obtain ⟨a, b, rest, rfl, ha⟩ := map_ge2 heq
       obtain rfl := Option.some.inj h
       rw [← heq, show ((a :: b :: rest).map toEo) = a.toEo :: b.toEo :: rest.map toEo from rfl,
         app_STRING_CONCAT _ _ _ (by rw [termTy_toEo]; exact ha), ← map_toEo_ty]; rfl)
    | (rename_i heq
       have h0 : l = [] := map_zero heq
       subst h0
       obtain rfl := Option.some.inj h
       simp only [List.map_nil]
       first | with_reducible exact app_REGEXP_NONE | with_reducible exact app_REGEXP_ALL | with_reducible exact app_REGEXP_ALLCHAR)
    | (cases h; done)

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

theorem smtType_string (w : native_String) :
    (Node.const (.string w)).smtType = native_ite (native_string_valid w) (.Seq .Char) .None := by
  simp only [smtType, toSmt, toEo, Const.toEo]; exact termTy_string w
theorem smtType_var_string (x : String) : (Node.var x .string).smtType = .Seq .Char := by
  simp only [smtType, toSmt, toEo, TypeNode.toEo]
  rw [show __eo_to_smt (Term.UConst (constId x) (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))) =
      SmtTerm.UConst (native_uconst_id (constId x)) (SmtType.Seq SmtType.Char) from rfl, __smtx_typeof.eq_def]
  simp only
  simp [__smtx_typeof_guard_wf, __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
    __smtx_inhabited_type, native_ite, native_and]
theorem smtType_purify (t : Node) : (Node.skolem .PURIFY #[t]).smtType = t.smtType := by
  show termTy (Node.skolem .PURIFY #[t]).toEo = termTy t.toEo
  rw [Node.toEo]
  simp only [SkolemId.toEo]
  exact termTy_purify t.toEo

/-- What a node keeps is right: its type is that of its translation; a function
skolem, applied to an argument of its argument type, has its result type. -/
def KeptOk (t : Node) : KeptTy → Prop
  | .none => True
  | .ty T => t.smtType = T
  | .fn A R => ∀ x : Term, termTy x = A → termTy ((nodeEoShape .APPLY_UF t.toEo).toEo [x]) = R

/-- The children's kept types, as `kept` collects them. -/
def keptTys (cs : List Node) : Option (List SmtType) :=
  cs.foldr (fun c acc => acc.bind fun ts => c.kept.ty?.map (· :: ts)) (some [])

theorem ty_ok {t : Node} {T : SmtType} (h : KeptOk t t.kept) (ht : t.kept.ty? = some T) : t.smtType = T := by
  cases hk : t.kept with
  | none => rw [hk] at ht; cases ht
  | ty U => rw [hk] at h ht; simp only [KeptTy.ty?, Option.some.injEq] at ht; subst ht; exact h
  | fn A R => rw [hk] at ht; cases ht

theorem keptTys_sound {cs : List Node} {ts : List SmtType}
    (hc : ∀ c ∈ cs, KeptOk c c.kept) (h : keptTys cs = some ts) : ts = cs.map smtType := by
  induction cs generalizing ts with
  | nil => simp [keptTys] at h; simp [h]
  | cons a l ih =>
    simp only [keptTys, List.foldr_cons] at h
    cases hl : keptTys l with
    | none => simp only [keptTys] at hl; rw [hl] at h; cases h
    | some ts' =>
      simp only [keptTys] at hl; rw [hl] at h
      cases ha : a.kept.ty? with
      | none => rw [ha] at h; cases h
      | some T =>
        rw [ha] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h; subst h
        have := ih (ts := ts') (fun c hm => hc c (by simp [hm])) (by simpa [keptTys] using hl)
        rw [List.map_cons, ty_ok (hc a (by simp)) ha, this]

theorem skolem_toEo (id : SkolemId) (cs : Array Node) :
    (Node.skolem id cs).toEo = id.toEo (cs.toList.map Node.toEo) := by
  rw [Node.toEo]; simp

theorem termTy_stoi_non_digit (a : Term) (h : termTy a = .Seq .Char) :
    termTy (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) a) = .Int := by
  unfold termTy at h ⊢
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) a) = (SmtTerm.str_indexof_re (__eo_to_smt a) (SmtTerm.re_inter SmtTerm.re_allchar (SmtTerm.re_comp (SmtTerm.re_range (SmtTerm.String (native_string_lit "0")) (SmtTerm.String (native_string_lit "9"))))) (SmtTerm.Numeral 0)) from rfl]
  simp only [__smtx_typeof.eq_def (SmtTerm.str_indexof_re _ _ _), h, __smtx_typeof.eq_def (SmtTerm.re_inter _ _),
    __smtx_typeof.eq_def SmtTerm.re_allchar, __smtx_typeof.eq_def (SmtTerm.re_comp _),
    __smtx_typeof.eq_def (SmtTerm.re_range _ _), __smtx_typeof.eq_def (SmtTerm.String _),
    __smtx_typeof.eq_def (SmtTerm.Numeral _)]
  decide

theorem typeof_replace_all (a b c : SmtTerm) : __smtx_typeof (SmtTerm.str_replace_all a b c) =
    __smtx_typeof_seq_op_3 (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_replace_re_all (a b c : SmtTerm) : __smtx_typeof (SmtTerm.str_replace_re_all a b c) =
    native_ite (native_Teq (__smtx_typeof a) (.Seq .Char)) (native_ite (native_Teq (__smtx_typeof b) .RegLan)
      (native_ite (native_Teq (__smtx_typeof c) (.Seq .Char)) (.Seq .Char) .None) .None) .None := by
  rw [__smtx_typeof.eq_def]

theorem typeof_occur (a b c : SmtTerm) : __smtx_typeof (SmtTerm._at_strings_occur_index a b c) =
    __smtx_typeof_str_indexof (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_occur_re (a b c : SmtTerm) : __smtx_typeof (SmtTerm._at_strings_occur_index_re a b c) =
    native_ite (native_Teq (__smtx_typeof a) (.Seq .Char)) (native_ite (native_Teq (__smtx_typeof b) .RegLan)
      (native_ite (native_Teq (__smtx_typeof c) .Int) .Int .None) .None) .None := by
  rw [__smtx_typeof.eq_def]

theorem typeof_ite (a b c : SmtTerm) : __smtx_typeof (SmtTerm.ite a b c) =
    __smtx_typeof_ite (__smtx_typeof a) (__smtx_typeof b) (__smtx_typeof c) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_eq (a b : SmtTerm) : __smtx_typeof (SmtTerm.eq a b) =
    __smtx_typeof_eq (__smtx_typeof a) (__smtx_typeof b) := by
  rw [__smtx_typeof.eq_def]

theorem typeof_to_int (a : SmtTerm) : __smtx_typeof (SmtTerm.str_to_int a) =
    native_ite (native_Teq (__smtx_typeof a) (.Seq .Char)) .Int .None := by
  rw [__smtx_typeof.eq_def]

theorem typeof_from_int (a : SmtTerm) : __smtx_typeof (SmtTerm.str_from_int a) =
    native_ite (native_Teq (__smtx_typeof a) .Int) (.Seq .Char) .None := by
  rw [__smtx_typeof.eq_def]

theorem typeof_div (a b : SmtTerm) : __smtx_typeof (SmtTerm.div a b) =
    native_ite (native_Teq (__smtx_typeof a) .Int) (native_ite (native_Teq (__smtx_typeof b) .Int) .Int .None) .None := by
  rw [__smtx_typeof.eq_def]

theorem typeof_mod (a b : SmtTerm) : __smtx_typeof (SmtTerm.mod a b) =
    native_ite (native_Teq (__smtx_typeof a) .Int) (native_ite (native_Teq (__smtx_typeof b) .Int) .Int .None) .None := by
  rw [__smtx_typeof.eq_def]

/-- Types the translation of a skolem, whose arguments have the types `hs`. -/
macro "skolem_ty" t:term : tactic =>
  `(tactic| (
    simp only [termTy] at *
    rw [show __eo_to_smt _ = $t from rfl]
    simp only [typeof_replace_all, typeof_replace_re_all, typeof_occur, typeof_occur_re, typeof_ite, typeof_eq,
      typeof_to_int, typeof_from_int, typeof_div, typeof_mod, typeof_substr, typeof_neg, typeof_len,
      typeof_numeral, *]
    decide))

theorem skolemTy_sound {id : SkolemId} {cs : Array Node} :
    KeptOk (.skolem id cs) (skolemTy id (cs.toList.map smtType)) := by
  obtain ⟨l⟩ := cs
  simp only
  unfold skolemTy
  split
  all_goals rename_i heq
  · obtain ⟨a, rfl, rfl⟩ := map_one heq
    exact smtType_purify a
  · obtain rfl := map_zero heq
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x) = _
    skolem_ty (SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0))
  · obtain rfl := map_zero heq
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x) = _
    skolem_ty (SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0))
  · obtain ⟨a, rfl, ha⟩ := map_one heq
    show termTy (Node.toEo _) = _
    rw [skolem_toEo]
    exact termTy_stoi_non_digit a.toEo ha
  · obtain ⟨a, b, rfl, ha, hb⟩ := map_two heq
    rw [← termTy_toEo] at ha hb
    show termTy (Node.toEo _) = _
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) a.toEo) b.toEo) = _
    skolem_ty (SmtTerm.neg (SmtTerm.str_len (SmtTerm.str_replace_all (__eo_to_smt a.toEo) (__eo_to_smt b.toEo) (SmtTerm.str_substr (__eo_to_smt a.toEo) (SmtTerm.Numeral 0) (SmtTerm.Numeral 1)))) (SmtTerm.str_len (SmtTerm.str_replace_all (__eo_to_smt a.toEo) (__eo_to_smt b.toEo) (SmtTerm.str_substr (__eo_to_smt a.toEo) (SmtTerm.Numeral 0) (SmtTerm.Numeral 0)))))
  · obtain ⟨a, b, rfl, ha, hb⟩ := map_two heq
    rw [← termTy_toEo] at ha hb
    show termTy (Node.toEo _) = _
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur_re) a.toEo) b.toEo) = _
    skolem_ty (SmtTerm.neg (SmtTerm.str_len (SmtTerm.str_replace_re_all (__eo_to_smt a.toEo) (__eo_to_smt b.toEo) (SmtTerm.str_substr (__eo_to_smt a.toEo) (SmtTerm.Numeral 0) (SmtTerm.Numeral 1)))) (SmtTerm.str_len (SmtTerm.str_replace_re_all (__eo_to_smt a.toEo) (__eo_to_smt b.toEo) (SmtTerm.str_substr (__eo_to_smt a.toEo) (SmtTerm.Numeral 0) (SmtTerm.Numeral 0)))))
  · obtain ⟨a, rfl, ha⟩ := map_one heq
    rw [← termTy_toEo] at ha
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) a.toEo) x) = _
    skolem_ty (SmtTerm.ite (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Numeral 0)) (SmtTerm.Numeral 0) (SmtTerm.str_to_int (SmtTerm.str_substr (__eo_to_smt a.toEo) (SmtTerm.Numeral 0) (__eo_to_smt x))))
  · obtain ⟨a, rfl, ha⟩ := map_one heq
    rw [← termTy_toEo] at ha
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) a.toEo) x) = _
    skolem_ty (SmtTerm.ite (SmtTerm.eq (__eo_to_smt x) (SmtTerm.Numeral 0)) (SmtTerm.Numeral 0) (SmtTerm.str_to_int (SmtTerm.str_substr (SmtTerm.str_from_int (__eo_to_smt a.toEo)) (SmtTerm.Numeral 0) (__eo_to_smt x))))
  · obtain ⟨a, b, rfl, ha, hb⟩ := map_two heq
    rw [← termTy_toEo] at ha hb
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index) a.toEo) b.toEo) x) = _
    skolem_ty (SmtTerm._at_strings_occur_index (__eo_to_smt a.toEo) (__eo_to_smt b.toEo) (__eo_to_smt x))
  · obtain ⟨a, b, rfl, ha, hb⟩ := map_two heq
    rw [← termTy_toEo] at ha hb
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_occur_index_re) a.toEo) b.toEo) x) = _
    skolem_ty (SmtTerm._at_strings_occur_index_re (__eo_to_smt a.toEo) (__eo_to_smt b.toEo) (__eo_to_smt x))
  · obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := map_three heq
    rw [← termTy_toEo] at ha hb hc
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_replace_all_result) a.toEo) b.toEo) c.toEo) x) = _
    skolem_ty (SmtTerm.str_replace_all (SmtTerm.str_substr (__eo_to_smt a.toEo) (SmtTerm._at_strings_occur_index (__eo_to_smt a.toEo) (__eo_to_smt b.toEo) (__eo_to_smt x)) (SmtTerm.str_len (__eo_to_smt a.toEo))) (__eo_to_smt b.toEo) (__eo_to_smt c.toEo))
  · obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := map_three heq
    rw [← termTy_toEo] at ha hb hc
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_replace_re_all_result) a.toEo) b.toEo) c.toEo) x) = _
    skolem_ty (SmtTerm.str_replace_re_all (SmtTerm.str_substr (__eo_to_smt a.toEo) (SmtTerm._at_strings_occur_index_re (__eo_to_smt a.toEo) (__eo_to_smt b.toEo) (__eo_to_smt x)) (SmtTerm.str_len (__eo_to_smt a.toEo))) (__eo_to_smt b.toEo) (__eo_to_smt c.toEo))
  · trivial

theorem indexedTy_sound {k : Kind} {is : Array Int} {l : List Node} {T : SmtType}
    (h : indexedTy k is.toList (l.map smtType) = some T) :
    termTy ((Op.indexed k is).eoShape.toEo (l.map toEo)) = T := by
  obtain ⟨is⟩ := is
  simp only at h
  unfold indexedTy at h
  split at h
  · rename_i i heq
    obtain ⟨a, rfl, ha⟩ := map_one heq
    split at h
    · rename_i hi
      obtain rfl := Option.some.inj h
      show termTy (Term.Apply (Term.UOp1 UserOp1.re_exp (Term.Numeral i)) a.toEo) = _
      rw [← termTy_toEo] at ha
      unfold termTy at ha ⊢
      rw [show __eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp (Term.Numeral i)) a.toEo) =
        SmtTerm.re_exp (SmtTerm.Numeral i) (__eo_to_smt a.toEo) from rfl, __smtx_typeof.eq_def]
      simp [ha, __smtx_typeof_re_exp, native_ite, native_zleq, hi]
    · cases h
  · rename_i i j heq
    obtain ⟨a, rfl, ha⟩ := map_one heq
    split at h
    · rename_i hi
      obtain rfl := Option.some.inj h
      show termTy (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral i) (Term.Numeral j)) a.toEo) = _
      rw [← termTy_toEo] at ha
      unfold termTy at ha ⊢
      rw [show __eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop (Term.Numeral i) (Term.Numeral j)) a.toEo) =
        SmtTerm.re_loop (SmtTerm.Numeral i) (SmtTerm.Numeral j) (__eo_to_smt a.toEo) from rfl, __smtx_typeof.eq_def]
      simp [ha, __smtx_typeof_re_loop, native_ite, native_zleq, hi.1, hi.2]
    · cases h
  · cases h

theorem ofOption_ok {t : Node} {o : Option SmtType} (h : ∀ T, o = some T → t.smtType = T) :
    KeptOk t (.ofOption o) := by
  cases o with
  | none => trivial
  | some T => exact h T rfl

/-- **What a node keeps is right.** -/
theorem kept_sound : ∀ t : Node, KeptOk t t.kept
  | .const c => by
    rw [Node.kept]
    refine ofOption_ok fun T h => ?_
    cases c <;> simp only [Const.ty, Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact smtType_bool _
    · exact smtType_int _
    · exact smtType_rat _
    · exact smtType_string _
  | .var x T' => by
    rw [Node.kept]
    refine ofOption_ok fun T h => ?_
    cases T' <;> simp only [varTy, Option.some.injEq, reduceCtorEq] at h <;> subst h
    · exact smtType_var_boolean x
    · exact smtType_var_integer x
    · exact smtType_var_real x
    · exact smtType_var_string x
  | .boundVar _ _ => by rw [Node.kept]; trivial
  | .skolem id cs => by
    rw [Node.kept, ← Array.foldr_toList]
    change KeptOk _ (match keptTys cs.toList with | some ts => skolemTy id ts | none => .none)
    cases hk : keptTys cs.toList with
    | none => trivial
    | some ts =>
      have hts := keptTys_sound (fun c hm => kept_sound c) hk
      subst hts
      exact skolemTy_sound
  | .app op cs => by
    rw [Node.kept, ← Array.foldr_toList]
    cases hk : keptTys cs.toList with
    | none =>
      simp only [keptTys] at hk
      rw [hk]; trivial
    | some ts =>
      have hts := keptTys_sound (fun c hm => kept_sound c) hk
      simp only [keptTys] at hk
      rw [hk]
      subst hts
      cases op with
      | kind k =>
        refine ofOption_ok fun T h => ?_
        show termTy (Node.app (.kind k) cs).toEo = T
        rw [toEo_app]; exact kindTy_sound h
      | indexed k is =>
        refine ofOption_ok fun T h => ?_
        show termTy (Node.app (.indexed k is) cs).toEo = T
        rw [toEo_app]; exact indexedTy_sound h
      | node k f =>
        simp only
        split
        · rename_i hk
          simp only [beq_iff_eq] at hk
          subst hk
          have hf := kept_sound f
          generalize f.kept = K at hf
          unfold KeptTy.apply
          split
          · rename_i A R T heq
            obtain ⟨a, hl, ha⟩ := map_one heq
            split
            · rename_i hT
              show termTy (Node.app (.node .APPLY_UF f) cs).toEo = R
              rw [toEo_app, hl]
              exact hf a.toEo (by rw [termTy_toEo, ha, hT])
            · trivial
          · trivial
        · trivial
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.mp hm); simp_all; omega)
    | (have := Array.sizeOf_lt_of_mem hm; simp_all; omega)
    | omega
    | (simp_all; omega)

/-- **The kept type of a node is Logos's type of its translation.** -/
theorem fastTy_sound (t : Node) (T : SmtType) (h : t.fastTy = some T) : t.smtType = T :=
  ty_ok (kept_sound t) h

theorem smtTypeR_eq (t : Node) : t.smtTypeR = t.smtType := by
  match t with
  | .const (.boolean b) => rw [smtType_bool, smtTypeR]
  | .const (.integer n) => rw [smtType_int, smtTypeR]
  | .const (.rational q) => rw [smtType_rat, smtTypeR]
  | .const (.bitVector _ _) | .const (.string _) | .const (.emptySet _) | .const (.dtCons _ _)
  | .const (.dtSel _ _ _) => rw [smtTypeR] <;> first | exact termTyF_eq _ | (intros; simp_all)
  | .var x T =>
    cases T
    case boolean => rw [smtType_var_boolean, smtTypeR]
    case integer => rw [smtType_var_integer, smtTypeR]
    case real => rw [smtType_var_real, smtTypeR]
    all_goals (rw [smtTypeR] <;> first | exact termTyF_eq _ | (intros; simp_all))
  | .boundVar _ _ | .skolem _ _ | .app (.indexed _ _) _ | .app (.node _ _) _ => rw [smtTypeR] <;> first | exact termTyF_eq _ | (intros; simp_all)
  | .app (.kind k) cs =>
    have ih : cs.attach.toList.map (fun ⟨c, _⟩ => c.fastTy.getD c.smtTypeR) = cs.toList.map smtType := by
      have hc : ∀ c ∈ cs, c.fastTy.getD c.smtTypeR = c.smtType := fun c _ => by
        cases hf : c.fastTy with
        | none => exact smtTypeR_eq c
        | some T => exact (fastTy_sound c T hf).symm
      have key : ∀ (l : List Node) (H : ∀ x ∈ l, x ∈ cs),
          (l.attachWith (· ∈ cs) H).map (fun ⟨c, _⟩ => c.fastTy.getD c.smtTypeR) = l.map smtType := by
        intro l
        induction l with
        | nil => intro; rfl
        | cons a l ih =>
          intro H
          simp only [List.attachWith_cons, List.map_cons]
          rw [hc a (H a (by simp)), ih]
      rw [Array.toList_attach]
      exact key _ _
    rw [smtTypeR]
    rw [ih]
    split
    · rename_i T hT
      show _ = termTy (Node.app (.kind k) cs).toEo
      rw [toEo_app]
      exact (kindTy_sound hT).symm
    · exact termTyF_eq _

theorem smtTypeF_eq (t : Node) : t.smtTypeF = t.smtType := by
  unfold smtTypeF
  cases hf : t.fastTy with
  | none => exact smtTypeR_eq t
  | some T => exact (fastTy_sound t T hf).symm

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

/-! ## The translation, with the nils typed by `termTyF`

`Node.toEo` (the specification) types the first element of a list by
translating it (`typedNil`), which for a component skolem of an unfolding is
exponential (see `termTyF`). The copies below type it by `termTyF`, and are
proven equal to the originals: the compiler uses them in their place
(`@[csimp]`), in the code that imports this module. -/

def typedNilF (op : UserOp) (x : Term) : Term := typedNilOfType op (termTyF x)

def nilEvalF (op : UserOp) : Telos.Nil → Term → Term
  | .const t, _ => t
  | .typed, x => typedNilF op x

def shapeToEoF : AppShape → List Term → Term
  | .spine head arity, xs => if arity.accepts xs.length then xs.foldl Term.Apply head else Term.Stuck
  | .rightAssocNil op nil, xs =>
    if 2 ≤ xs.length then eoRightAssocNil op (nilEvalF op nil (xs.headD Term.Stuck)) xs
    else Term.Stuck
  | .typedList op, xs =>
    if 2 ≤ xs.length then
      eoApp1 op (eoRightAssocNil UserOp._at__at_TypedList_cons
        (typedNilF UserOp._at__at_TypedList_cons (xs.headD Term.Stuck)) xs)
    else Term.Stuck
  | .binderList, xs => eoList xs
  | .binder op, [vs, body] | .binder op, [vs, body, _] => eoApp2 op vs body
  | .binder _, _ => Term.Stuck
  | .none, _ => Term.Stuck

def toEoF : Node → Term
  | .const c => c.toEo
  | .var name T => Term.UConst (constId name) T.toEo
  | .boundVar name T => Term.Var (Term.String (native_string_lit name)) T.toEo
  | .skolem id cs => id.toEo (cs.attach.toList.map fun ⟨c, _⟩ => c.toEoF)
  | .app (.kind k) cs => shapeToEoF k.eoShape (cs.attach.toList.map fun ⟨c, _⟩ => c.toEoF)
  | .app (.indexed k is) cs =>
      shapeToEoF (indexedEoShape k is.toList) (cs.attach.toList.map fun ⟨c, _⟩ => c.toEoF)
  | .app (.node k f) cs =>
      shapeToEoF (nodeEoShape k f.toEoF) (cs.attach.toList.map fun ⟨c, _⟩ => c.toEoF)

@[csimp] theorem typedNil_csimp : @typedNil = @typedNilF := by
  funext op x; simp [typedNilF, typedNil, termTyF_eq, termTy]

@[csimp] theorem nilEval_csimp : @Telos.Nil.eval = @nilEvalF := by
  funext op n x; cases n <;> simp [nilEvalF, Telos.Nil.eval, typedNil_csimp]

@[csimp] theorem shapeToEo_csimp : @AppShape.toEo = @shapeToEoF := by
  funext s xs
  cases s <;> (try rfl) <;> (simp only [AppShape.toEo, shapeToEoF, nilEval_csimp, typedNil_csimp]) <;> rfl

theorem toEoF_eq : ∀ n : Node, n.toEoF = n.toEo
  | .const c => by rw [toEoF, toEo]
  | .var name T => by rw [toEoF, toEo]
  | .boundVar name T => by rw [toEoF, toEo]
  | .skolem id cs => by
    rw [toEoF, toEo]
    congr 1
    apply List.map_congr_left
    intro ⟨c, hc⟩ _
    exact toEoF_eq c
  | .app (.kind k) cs => by
    rw [toEoF, toEo, ← shapeToEo_csimp]
    congr 1
    apply List.map_congr_left
    intro ⟨c, hc⟩ _
    exact toEoF_eq c
  | .app (.indexed k is) cs => by
    rw [toEoF, toEo, ← shapeToEo_csimp]
    congr 1
    apply List.map_congr_left
    intro ⟨c, hc⟩ _
    exact toEoF_eq c
  | .app (.node k f) cs => by
    rw [toEoF, toEo, ← shapeToEo_csimp, toEoF_eq f]
    congr 1
    apply List.map_congr_left
    intro ⟨c, hc⟩ _
    exact toEoF_eq c
termination_by n => sizeOf n
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have := Array.sizeOf_lt_of_mem hc; omega)
    | omega

@[csimp] theorem toEo_csimp : @toEo = @toEoF := by
  funext n; exact (toEoF_eq n).symm

/-- The other definitions of `ToEo.lean` that translate, by the fast copies
(their callers there are compiled before `toEo_csimp`). -/
def toSmtF (t : Node) : SmtTerm := __eo_to_smt t.toEoF

@[csimp] theorem toSmt_csimp : @toSmt = @toSmtF := by
  funext t; simp [toSmt, toSmtF, toEoF_eq]

def smtTypeFF (t : Node) : SmtType := t.smtTypeF

@[csimp] theorem smtType_csimp : @smtType = @smtTypeFF := by
  funext t; simp [smtTypeFF, smtTypeF_eq]

def getTypeFF (t : Node) : Option TypeNode := TypeNode.ofSmt t.smtTypeF

@[csimp] theorem getType_csimp : @getType = @getTypeFF := by
  funext t; simp [getTypeFF, getType, smtTypeF_eq]

def eqFormulaF (t s : Node) : Term := eoApp2 UserOp.eq t.toEoF s.toEoF

@[csimp] theorem eqFormula_csimp : @eqFormula = @eqFormulaF := by
  funext t s; simp [eqFormula, eqFormulaF, toEoF_eq]

end Node

end Telos
