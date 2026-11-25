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

/-- The application of a declared constant (Logos translates it as it is). -/
inductive UHead : Term → Prop
  | uconst (i : native_Nat) (T : Term) : UHead (Term.UConst i T)
  | app {g : Term} (x : Term) : UHead g → UHead (Term.Apply g x)

theorem toSmt_apply_uhead {f : Term} (h : UHead f) (y : Term) :
    __eo_to_smt (Term.Apply f y) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt y) := by
  rcases h with _ | ⟨_, h⟩
  · rfl
  rcases h with _ | ⟨_, h⟩
  · rfl
  rcases h with _ | ⟨_, h⟩
  · rfl
  rcases h with _ | ⟨_, h⟩
  · rfl
  rename_i g _
  cases g <;> rfl

theorem typeof_apply_uhead {f : Term} (h : UHead f) (y : Term) :
    termTy (Term.Apply f y) = __smtx_typeof_apply (termTy f) (termTy y) := by
  unfold termTy
  rw [toSmt_apply_uhead h]
  cases h with
  | uconst i T =>
    rw [show __eo_to_smt (Term.UConst i T) = SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T) from rfl,
      __smtx_typeof.eq_def (SmtTerm.Apply _ _)]
  | app x hg => rw [toSmt_apply_uhead hg, __smtx_typeof.eq_def (SmtTerm.Apply _ _)]

theorem isUHead_sound : ∀ {f : Term}, isUHead f = true → UHead f
  | .UConst i T, _ => .uconst i T
  | .Apply f x, h => .app x (isUHead_sound (f := f) (by simpa [isUHead] using h))

theorem typeof_apply_isUHead {f : Term} (h : isUHead f = true) (x : Term) :
    __smtx_typeof_apply (termTy f) (termTy x) = termTy (Term.Apply f x) :=
  (typeof_apply_uhead (isUHead_sound h) x).symm

theorem termTy_uconst (i : native_Nat) (T : Term) : termTy (Term.UConst 0 T) = termTy (Term.UConst i T) := by
  unfold termTy
  rw [show __eo_to_smt (Term.UConst 0 T) = SmtTerm.UConst (native_uconst_id 0) (__eo_to_smt_type T) from rfl,
    show __eo_to_smt (Term.UConst i T) = SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T) from rfl,
    __smtx_typeof.eq_def, __smtx_typeof.eq_def (SmtTerm.UConst (native_uconst_id i) _)]

theorem termTyF_eq (t : Term) : termTyF t = termTy t := by
  fun_induction termTyF t <;>
    first
    | with_reducible rfl
    | exact termTy_uconst _ _
    | (rename_i h ih₁ ih₂; rw [ih₁, ih₂]; exact typeof_apply_isUHead h _)
    | simp_all only [termTy_comp, termTy_str_in_re, termTy_str_to_code, termTy_eq, termTy_and,
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

theorem termTy_qdiv_total (a b : Term) : termTy (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Real := by
  unfold termTy; rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b) = SmtTerm.qdiv_total (__eo_to_smt a) (__eo_to_smt b) from rfl, __smtx_typeof.eq_def] <;> rfl

theorem app_DIVISION_TOTAL (a b : Term) : termTy (Kind.DIVISION_TOTAL.eoShape.toEo [a, b]) = __smtx_typeof_arith_overload_op_2_ret (termTy a) (termTy b) .Real := by
  show termTy (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) a) b) = _; exact termTy_qdiv_total a b

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
       first | with_reducible exact app_IMPLIES _ _ | with_reducible exact app_XOR _ _ | with_reducible exact app_EQUAL _ _ | with_reducible exact app_SUB _ _ | with_reducible exact app_LT _ _ | with_reducible exact app_LEQ _ _ | with_reducible exact app_GT _ _ | with_reducible exact app_GEQ _ _ | with_reducible exact app_DIVISION _ _ | with_reducible exact app_DIVISION_TOTAL _ _ | with_reducible exact app_INTS_DIVISION _ _ | with_reducible exact app_INTS_MODULUS _ _ | with_reducible exact app_INTS_DIVISION_TOTAL _ _ | with_reducible exact app_INTS_MODULUS_TOTAL _ _ | with_reducible exact app_DIVISIBLE _ _ | with_reducible exact app_STRING_CHARAT _ _ | with_reducible exact app_STRING_CONTAINS _ _ | with_reducible exact app_STRING_PREFIX _ _ | with_reducible exact app_STRING_SUFFIX _ _ | with_reducible exact app_STRING_LT _ _ | with_reducible exact app_STRING_LEQ _ _ | with_reducible exact app_STRING_IN_REGEXP _ _ | with_reducible exact app_REGEXP_DIFF _ _ | with_reducible exact app_REGEXP_RANGE _ _)
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

/-- A list of variables of types `Ts`, as translated. -/
inductive BinderOk : Term → List SmtType → Prop
  | nil : BinderOk Term.__eo_List_nil []
  | cons {s : native_String} {Ty vs : Term} {T : SmtType} {Ts : List SmtType} :
      __eo_to_smt_type Ty = T → __smtx_type_wf T = true → BinderOk vs Ts →
      BinderOk (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) Ty)) vs) (T :: Ts)

/-- A concatenation of (at least) `n` regular expressions. -/
def CatOk : SmtTerm → Nat → Prop
  | _, 0 => True
  | .re_concat a b, n + 1 => __smtx_typeof a = .RegLan ∧ __smtx_typeof b = .RegLan ∧ CatOk b n
  | _, _ + 1 => False

/-- What a node keeps is right: its type is that of its translation; a function
skolem, applied to an argument of its argument type, has its result type; and
the translation has the form that is kept. -/
def KeptOk (t : Node) : KeptTy → Prop
  | .none => True
  | .ty T => t.smtType = T
  | .fn A R => ∀ x : Term, termTy x = A → termTy ((nodeEoShape .APPLY_UF t.toEo).toEo [x]) = R
  | .uf F => (∃ i Ty, t.toEo = Term.UConst i Ty) ∧ t.smtType = F
  | .bvar T => (∃ s Ty, t.toEo = Term.Var (Term.String s) Ty ∧ __eo_to_smt_type Ty = T ∧ __smtx_type_wf T = true) ∧
      t.smtType = T
  | .binder Ts => BinderOk t.toEo Ts
  | .quant Ts => (∃ vs F, t.toEo = Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) F ∧ BinderOk vs Ts ∧
      termTy F = .Bool) ∧ t.smtType = .Bool
  | .recat n => CatOk t.toSmt n ∧ t.smtType = .RegLan
  | .num i => t.toEo = Term.Numeral i ∧ t.smtType = .Int

theorem ty_ok' {t : Node} {k : KeptTy} {T : SmtType} (h : KeptOk t k) (ht : k.ty? = some T) : t.smtType = T := by
  cases k <;> simp only [KeptTy.ty?, Option.some.injEq, reduceCtorEq] at ht <;> subst ht
  · exact h
  · exact h.2
  · exact h.2
  · exact h.2
  · exact h.2
  · exact h.2

theorem ty_ok {t : Node} {T : SmtType} (h : KeptOk t t.kept) (ht : t.kept.ty? = some T) : t.smtType = T :=
  ty_ok' h ht

/-- What the children keep, as `kept` collects it. -/
def keptsOf (cs : List Node) : List KeptTy := cs.foldr (fun c acc => c.kept :: acc) []

theorem keptsOf_map (cs : List Node) : keptsOf cs = cs.map Node.kept := by
  induction cs with
  | nil => rfl
  | cons a l ih => simp only [keptsOf, List.foldr_cons, List.map_cons] at ih ⊢; rw [ih]

theorem keptTys_sound {cs : List Node} {ts : List SmtType}
    (hc : ∀ c ∈ cs, KeptOk c c.kept) (h : KeptTy.tys (cs.map Node.kept) = some ts) : ts = cs.map smtType := by
  induction cs generalizing ts with
  | nil => simp [KeptTy.tys] at h; simp [h]
  | cons a l ih =>
    simp only [List.map_cons, KeptTy.tys] at h
    cases hl : KeptTy.tys (l.map Node.kept) with
    | none => rw [hl] at h; cases h
    | some ts' =>
      rw [hl] at h
      cases ha : a.kept.ty? with
      | none => rw [ha] at h; cases h
      | some T =>
        rw [ha] at h
        simp only [Option.bind_some, Option.map_some, Option.some.injEq] at h; subst h
        have := ih (ts := ts') (fun c hm => hc c (by simp [hm])) hl
        rw [List.map_cons, ty_ok (hc a (by simp)) ha, this]

theorem bvars_sound {cs : List Node} {Ts : List SmtType}
    (hc : ∀ c ∈ cs, KeptOk c c.kept) (h : KeptTy.bvars (cs.map Node.kept) = some Ts) :
    BinderOk (eoList (cs.map Node.toEo)) Ts := by
  induction cs generalizing Ts with
  | nil => simp [KeptTy.bvars] at h; subst h; exact .nil
  | cons a l ih =>
    simp only [List.map_cons, KeptTy.bvars] at h
    cases hl : KeptTy.bvars (l.map Node.kept) with
    | none => rw [hl] at h; cases h
    | some Ts' =>
      rw [hl] at h
      have hak := hc a (by simp)
      cases ha : a.kept <;> rw [ha] at h hak <;> simp only [KeptTy.bvar?, Option.bind_some, Option.map_none,
        Option.map_some, reduceCtorEq, Option.some.injEq] at h
      subst h
      obtain ⟨⟨s, Ty, he, hT, hwf⟩, -⟩ := hak
      simp only [List.map_cons, eoList]
      rw [he]
      exact .cons hT hwf (ih (fun c hm => hc c (by simp [hm])) hl)

theorem smtTyOf_sound : ∀ (T : TypeNode) {S : SmtType}, smtTyOf T = some S →
    __eo_to_smt_type T.toEo = S ∧ S ≠ .None := by
  intro T
  induction T using smtTyOf.induct with
  | case1 | case2 | case3 | case4 | case5 | case6 =>
    intro S h
    simp only [smtTyOf, Option.some.injEq] at h
    subst h
    refine ⟨?_, by simp⟩
    simp only [TypeNode.toEo]
    first | rfl | simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]
  | case7 e ih =>
    intro S h
    simp only [smtTyOf, Option.map_eq_some_iff] at h
    obtain ⟨E, hE, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hE
    refine ⟨?_, by simp⟩
    simp only [TypeNode.toEo]
    rw [show __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) e.toEo) =
      __smtx_typeof_guard (__eo_to_smt_type e.toEo) (SmtType.Seq (__eo_to_smt_type e.toEo)) from rfl, h1]
    simp [__smtx_typeof_guard, native_ite, native_Teq, h2]
  | case8 e ih =>
    intro S h
    simp only [smtTyOf, Option.map_eq_some_iff] at h
    obtain ⟨E, hE, rfl⟩ := h
    obtain ⟨h1, h2⟩ := ih hE
    refine ⟨?_, by simp⟩
    simp only [TypeNode.toEo]
    rw [show __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) e.toEo) =
      __smtx_typeof_guard (__eo_to_smt_type e.toEo) (SmtType.Set (__eo_to_smt_type e.toEo)) from rfl, h1]
    simp [__smtx_typeof_guard, native_ite, native_Teq, h2]
  | case9 a r iha ihr =>
    intro S h
    simp only [smtTyOf, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, R, hR, rfl⟩ := h
    obtain ⟨h1, h2⟩ := iha hA
    obtain ⟨h3, h4⟩ := ihr hR
    refine ⟨?_, by simp⟩
    simp only [TypeNode.toEo]
    rw [show __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType a.toEo) r.toEo) =
      __smtx_typeof_guard (__eo_to_smt_type a.toEo) (__smtx_typeof_guard (__eo_to_smt_type r.toEo)
        (SmtType.FunType (__eo_to_smt_type a.toEo) (__eo_to_smt_type r.toEo))) from rfl, h1, h3]
    simp [__smtx_typeof_guard, native_ite, native_Teq, h2, h4]
  | case10 T h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    intro S h
    unfold smtTyOf at h
    split at h <;> simp_all

theorem varTy_sound {T : TypeNode} {S : SmtType} (h : varTy T = some S) :
    __eo_to_smt_type T.toEo = S ∧ __smtx_type_wf S = true := by
  unfold varTy at h
  split at h
  · rename_i U hU
    split at h
    · rename_i hwf
      obtain rfl := Option.some.inj h
      exact ⟨(smtTyOf_sound T hU).1, hwf⟩
    · cases h
  · cases h

theorem smtType_var {x : String} {T : TypeNode} {S : SmtType} (h : varTy T = some S) : (Node.var x T).smtType = S := by
  obtain ⟨h1, h2⟩ := varTy_sound h
  simp only [smtType, toSmt, toEo]
  rw [show __eo_to_smt (Term.UConst (constId x) T.toEo) = SmtTerm.UConst (native_uconst_id (constId x)) (__eo_to_smt_type T.toEo)
    from rfl, h1, __smtx_typeof.eq_def]
  simp [__smtx_typeof_guard_wf, h2, native_ite]

theorem smtType_boundVar {x : String} {T : TypeNode} {S : SmtType} (h : varTy T = some S) :
    (Node.boundVar x T).smtType = S := by
  obtain ⟨h1, h2⟩ := varTy_sound h
  simp only [smtType, toSmt, toEo]
  rw [show __eo_to_smt (Term.Var (Term.String (native_string_lit x)) T.toEo) =
    SmtTerm.Var (native_string_lit x) (__eo_to_smt_type T.toEo) from rfl, h1, __smtx_typeof.eq_def]
  simp [__smtx_typeof_guard_wf, h2, native_ite]

theorem typeof_not (a : SmtTerm) : __smtx_typeof (SmtTerm.not a) =
    native_ite (native_Teq (__smtx_typeof a) .Bool) .Bool .None := by
  rw [__smtx_typeof.eq_def]

/-- An existential formula over well-formed variables is a Boolean. -/
theorem typeof_exists {vs : Term} {Ts : List SmtType} (h : BinderOk vs Ts) {F : SmtTerm}
    (hF : __smtx_typeof F = .Bool) : __smtx_typeof (__eo_to_smt_exists vs F) = .Bool := by
  induction h with
  | nil => exact hF
  | cons hT hwf _ ih =>
    simp only [__eo_to_smt_exists]
    rw [__smtx_typeof.eq_def]
    simp [ih, hT, __smtx_typeof_guard_wf, hwf, native_ite, native_Teq]

theorem typeof_choice {s : native_String} {T : SmtType} {F : SmtTerm} (hwf : __smtx_type_wf T = true)
    (hF : __smtx_typeof F = .Bool) : __smtx_typeof (SmtTerm.choice s T F) = T := by
  rw [__smtx_typeof.eq_def]
  simp [hF, __smtx_typeof_guard_wf, hwf, native_ite, native_Teq]

/-- The skolem of the `n`-th variable has its type. -/
theorem typeof_skolemize {vs : Term} {Ts : List SmtType} (h : BinderOk vs Ts) :
    ∀ {G : SmtTerm} {n : Nat} {T : SmtType}, __smtx_typeof G = .Bool → Ts[n]? = some T →
      __smtx_typeof (__eo_to_smt_quantifiers_skolemize vs G n) = T := by
  induction h with
  | nil => intro G n T _ hn; simp at hn
  | @cons s Ty vs T' Ts hT hwf hvs ih =>
    intro G n T hG hn
    have hc : __smtx_typeof (SmtTerm.choice s T' (__eo_to_smt_exists vs G)) = T' :=
      typeof_choice hwf (typeof_exists hvs hG)
    cases n with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hn
      subst hn
      simp only [__eo_to_smt_quantifiers_skolemize, hT]
      exact hc
    | succ n =>
      simp only [List.getElem?_cons_succ] at hn
      simp only [__eo_to_smt_quantifiers_skolemize, hT]
      refine ih ?_ hn
      rw [__smtx_typeof.eq_def]
      simp [hc, hG, __smtx_typeof_guard_wf, hwf, native_ite, native_Teq]

/-- A component of a concatenation of regular expressions is a string. -/
theorem compTy_string : ∀ (n : Nat) {R : SmtTerm} {m : Nat}, CatOk R m → n < m →
    compTy (.Seq .Char) R n = .Seq .Char := by
  intro n
  induction n with
  | zero =>
    intro R m h hm
    cases m with
    | zero => omega
    | succ m =>
      cases R <;> simp only [CatOk] at h
      simp only [compTy, splitTy, h.1, h.2.1]
      decide
  | succ n ih =>
    intro R m h hm
    cases m with
    | zero => omega
    | succ m =>
      cases R <;> simp only [CatOk] at h
      simp only [compTy, splitTy, h.1, h.2.1]
      have : __smtx_typeof_str_substr (.Seq .Char)
          (native_ite (native_Teq (.Seq .Char) (.Seq .Char)) (native_ite (native_Teq SmtType.RegLan .RegLan)
            (native_ite (native_Teq SmtType.RegLan .RegLan) .Int .None) .None) .None)
          (__smtx_typeof_arith_overload_op_2 (__smtx_typeof_seq_op_1_ret (.Seq .Char) .Int)
            (native_ite (native_Teq (.Seq .Char) (.Seq .Char)) (native_ite (native_Teq SmtType.RegLan .RegLan)
              (native_ite (native_Teq SmtType.RegLan .RegLan) .Int .None) .None) .None)) = .Seq .Char := by decide
      rw [this]
      exact ih h.2.2 (by omega)

theorem reTy2_inv {T U : SmtType} (h : reTy2 T U = .RegLan) : T = .RegLan ∧ U = .RegLan := by
  by_cases h1 : T = .RegLan <;> by_cases h2 : U = .RegLan <;> simp_all [reTy2, native_ite, native_Teq]

theorem kepts_one {l : List Node} {x : KeptTy} (h : l.map Node.kept = [x]) : ∃ a, l = [a] ∧ a.kept = x := by
  match l, h with | [a], h => exact ⟨a, rfl, by simpa using h⟩
theorem kepts_two {l : List Node} {x y : KeptTy} (h : l.map Node.kept = [x, y]) :
    ∃ a b, l = [a, b] ∧ a.kept = x ∧ b.kept = y := by
  match l, h with | [a, b], h => simp at h; exact ⟨a, b, rfl, h.1, h.2⟩
theorem kepts_three {l : List Node} {x y z : KeptTy} (h : l.map Node.kept = [x, y, z]) :
    ∃ a b c, l = [a, b, c] ∧ a.kept = x ∧ b.kept = y ∧ c.kept = z := by
  match l, h with | [a, b, c], h => simp at h; exact ⟨a, b, c, rfl, h.1, h.2.1, h.2.2⟩

/-- The translation of a concatenation of regular expressions. -/
theorem catOk_chain : ∀ (l : List Node),
    (l.map smtType).foldr reTy2 .RegLan = .RegLan →
    CatOk (__eo_to_smt (eoRightAssocNil UserOp.re_concat
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) (l.map toEo))) l.length ∧
    __smtx_typeof (__eo_to_smt (eoRightAssocNil UserOp.re_concat
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) (l.map toEo))) = .RegLan := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨trivial, ?_⟩
    simp only [List.map_nil, eoRightAssocNil]
    show termTy _ = _
    rw [termTy_str_to_re, termTy_string]
    decide
  | cons a l ih =>
    intro h
    simp only [List.map_cons, List.foldr_cons] at h
    obtain ⟨ha, hl⟩ := reTy2_inv h
    obtain ⟨i1, i2⟩ := ih hl
    simp only [List.map_cons, eoRightAssocNil, List.length_cons]
    rw [show ∀ x y, __eo_to_smt (eoApp2 UserOp.re_concat x y) = SmtTerm.re_concat (__eo_to_smt x) (__eo_to_smt y)
      from fun _ _ => rfl]
    refine ⟨⟨ha, i2, i1⟩, ?_⟩
    rw [__smtx_typeof.eq_def]
    have ha' : __smtx_typeof (__eo_to_smt a.toEo) = .RegLan := ha
    simp [ha', i2, native_ite, native_Teq]

theorem termTy_foldl_uhead : ∀ (xs : List Term) {f : Term}, UHead f →
    termTy (xs.foldl Term.Apply f) = (xs.map termTy).foldl __smtx_typeof_apply (termTy f)
  | [], _, _ => rfl
  | x :: xs, f, hf => by
    simp only [List.foldl, List.map]
    rw [termTy_foldl_uhead xs (UHead.app x hf), typeof_apply_uhead hf]

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
  · obtain rfl := map_zero heq
    intro x hx
    rw [skolem_toEo]
    show termTy (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) = _
    unfold termTy at hx ⊢
    rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp._at_div_by_zero) x) =
      SmtTerm.qdiv (__eo_to_smt x) (SmtTerm.Rational (native_mk_rational 0 1)) from rfl]
    have hq : ∀ a b, __smtx_typeof (SmtTerm.qdiv a b) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof a) (__smtx_typeof b) .Real := by
      intro a b; rw [__smtx_typeof.eq_def]
    have hr : ∀ r, __smtx_typeof (SmtTerm.Rational r) = .Real := by intro r; rw [__smtx_typeof.eq_def]
    rw [hq, hx, hr]
    rfl
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

theorem forall_ok {t : Node} {vs F : Term} {T : SmtType} {Ts : List SmtType}
    (he : t.toEo = Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) F) (hb : BinderOk vs (T :: Ts))
    (hF : termTy F = .Bool) : KeptOk t (.quant (T :: Ts)) := by
  refine ⟨⟨vs, F, he, hb, hF⟩, ?_⟩
  show termTy t.toEo = _
  rw [he]
  unfold termTy
  have hF' : __smtx_typeof (__eo_to_smt F) = .Bool := hF
  have hx : __smtx_typeof (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt F))) = .Bool :=
    typeof_exists hb (by rw [typeof_not, hF']; decide)
  cases hb with
  | @cons s Ty vs' _ _ hT hwf hvs =>
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall)
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) Ty)) vs')) F) =
      SmtTerm.not (__eo_to_smt_exists (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) Ty)) vs')
        (SmtTerm.not (__eo_to_smt F))) from rfl, typeof_not, hx]
    decide

theorem skolemKept_sound {id : SkolemId} {cs : Array Node} (hc : ∀ c ∈ cs.toList, KeptOk c c.kept) :
    KeptOk (.skolem id cs) (skolemKept id (cs.toList.map Node.kept)) := by
  have gen : KeptOk (.skolem id cs) (match KeptTy.tys (cs.toList.map Node.kept) with
      | some ts => skolemTy id ts | none => .none) := by
    cases hk : KeptTy.tys (cs.toList.map Node.kept) with
    | none => trivial
    | some ts =>
      have hts := keptTys_sound hc hk
      subst hts
      exact skolemTy_sound
  unfold skolemKept
  split
  · -- `@quantifiers_skolemize`
    rename_i Ts i heq
    obtain ⟨q, n, hl, hq, hn⟩ := kepts_two heq
    have kq := hc q (by simp [hl])
    have kn := hc n (by simp [hl])
    rw [hq] at kq; rw [hn] at kn
    obtain ⟨⟨vs, F, he, hb, hF⟩, -⟩ := kq
    split
    · rename_i hi
      split
      · rename_i T hT
        show termTy (Node.toEo _) = T
        rw [skolem_toEo, hl]
        simp only [List.map_cons, List.map_nil, SkolemId.toEo, he, kn.1]
        unfold termTy
        rw [show __eo_to_smt (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) F) (Term.Numeral i)) =
          native_ite (native_zleq 0 i)
            (__eo_to_smt_quantifiers_skolemize vs (SmtTerm.not (__eo_to_smt F)) (native_int_to_nat i)) SmtTerm.None from rfl]
        simp only [native_zleq, hi, decide_true, native_ite, ↓reduceIte]
        refine typeof_skolemize hb ?_ hT
        have hF' : __smtx_typeof (__eo_to_smt F) = .Bool := hF
        rw [typeof_not, hF']; decide
      · trivial
    · trivial
  · -- `@re_unfold_pos_component`
    rename_i k n i heq
    obtain ⟨a, r, m, hl, ha, hr, hm⟩ := kepts_three heq
    have ka := hc a (by simp [hl])
    have kr := hc r (by simp [hl])
    have km := hc m (by simp [hl])
    rw [hr] at kr; rw [hm] at km
    split
    · rename_i hcond
      have hta := ty_ok ka (by rw [ha]; exact hcond.1)
      show termTy (Node.toEo _) = _
      rw [skolem_toEo, hl]
      simp only [List.map_cons, List.map_nil, SkolemId.toEo, km.1]
      rw [termTy_comp, termTy_toEo, hta]
      simp only [__eo_to_smt_nat_is_valid, native_zleq, hcond.2.1, decide_true, native_ite, ↓reduceIte, __eo_to_smt_nat]
      exact compTy_string _ kr.1 hcond.2.2
    · trivial
  · exact gen

theorem appKept_sound {k : Kind} {cs : Array Node} (hc : ∀ c ∈ cs.toList, KeptOk c c.kept) :
    KeptOk (.app (.kind k) cs) (appKept k (cs.toList.map Node.kept)) := by
  unfold appKept
  split
  · split
    · rename_i Ts hT
      show BinderOk (Node.toEo _) Ts
      rw [toEo_app]
      exact bvars_sound hc hT
    · trivial
  · rename_i T Ts b heq
    obtain ⟨v, body, hl, hv, hb⟩ := kepts_two heq
    have kv := hc v (by simp [hl])
    have kb := hc body (by simp [hl])
    rw [hv] at kv
    split
    · rename_i hB
      have hF := ty_ok kb (by rw [hb]; exact hB)
      have he : (Node.app (.kind .FORALL) cs).toEo = Term.Apply (Term.Apply (Term.UOp UserOp.forall) v.toEo) body.toEo := by
        rw [toEo_app, hl]; rfl
      exact forall_ok he kv hF
    · trivial
  · rename_i T Ts b p heq
    obtain ⟨v, body, pat, hl, hv, hb, -⟩ := kepts_three heq
    have kv := hc v (by simp [hl])
    have kb := hc body (by simp [hl])
    rw [hv] at kv
    split
    · rename_i hB
      have hF := ty_ok kb (by rw [hb]; exact hB)
      have he : (Node.app (.kind .FORALL) cs).toEo = Term.Apply (Term.Apply (Term.UOp UserOp.forall) v.toEo) body.toEo := by
        rw [toEo_app, hl]; rfl
      exact forall_ok he kv hF
    · trivial
  · rename_i k ks _ _ _
    split
    · rename_i ts hts'
      have hts := keptTys_sound hc hts'
      subst hts
      split
      · rename_i hcat
        simp only [Bool.and_eq_true, beq_iff_eq] at hcat
        obtain ⟨rfl, hkt⟩ := hcat
        have hty : (Node.app (.kind .REGEXP_CONCAT) cs).smtType = .RegLan := by
          show termTy (Node.toEo _) = _
          rw [toEo_app]; exact kindTy_sound hkt
        refine ⟨?_, hty⟩
        match hl : cs.toList, hkt with
        | a :: b :: rest, hkt =>
          simp only [List.map_cons, kindTy, Option.some.injEq] at hkt
          have := (catOk_chain (a :: b :: rest) (by simpa using hkt)).1
          unfold toSmt
          rw [toEo_app, hl]
          simp only [List.map_cons] at this ⊢
          show CatOk (__eo_to_smt (eoRightAssocNil UserOp.re_concat
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])) (a.toEo :: b.toEo :: rest.map toEo))) _
          simpa only [List.length_cons, List.length_map] using this
      · refine ofOption_ok fun T h => ?_
        show termTy (Node.app (.kind _) cs).toEo = T
        rw [toEo_app]; exact kindTy_sound h
    · trivial

/-- **What a node keeps is right.** -/
theorem kept_sound : ∀ t : Node, KeptOk t t.kept
  | .const (.integer n) => by
    rw [Node.kept]
    exact ⟨by simp [Node.toEo, Const.toEo], smtType_int n⟩
  | .const (.boolean b) => by
    rw [Node.kept.eq_def]
    exact smtType_bool b
  | .const (.rational q) => by
    rw [Node.kept.eq_def]
    exact smtType_rat q
  | .const (.string w) => by
    rw [Node.kept.eq_def]
    exact smtType_string w
  | .const (.bitVector ..) | .const (.emptySet _) | .const (.emptySeq _) | .const (.dtCons ..)
  | .const (.dtSel ..) => by
    rw [Node.kept.eq_def]; trivial
  | .var x T' => by
    rw [Node.kept]
    split
    · rename_i S hS
      exact ⟨⟨_, _, by rw [Node.toEo]⟩, smtType_var hS⟩
    · trivial
  | .boundVar x T' => by
    rw [Node.kept]
    split
    · rename_i S hS
      exact ⟨⟨_, _, by rw [Node.toEo], varTy_sound hS⟩, smtType_boundVar hS⟩
    · trivial
  | .skolem id cs => by
    rw [Node.kept, ← Array.foldr_toList]
    change KeptOk _ (skolemKept id (keptsOf cs.toList))
    rw [keptsOf_map]
    exact skolemKept_sound fun c hm => kept_sound c
  | .app op cs => by
    rw [Node.kept.eq_def]
    dsimp only
    rw [← Array.foldr_toList]
    change KeptOk _ (match op with
      | .kind k => appKept k (keptsOf cs.toList)
      | .indexed k is => match KeptTy.tys (keptsOf cs.toList) with
        | some ts => .ofOption (indexedTy k is.toList ts) | none => .none
      | .node k f => if k == .APPLY_UF then f.kept.apply (keptsOf cs.toList) else .none)
    rw [keptsOf_map]
    cases op with
    | kind k => exact appKept_sound fun c hm => kept_sound c
    | indexed k is =>
      simp only
      split
      · rename_i ts hts'
        have hts := keptTys_sound (fun c hm => kept_sound c) hts'
        subst hts
        refine ofOption_ok fun T h => ?_
        show termTy (Node.app (.indexed k is) cs).toEo = T
        rw [toEo_app]; exact indexedTy_sound h
      · trivial
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
        · rename_i A R k' heq
          obtain ⟨a, hl, ha⟩ := kepts_one heq
          split
          · rename_i hT
            show termTy (Node.app (.node .APPLY_UF f) cs).toEo = R
            rw [toEo_app, hl]
            have hm : a ∈ cs.toList := by simp [hl]
            exact hf a.toEo (by rw [termTy_toEo]; exact ty_ok (kept_sound a) (by rw [ha]; exact hT))
          · trivial
        · rename_i F k' ks heq
          obtain ⟨⟨i, Ty, he⟩, hF⟩ := hf
          split
          · rename_i ts hts'
            rw [← heq] at hts'
            have hts := keptTys_sound (fun c hm => kept_sound c) hts'
            subst hts
            show termTy (Node.app (.node .APPLY_UF f) cs).toEo = _
            have hne : 1 ≤ cs.toList.length := by
              have := congrArg List.length heq
              simp at this; simp; omega
            rw [toEo_app]
            simp only [Op.eoShape, nodeEoShape, he, isFnSkolemTerm, Bool.false_eq_true, ↓reduceIte, AppShape.toEo,
              Arity.accepts, List.length_map, hne, decide_true]
            rw [termTy_foldl_uhead _ (UHead.uconst i Ty), map_toEo_ty]
            have : termTy (Term.UConst i Ty) = F := by rw [← hF, ← termTy_toEo, he]
            rw [this]
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
  | .const (.bitVector _ _) | .const (.string _) | .const (.emptySet _) | .const (.emptySeq _) | .const (.dtCons _ _)
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

/-- The kept type of the first of the nodes, or its type computed from its
translation `x`. -/
def headTy (cs : Array Node) (xs : List Term) : SmtType :=
  match cs[0]? with
  | some c => match c.fastTy with
    | some T => T
    | none => termTyF (xs.headD Term.Stuck)
  | none => termTyF (xs.headD Term.Stuck)

theorem headTy_eq (cs : Array Node) (xs : List Term) (h : xs = cs.toList.map toEo) :
    headTy cs xs = termTy (xs.headD Term.Stuck) := by
  unfold headTy
  split
  · rename_i c hc
    split
    · rename_i T hT
      have : xs.headD Term.Stuck = c.toEo := by
        obtain ⟨l⟩ := cs
        subst h
        cases l with
        | nil => simp at hc
        | cons a l => simp at hc; subst hc; rfl
      rw [this, termTy_toEo]
      exact (fastTy_sound c T hT).symm
    · exact termTyF_eq _
  · exact termTyF_eq _

def toEoF : Node → Term
  | .const c => c.toEo
  | .var name T => Term.UConst (constId name) T.toEo
  | .boundVar name T => Term.Var (Term.String (native_string_lit name)) T.toEo
  | .skolem id cs => id.toEo (cs.attach.toList.map fun ⟨c, _⟩ => c.toEoF)
  | .app (.kind k) cs =>
      let xs := cs.attach.toList.map fun ⟨c, _⟩ => c.toEoF
      match k.eoShape with
      | .rightAssocNil op .typed =>
        if 2 ≤ xs.length then eoRightAssocNil op (typedNilOfType op (headTy cs xs)) xs else Term.Stuck
      | s => shapeToEoF s xs
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
    have hl : (cs.attach.toList.map fun ⟨c, _⟩ => c.toEoF) = cs.toList.map toEo := by
      have : (cs.attach.toList.map fun ⟨c, _⟩ => c.toEoF) = cs.attach.toList.map fun ⟨c, _⟩ => c.toEo := by
        apply List.map_congr_left
        intro ⟨c, hc⟩ _
        exact toEoF_eq c
      rw [this]; simp
    rw [toEoF, toEo_app]
    simp only [hl, Op.eoShape]
    split
    · rename_i op hs
      rw [hs, headTy_eq cs _ rfl]
      rfl
    · rw [← shapeToEo_csimp]
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
