import Cpc.SmtTranslate
import Cpc.SmtTyping
import Telos.Core.Node.KindTy

/-!
# The type of a CPC term's translation, computed fast

The definitions of `termTy`, Logos's type of a CPC term's translation, and of
`termTyF`, which computes it without translating the component skolems of the
unfoldings of memberships (`@re_unfold_pos_component`), whose translations are
exponential as trees. They come before the translation of nodes (`Node.toEo`),
which types the first element of a list to find its nil (`typedNil`). The
proof that `termTyF` is `termTy` is `termTyF_eq`
(`Telos/Core/Node/SmtTypeFast.lean`).
-/

open Eo
open Smtm
open SmtEval

namespace Telos.Node

/-- The SMT type of a Logos term's translation. -/
def termTy (t : Term) : SmtType := __smtx_typeof (__eo_to_smt t)

/-- The type of `str.indexof_re_split` of arguments of these types. -/
def splitTy (s r₁ r₂ : SmtType) : SmtType :=
  native_ite (native_Teq s (.Seq .Char))
    (native_ite (native_Teq r₁ .RegLan) (native_ite (native_Teq r₂ .RegLan) .Int .None) .None) .None

/-- The type of the translation of the `n`-th component of a string of type
`T` in the concatenation `R` (`__eo_to_smt_re_unfold_pos_component`). -/
def compTy (T : SmtType) : SmtTerm → Nat → SmtType
  | .re_concat r₁ r₂, 0 => __smtx_typeof_str_substr T .Int (splitTy T (__smtx_typeof r₁) (__smtx_typeof r₂))
  | .re_concat r₁ r₂, n + 1 =>
    let v := splitTy T (__smtx_typeof r₁) (__smtx_typeof r₂)
    compTy (__smtx_typeof_str_substr T v (__smtx_typeof_arith_overload_op_2 (__smtx_typeof_seq_op_1_ret T .Int) v))
      r₂ n
  | _, _ => .None

/-- Whether a term has a component skolem. -/
def hasComp : Term → Bool
  | .UOp3 UserOp3._at_re_unfold_pos_component .. => true
  | .Apply f a => hasComp f || hasComp a
  | _ => false

/-- **The type of a term's translation**, without translating component
skolems (`termTyF_eq`). -/
def termTyF (t : Term) : SmtType :=
  if !hasComp t then termTy t else
  match t with
  | .UOp3 UserOp3._at_re_unfold_pos_component x₁ x₂ x₃ =>
    native_ite (__eo_to_smt_nat_is_valid x₃) (compTy (termTyF x₁) (__eo_to_smt x₂) (__eo_to_smt_nat x₃)) .None
  | .Apply (.Apply (.UOp UserOp.eq) a) b => __smtx_typeof_eq (termTyF a) (termTyF b)
  | .Apply (.Apply (.UOp UserOp.and) a) b => boolTy2 (termTyF a) (termTyF b)
  | .Apply (.Apply (.UOp UserOp.or) a) b => boolTy2 (termTyF a) (termTyF b)
  | .Apply (.UOp UserOp.not) a => boolTy1 (termTyF a)
  | .Apply (.Apply (.UOp UserOp.str_in_re) a) b =>
    native_ite (native_Teq (termTyF a) (.Seq .Char)) (native_ite (native_Teq (termTyF b) .RegLan) .Bool .None) .None
  | .Apply (.Apply (.UOp UserOp.str_concat) a) b => __smtx_typeof_seq_op_2 (termTyF a) (termTyF b)
  | .Apply (.UOp UserOp.str_len) a => __smtx_typeof_seq_op_1_ret (termTyF a) .Int
  | .Apply (.UOp UserOp.str_to_code) a => native_ite (native_Teq (termTyF a) (.Seq .Char)) .Int .None
  | .Apply (.UOp UserOp._at_purify) a => termTyF a
  | .Apply (.Apply (.UOp UserOp.plus) a) b => __smtx_typeof_arith_overload_op_2 (termTyF a) (termTyF b)
  | .Apply (.Apply (.UOp UserOp.mult) a) b => __smtx_typeof_arith_overload_op_2 (termTyF a) (termTyF b)
  | .Apply (.Apply (.UOp UserOp.neg) a) b => __smtx_typeof_arith_overload_op_2 (termTyF a) (termTyF b)
  | .Apply (.UOp UserOp.__eoo_neg_2) a => __smtx_typeof_arith_overload_op_1 (termTyF a)
  | .Apply (.Apply (.UOp UserOp.lt) a) b => __smtx_typeof_arith_overload_op_2_ret (termTyF a) (termTyF b) .Bool
  | .Apply (.Apply (.UOp UserOp.leq) a) b => __smtx_typeof_arith_overload_op_2_ret (termTyF a) (termTyF b) .Bool
  | .Apply (.Apply (.UOp UserOp.gt) a) b => __smtx_typeof_arith_overload_op_2_ret (termTyF a) (termTyF b) .Bool
  | .Apply (.UOp UserOp.to_real) a => native_ite (native_Teq (termTyF a) .Int) .Real .None
  | .Apply (.Apply (.UOp UserOp.imp) a) b => boolTy2 (termTyF a) (termTyF b)
  | .Apply (.Apply (.UOp UserOp.xor) a) b => boolTy2 (termTyF a) (termTyF b)
  | .Apply (.Apply (.Apply (.UOp UserOp.str_substr) a) b) c =>
    __smtx_typeof_str_substr (termTyF a) (termTyF b) (termTyF c)
  | .Apply (.Apply (.UOp UserOp.geq) a) b => __smtx_typeof_arith_overload_op_2_ret (termTyF a) (termTyF b) .Bool
  | .Apply (.Apply (.Apply (.UOp UserOp.ite) c) a) b => __smtx_typeof_ite (termTyF c) (termTyF a) (termTyF b)
  | .Apply (.Apply (.UOp UserOp.str_contains) a) b => __smtx_typeof_seq_op_2_ret (termTyF a) (termTyF b) .Bool
  | .Apply (.Apply (.UOp UserOp.str_prefixof) a) b => __smtx_typeof_seq_op_2_ret (termTyF a) (termTyF b) .Bool
  | .Apply (.Apply (.UOp UserOp.str_suffixof) a) b => __smtx_typeof_seq_op_2_ret (termTyF a) (termTyF b) .Bool
  | .Apply (.Apply (.UOp UserOp.str_at) a) b => __smtx_typeof_str_at (termTyF a) (termTyF b)
  | .Apply (.Apply (.Apply (.UOp UserOp.str_indexof) a) b) c => __smtx_typeof_str_indexof (termTyF a) (termTyF b) (termTyF c)
  | .Apply (.Apply (.Apply (.UOp UserOp.str_replace) a) b) c => __smtx_typeof_seq_op_3 (termTyF a) (termTyF b) (termTyF c)
  | .Apply (.Apply (.Apply (.UOp UserOp.str_replace_all) a) b) c => __smtx_typeof_seq_op_3 (termTyF a) (termTyF b) (termTyF c)
  | .Apply (.UOp UserOp.str_to_re) a => native_ite (native_Teq (termTyF a) (.Seq .Char)) .RegLan .None
  | .Apply (.UOp UserOp.str_to_int) a => native_ite (native_Teq (termTyF a) (.Seq .Char)) .Int .None
  | .Apply (.UOp UserOp.str_from_int) a => native_ite (native_Teq (termTyF a) .Int) (.Seq .Char) .None
  | .Apply (.UOp UserOp.str_from_code) a => native_ite (native_Teq (termTyF a) .Int) (.Seq .Char) .None
  | .Apply (.UOp UserOp.str_is_digit) a => native_ite (native_Teq (termTyF a) (.Seq .Char)) .Bool .None
  | .Apply (.UOp UserOp.str_rev) a => __smtx_typeof_seq_op_1 (termTyF a)
  | t => termTy t


end Telos.Node
