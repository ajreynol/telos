import TelosProofs.Core.LogosFacts
import Telos.Core.Certified

/-!
# Template rule steps are CPC steps

`TRule.provesEq`: under `TRule.Ok`, the command list of a template step
(`Telos/Core/Template.lean`) is accepted by Logos's checker, read left to right,
or right to left by a `symm` step. The generic part (`provesEq_one`,
`provesEq_one_symm`) needs only that the rule's step yields `(= n m)` from the
empty state (`TRule.step_eq`), one case per rule.
-/

open Eo Smtm SmtEval

namespace Telos

namespace Template

/-- `__eo_is_bool_type` of a formula of SMT type `Bool`. -/
theorem is_bool_type_of [LogosFacts] {F : Term} (hF : F ≠ .Stuck)
    (h : __smtx_typeof (__eo_to_smt F) = SmtType.Bool) : __eo_is_bool_type F = .Boolean true := by
  unfold __eo_is_bool_type
  split
  · exact absurd rfl hF
  · rw [LogosFacts.eo_typeof_bool _ h]; simp [__eo_eq, native_teq]

theorem eqFormula_ne_stuck (a b : Node) : eqFormula a b ≠ .Stuck := by simp [eqFormula, eoApp2]

/-- One step, whose rule yields `(= n m)` from the empty state. -/
theorem provesEq_one [LogosFacts] {r : CRule} {args : CArgList} {n m : Node}
    (hT : cmdTranslationOk (.step r args .nil))
    (hstep : __eo_cmd_step_proven CState.nil r args .nil = eqFormula n m)
    (hty : __smtx_typeof (__eo_to_smt (eqFormula n m)) = SmtType.Bool) :
    ProvesEq (.cons (.step r args .nil) .nil) n m := by
  have hrun : runFromEmpty (.cons (.step r args .nil) .nil) =
      CState.cons (CStateObj.proven (eqFormula n m)) CState.nil := by
    show __eo_invoke_cmd_list CState.nil (.cons (.step r args .nil) .nil) = _
    rw [__eo_invoke_cmd_list, __eo_invoke_cmd_list, __eo_invoke_cmd] <;> try simp
    rw [hstep, __eo_push_proven, is_bool_type_of (eqFormula_ne_stuck n m) hty, __eo_push_proven_check]
  refine ⟨CmdListTranslationOk.cons _ _ hT CmdListTranslationOk.nil, ?_, ?_⟩
  · rw [hrun]; rfl
  · rw [hrun]; rfl

theorem typeof_eq_comm {T U : SmtType} (h : __smtx_typeof_eq T U = SmtType.Bool) :
    __smtx_typeof_eq U T = SmtType.Bool := by
  unfold __smtx_typeof_eq __smtx_typeof_guard at *
  cases T <;> cases U <;> simp_all [native_ite, native_Teq]

/-- One step, whose rule yields `(= m n)` from the empty state, then `symm`. -/
theorem provesEq_one_symm [LogosFacts] {r : CRule} {args : CArgList} {n m : Node}
    (hT : cmdTranslationOk (.step r args .nil))
    (hstep : __eo_cmd_step_proven CState.nil r args .nil = eqFormula m n)
    (hty : __smtx_typeof (__eo_to_smt (eqFormula m n)) = SmtType.Bool) :
    ProvesEq (.cons (.step r args .nil) (.cons (.step .symm .nil (.cons 0 .nil)) .nil)) n m := by
  have hty' : __smtx_typeof (__eo_to_smt (eqFormula n m)) = SmtType.Bool := by
    rw [Node.typeof_eqFormula] at *; exact typeof_eq_comm hty
  have hrun : runFromEmpty (.cons (.step r args .nil) (.cons (.step .symm .nil (.cons 0 .nil)) .nil)) =
      CState.cons (CStateObj.proven (eqFormula n m))
        (CState.cons (CStateObj.proven (eqFormula m n)) CState.nil) := by
    show __eo_invoke_cmd_list CState.nil (.cons (.step r args .nil) (.cons (.step .symm .nil (.cons 0 .nil)) .nil)) = _
    rw [__eo_invoke_cmd_list, __eo_invoke_cmd] <;> try simp
    rw [hstep, __eo_push_proven, is_bool_type_of (eqFormula_ne_stuck m n) hty, __eo_push_proven_check]
    rw [__eo_invoke_cmd_list, __eo_invoke_cmd_list, __eo_invoke_cmd] <;> try simp
    rw [show __eo_cmd_step_proven (CState.cons (CStateObj.proven (eqFormula m n)) CState.nil) CRule.symm .nil
        (.cons 0 .nil) = eqFormula n m from rfl]
    rw [__eo_push_proven, is_bool_type_of (eqFormula_ne_stuck n m) hty', __eo_push_proven_check]
  refine ⟨CmdListTranslationOk.cons _ _ hT (CmdListTranslationOk.cons _ _ trivial CmdListTranslationOk.nil), ?_, ?_⟩
  · rw [hrun]; rfl
  · rw [hrun]; rfl

/-! ## Each rule's step -/

theorem toEo_spine1 {k : Kind} {op : UserOp} (hk : k.eoShape = .spine (Term.UOp op) (.exactly 1)) (a : Node) :
    (Node.app (.kind k) #[a]).toEo = Term.Apply (Term.UOp op) a.toEo := by
  rw [Node.toEo_app]; simp [Op.eoShape, hk, AppShape.toEo, Arity.accepts]

theorem toEo_spine2 {k : Kind} {op : UserOp} (hk : k.eoShape = .spine (Term.UOp op) (.exactly 2)) (a b : Node) :
    (Node.app (.kind k) #[a, b]).toEo = Term.Apply (Term.Apply (Term.UOp op) a.toEo) b.toEo := by
  rw [Node.toEo_app]; simp [Op.eoShape, hk, AppShape.toEo, Arity.accepts]

theorem toEo_not (a : Node) : (Node.notNode a).toEo = Term.Apply (Term.UOp .not) a.toEo :=
  toEo_spine1 rfl a
theorem toEo_eq (a b : Node) : (Node.eqNode a b).toEo = eqFormula a b :=
  toEo_spine2 rfl a b
theorem toEo_leq (a b : Node) : (Node.mkNode .LEQ #[a, b]).toEo = Term.Apply (Term.Apply (Term.UOp .leq) a.toEo) b.toEo :=
  toEo_spine2 rfl a b
theorem toEo_lt (a b : Node) : (Node.mkNode .LT #[a, b]).toEo = Term.Apply (Term.Apply (Term.UOp .lt) a.toEo) b.toEo :=
  toEo_spine2 rfl a b
theorem toEo_gt (a b : Node) : (Node.mkNode .GT #[a, b]).toEo = Term.Apply (Term.Apply (Term.UOp .gt) a.toEo) b.toEo :=
  toEo_spine2 rfl a b
theorem toEo_geq (a b : Node) : (Node.mkNode .GEQ #[a, b]).toEo = Term.Apply (Term.Apply (Term.UOp .geq) a.toEo) b.toEo :=
  toEo_spine2 rfl a b

/-- `(+ s 1)` for an integer `s` is `(+ s (+ 1 0))`. -/
theorem toEo_succ {s : Node} (hs : s.smtType = SmtType.Int) :
    (Node.mkNode .ADD #[s, .const (.integer 1)]).toEo =
      Term.Apply (Term.Apply (Term.UOp .plus) s.toEo)
        (Term.Apply (Term.Apply (Term.UOp .plus) (Term.Numeral 1)) (Term.Numeral 0)) := by
  rw [Node.mkNode, Node.toEo_app]
  have : __smtx_typeof (__eo_to_smt s.toEo) = SmtType.Int := hs
  simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Nil.eval, typedNil, this, typedNilOfType, eoRightAssocNil,
    eoApp2, Node.toEo, Const.toEo]

theorem toEo_ne_stuck {a : Node} (h : a.smtTypeF ≠ SmtType.None) : a.toEo ≠ .Stuck := by
  intro he
  rw [Node.smtTypeF_eq] at h
  apply h
  show __smtx_typeof (__eo_to_smt a.toEo) = _
  rw [he, show __eo_to_smt Term.Stuck = SmtTerm.None from rfl, __smtx_typeof.eq_def]

end Template

open Template

theorem TRule.step_eq {r : TRule} {args : List Node} {n m : Node} (h : r.Ok args n m) :
    cmdTranslationOk (.step r.rule (TRule.argList args) .nil) ∧
      __eo_cmd_step_proven CState.nil r.rule (TRule.argList args) .nil = eqFormula n m := by
  obtain ⟨hl, hr, -, ha, hi⟩ := h
  have hok : ∀ a ∈ args, eoHasSmtTranslation a.toEo := fun a hm => by
    have := ha a hm; rw [Node.smtTypeF_eq] at this; exact this
  have hns : ∀ a ∈ args, a.toEo ≠ .Stuck := fun a hm => toEo_ne_stuck (ha a hm)
  cases r <;> rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, _⟩⟩⟩ <;>
    simp only [TRule.lhs, Option.some.injEq, reduceCtorEq] at hl
  all_goals (subst hl; simp only [TRule.rhs, Option.some.injEq] at hr; subst hr)
  all_goals refine ⟨by first
    | exact ⟨hok _ (by simp), trivial⟩
    | exact ⟨hok _ (by simp), hok _ (by simp), trivial⟩, ?_⟩
  · -- bool-double-not-elim
    have ha' := hns a (by simp)
    show __eo_prog_bool_double_not_elim a.toEo = _
    unfold __eo_prog_bool_double_not_elim
    split <;> simp_all [eqFormula, eoApp2, toEo_not]
  case eqRefl.cons.nil =>
    have ha' := hns a (by simp)
    show __eo_prog_eq_refl a.toEo = _
    unfold __eo_prog_eq_refl
    split <;> simp_all [eqFormula, eoApp2, toEo_eq, Node.mkTrue, Node.toEo, Const.toEo]
  all_goals have ha' := hns a (by simp)
  all_goals have hb' := hns b (by simp)
  · -- arith-elim-leq
    show __eo_prog_arith_elim_leq a.toEo b.toEo = _
    unfold __eo_prog_arith_elim_leq
    split <;> simp_all [eqFormula, eoApp2, toEo_leq, toEo_geq]
  · -- arith-elim-lt
    show __eo_prog_arith_elim_lt a.toEo b.toEo = _
    unfold __eo_prog_arith_elim_lt
    split <;> simp_all [eqFormula, eoApp2, toEo_lt, toEo_geq, toEo_not]
  · -- arith-elim-gt
    show __eo_prog_arith_elim_gt a.toEo b.toEo = _
    unfold __eo_prog_arith_elim_gt
    split <;> simp_all [eqFormula, eoApp2, toEo_gt, toEo_geq, toEo_not]
  · -- arith-leq-norm
    have hbI : b.smtType = SmtType.Int := by
      have := hi rfl b (by simp); rwa [Node.smtTypeF_eq] at this
    show __eo_prog_arith_leq_norm a.toEo b.toEo = _
    unfold __eo_prog_arith_leq_norm
    split <;> simp_all [eqFormula, eoApp2, toEo_leq, toEo_geq, toEo_not, toEo_succ hbI]
  · -- eq-symm
    show __eo_prog_eq_symm a.toEo b.toEo = _
    unfold __eo_prog_eq_symm
    split <;> simp_all [eqFormula, eoApp2, toEo_eq]

theorem TRule.typeof_of_ok {r : TRule} {args : List Node} {n m : Node} (h : r.Ok args n m) :
    __smtx_typeof (__eo_to_smt (eqFormula n m)) = SmtType.Bool := by
  have := h.2.2.1
  rw [Node.smtTypeF_eq] at this
  rw [← toEo_eq]; exact this

/-- **A template step is a CPC step**, read left to right. -/
theorem TRule.provesEq [LogosFacts] {r : TRule} {args : List Node} {n m : Node} (h : r.Ok args n m) :
    ProvesEq (r.cmds args false) n m := by
  obtain ⟨hT, hs⟩ := TRule.step_eq h
  exact provesEq_one hT hs (TRule.typeof_of_ok h)

/-- **A template step is a CPC step**, read right to left (then `symm`). -/
theorem TRule.provesEq_rev [LogosFacts] {r : TRule} {args : List Node} {n m : Node} (h : r.Ok args m n) :
    ProvesEq (r.cmds args true) n m := by
  obtain ⟨hT, hs⟩ := TRule.step_eq h
  exact provesEq_one_symm hT hs (TRule.typeof_of_ok h)

end Telos
