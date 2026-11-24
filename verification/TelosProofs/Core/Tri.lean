import TelosProofs.Core.CondEquiv
import TelosProofs.Core.QuantCong
import TelosProofs.Core.ChildTyping
import TelosProofs.Core.Semantic

/-!
# Triangular substitution steps are equivalences

`Certified.tri` (`Telos/Core/Tri.lean`): under `TriPlan.Ok n k`, and with its
certified rewrites, `n` is equivalent to `k` (`tri_equiv`).

1. *Closed terms.* The conjuncts the entries come from are closed
   (`groundOrder_closed`), so their truth does not depend on the values of
   variables (`LogosFacts.closed_eval`), and the condition "the entries hold" is
   stable (`StableCond`).
2. *Entries.* Each entry, read off a true conjunct, relates its sides.
3. *Justifications* relate their pairs under the entries with position at least
   their `minPos` (`justs_sound`), by congruence (`CondEquiv.lean`; for
   `distinct`, `DistinctCong.lean`; in the body of a quantifier,
   `QuantCong.lean`), given that the children of a well-typed application are
   well typed (`ChildTyping.lean`).
4. *Chains* relate each conjunct to its result (`chain_sound`).
5. *The step.* By induction from the last conjunct down, each conjunct of the
   result is `Bool` and holds iff the one of `n` does, in every model where the
   later conjuncts of the result hold; so `n` and `k` have the same value.
-/

open Eo Smtm SmtEval

set_option linter.internalConstructors false

namespace Telos

set_option linter.unusedSectionVars false

/-! ## Closed terms -/

/-- `t` is closed in the empty context (Logos's `__eo_is_closed`, without the
`Stuck` case). -/
abbrev ClosedT (t : Term) : Prop := __eo_is_closed_rec t Term.__eo_List_nil = Term.Boolean true

theorem eo_and_tt : __eo_and (Term.Boolean true) (Term.Boolean true) = Term.Boolean true := by
  decide

theorem closed_apply {f x : Term} (hf1 : ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hf2 : ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs) (h1 : ClosedT f) (h2 : ClosedT x) :
    ClosedT (Term.Apply f x) := by
  unfold ClosedT at *
  rw [__eo_is_closed_rec.eq_def]
  split <;> simp_all [eo_and_tt]

theorem closed_of_is_closed {t : Term} (h : __eo_is_closed t = Term.Boolean true) : ClosedT t := by
  unfold __eo_is_closed at h
  split at h
  · simp at h
  · exact h

theorem is_closed_of_closed {t : Term} (hs : t ≠ Term.Stuck) (h : ClosedT t) :
    __eo_is_closed t = Term.Boolean true := by
  unfold __eo_is_closed
  split
  · exact absurd rfl hs
  · exact h

theorem closed_uop (op : UserOp) : ClosedT (Term.UOp op) := by
  unfold ClosedT; rw [__eo_is_closed_rec.eq_def]

theorem closed_numeral (n : native_Int) : ClosedT (Term.Numeral n) := by
  unfold ClosedT; rw [__eo_is_closed_rec.eq_def]

theorem closed_rational (q : native_Rat) : ClosedT (Term.Rational q) := by
  unfold ClosedT; rw [__eo_is_closed_rec.eq_def]

theorem closed_binary (w v : native_Int) : ClosedT (Term.Binary w v) := by
  unfold ClosedT; rw [__eo_is_closed_rec.eq_def]

/-- A closed head of a spine that is not (part of) a quantifier. -/
def SpineHeadOk (h : Term) : Prop :=
  ClosedT h ∧ h ≠ Term.UOp UserOp.forall ∧ h ≠ Term.UOp UserOp.exists ∧
    (∀ vs, h ≠ Term.Apply (Term.UOp UserOp.forall) vs) ∧
    (∀ vs, h ≠ Term.Apply (Term.UOp UserOp.exists) vs)

theorem spineHeadOk_apply {h x : Term} (hh : SpineHeadOk h) (hx : ClosedT x) :
    SpineHeadOk (Term.Apply h x) := by
  obtain ⟨hc, h1, h2, h3, h4⟩ := hh
  refine ⟨closed_apply h3 h4 hc hx, by simp, by simp, fun vs e => ?_, fun vs e => ?_⟩
  · simp only [Term.Apply.injEq] at e; exact h1 e.1
  · simp only [Term.Apply.injEq] at e; exact h2 e.1

theorem closed_spine : ∀ (xs : List Term) {h : Term}, SpineHeadOk h →
    (∀ x ∈ xs, ClosedT x) → ClosedT (xs.foldl Term.Apply h)
  | [], _, hh, _ => hh.1
  | x :: xs, _, hh, hx =>
    closed_spine xs (spineHeadOk_apply hh (hx x (by simp))) (fun y hy => hx y (by simp [hy]))

theorem spineHeadOk_of {h : Term} (hq : headQuantFree h = true)
    (hc : __eo_is_closed h = Term.Boolean true) : SpineHeadOk h := by
  refine ⟨closed_of_is_closed hc, ?_, ?_, ?_, ?_⟩
  · intro e; subst e; simp [headQuantFree] at hq
  · intro e; subst e; simp [headQuantFree] at hq
  · intro vs e; subst e; simp [headQuantFree] at hq
  · intro vs e; subst e; simp [headQuantFree] at hq

/-- The prefixes of a spine with a `headQuantFree` head are not quantifiers. -/
def QHead (h : Term) : Prop :=
  h ≠ Term.UOp UserOp.forall ∧ h ≠ Term.UOp UserOp.exists ∧
    (∀ vs, h ≠ Term.Apply (Term.UOp UserOp.forall) vs) ∧
    (∀ vs, h ≠ Term.Apply (Term.UOp UserOp.exists) vs) ∧
    (∀ vs b, h ≠ Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) b) ∧
    (∀ vs b, h ≠ Term.Apply (Term.Apply (Term.UOp UserOp.exists) vs) b)

theorem qHead_of {h : Term} (hq : headQuantFree h = true) : QHead h := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; subst e; simp [headQuantFree] at hq
  · intro e; subst e; simp [headQuantFree] at hq
  · intro vs e; subst e; simp [headQuantFree] at hq
  · intro vs e; subst e; simp [headQuantFree] at hq
  · intro vs b e; subst e; simp [headQuantFree] at hq
  · intro vs b e; subst e; simp [headQuantFree] at hq

theorem qHead_apply {h x : Term} (hh : QHead h) : QHead (Term.Apply h x) := by
  obtain ⟨h1, h2, h3, h4, _, _⟩ := hh
  refine ⟨by simp, by simp, fun vs e => ?_, fun vs e => ?_, fun vs b e => ?_, fun vs b e => ?_⟩
  · simp only [Term.Apply.injEq] at e; exact h1 e.1
  · simp only [Term.Apply.injEq] at e; exact h2 e.1
  · simp only [Term.Apply.injEq] at e; exact h3 _ e.1
  · simp only [Term.Apply.injEq] at e; exact h4 _ e.1

theorem notTopLevelQuantifier_spine : ∀ (xs : List Term) {h : Term}, QHead h →
    NotTopLevelQuantifier (xs.foldl Term.Apply h)
  | [], _, hh => ⟨hh.2.2.2.2.1, hh.2.2.2.2.2⟩
  | _ :: xs, _, hh => notTopLevelQuantifier_spine xs (qHead_apply hh)

theorem closed_app2 {op : UserOp} (hf : op ≠ UserOp.forall) (he : op ≠ UserOp.exists) {x r : Term}
    (hx : ClosedT x) (hr : ClosedT r) : ClosedT (eoApp2 op x r) := by
  unfold eoApp2
  refine closed_apply (fun vs e => ?_) (fun vs e => ?_) ?_ hr
  · simp only [Term.Apply.injEq, Term.UOp.injEq] at e; exact hf e.1
  · simp only [Term.Apply.injEq, Term.UOp.injEq] at e; exact he e.1
  · exact closed_apply (by simp) (by simp) (closed_uop op) hx

theorem closed_rightAssocNil {op : UserOp} (hf : op ≠ UserOp.forall) (he : op ≠ UserOp.exists)
    {nil : Term} (hn : ClosedT nil) : ∀ (xs : List Term), (∀ x ∈ xs, ClosedT x) →
    ClosedT (eoRightAssocNil op nil xs)
  | [], _ => hn
  | x :: xs, hx =>
    closed_app2 hf he (hx x (by simp)) (closed_rightAssocNil hf he hn xs fun y hy => hx y (by simp [hy]))

/-- The nil of a well-typed chain is well typed. -/
theorem nil_typed {op : UserOp} (hrest : ∀ {x r : Term}, HasSmtType (eoApp2 op x r) → HasSmtType r)
    {nil : Term} : ∀ (xs : List Term), HasSmtType (eoRightAssocNil op nil xs) → HasSmtType nil
  | [], h => h
  | _ :: xs, h => nil_typed hrest xs (hrest h)

theorem closed_typedNil {op : UserOp} (hop : op = UserOp.plus ∨ op = UserOp.mult ∨ op.isBvNary = true)
    (T : SmtType) (h : typedNilOfType op T ≠ Term.Stuck) : ClosedT (typedNilOfType op T) := by
  have key : ∀ t : Term, (t = Term.Stuck ∨ (∃ n, t = Term.Numeral n) ∨ (∃ q, t = Term.Rational q) ∨
      ∃ w v, t = Term.Binary w v) → t ≠ Term.Stuck → ClosedT t := by
    rintro t (rfl | ⟨n, rfl⟩ | ⟨q, rfl⟩ | ⟨w, v, rfl⟩) hs
    · exact absurd rfl hs
    · exact closed_numeral n
    · exact closed_rational q
    · exact closed_binary w v
  refine key _ ?_ h
  simp only [UserOp.isBvNary, Bool.or_eq_true, beq_iff_eq] at hop
  rcases hop with rfl | rfl | ((((rfl | rfl) | rfl) | rfl) | rfl) | rfl <;>
    cases T <;> simp [typedNilOfType]

theorem closed_uconst (i : native_Nat) (T : Term) : ClosedT (Term.UConst i T) := by
  unfold ClosedT; rw [__eo_is_closed_rec.eq_def]

theorem closed_const {c : Const} (h : c.groundOk = true) : ClosedT c.toEo := by
  cases c with
  | dtCons T i =>
    cases T <;> simp [Const.groundOk] at h
    simp only [Const.toEo]; unfold ClosedT; rw [__eo_is_closed_rec.eq_def]
  | dtSel T i j =>
    cases T <;> simp [Const.groundOk] at h
    simp only [Const.toEo]; unfold ClosedT; rw [__eo_is_closed_rec.eq_def]
  | emptySet T => simp [Const.groundOk] at h
  | emptySeq T => simp [Const.groundOk] at h
  | _ => simp only [Const.toEo]; unfold ClosedT; rw [__eo_is_closed_rec.eq_def]

variable [LogosFacts]

/-- The children of a well-typed application below which substitution may go are
well typed. -/
theorem children_typed_subst {op : Op} {cs : Array Node} (hc : op.childrenTypedOfParent = true)
    (h : HasSmtType (Node.app op cs).toEo) : ∀ c ∈ cs.toList, HasSmtType c.toEo :=
  ChildTyping.children_wellTyped hc h

theorem substCongruent_ne {op : UserOp} {nil : Nil}
    (h : (AppShape.rightAssocNil op nil).substCongruent = true) :
    op ≠ UserOp.forall ∧ op ≠ UserOp.exists := by
  constructor <;> (intro e; subst e; cases nil <;>
    simp [AppShape.substCongruent, UserOp.isReNary, UserOp.isTypedNary, UserOp.isBvNary] at h)

/-- **Ground nodes are closed.** Every well-typed node of a well-formed order is
closed. -/
theorem groundOrder_closed (order : Array GroundItem)
    (hok : ∀ g, g < order.size → groundItemOk order g = true) :
    ∀ g (hg : g < order.size), HasSmtType order[g].node.toEo → ClosedT order[g].node.toEo := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro hg ht
  have hg' := hok g hg
  simp only [groundItemOk, Array.getElem?_eq_getElem hg, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true, List.mem_range] at hg'
  obtain ⟨⟨hloc, hsz⟩, hkids⟩ := hg'
  -- the children are closed, when well typed
  have hch : ∀ c ∈ order[g].node.getChildren.toList, HasSmtType c.toEo → ClosedT c.toEo := by
    intro c hc htc
    obtain ⟨t, ht', hct⟩ := List.getElem_of_mem hc
    have htk : t < order[g].kids.size := by rw [hsz]; simpa using ht'
    have := hkids t htk
    rw [Array.getElem?_eq_getElem htk,
      Array.getElem?_eq_getElem (by simpa using ht' : t < order[g].node.getChildren.size)] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨hkg, hk⟩ := this
    have hkn : order[g].kids[t] < order.size := Nat.lt_trans hkg hg
    rw [Array.getElem?_eq_getElem hkn] at hk
    simp only [Option.map_some, Option.getD_some, beq_iff_eq] at hk
    have hc' : c = order[order[g].kids[t]].node := by
      rw [hk, ← hct]; simp
    subst hc'
    exact ih _ hkg hkn htc
  generalize order[g].node = u at hloc ht hch
  cases u with
  | const c => simp only [Node.toEo]; exact closed_const (by simpa [Node.groundLocal] using hloc)
  | var n T => simp only [Node.toEo]; exact closed_uconst _ _
  | boundVar => simp [Node.groundLocal] at hloc
  | skolem => simp [Node.groundLocal] at hloc
  | app op cs =>
    have htc := children_typed_subst (by
      simp only [Node.groundLocal, Op.substOk, Bool.and_eq_true] at hloc; exact hloc.1.2) ht
    have hcl : ∀ x ∈ cs.toList.map Node.toEo, ClosedT x := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
      exact hch c (by simpa [Node.getChildren] using hc) (htc c hc)
    rw [Node.toEo_app] at ht ⊢
    simp only [Node.groundLocal, Op.substOk, Bool.and_eq_true] at hloc
    obtain ⟨⟨hsc, _⟩, hsh⟩ := hloc
    generalize op.eoShape = sh at hsc hsh ht ⊢
    cases sh with
    | spine head arity =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hsh
      simp only [AppShape.toEo, List.length_map, Array.length_toList, hsh.1, ite_true] at ht ⊢
      exact closed_spine _ (spineHeadOk_of hsc hsh.2) hcl
    | rightAssocNil op' nil =>
      obtain ⟨hf, he⟩ := substCongruent_ne hsc
      cases nil with
      | const t =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsh
        simp only [AppShape.toEo, List.length_map, Array.length_toList, hsh.1, ite_true,
          Nil.eval] at ht ⊢
        exact closed_rightAssocNil hf he (closed_of_is_closed hsh.2) _ hcl
      | typed =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hsh
        simp only [AppShape.toEo, List.length_map, Array.length_toList, hsh.1, ite_true,
          Nil.eval] at ht ⊢
        simp only [AppShape.substCongruent, Bool.or_eq_true, beq_iff_eq] at hsc
        have hrest : ∀ {x r : Term}, HasSmtType (eoApp2 op' x r) → HasSmtType r := by
          rcases hsc with hpm | hty
          · exact translation_rest_arith hpm
          · exact fun h => (typed_nary_args hty h).2
        have hnil := nil_typed hrest _ ht
        have hop : op' = UserOp.plus ∨ op' = UserOp.mult ∨ op'.isBvNary = true := by
          rcases hsc with (h | h) | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · simp only [UserOp.isTypedNary, Bool.or_eq_true, beq_iff_eq] at h
            exact Or.inr (Or.inr (h.resolve_right hsh.2))
        refine closed_rightAssocNil hf he ?_ _ hcl
        exact closed_typedNil hop _ (fun e => not_translation_stuck (by unfold typedNil at hnil; rw [e] at hnil; exact hnil))
    | none =>
      simp only [AppShape.toEo] at ht; exact absurd ht ChildTyping.typed_stuck
    | typedList _ => simp at hsh
    | _ => simp [AppShape.substCongruent] at hsc

/-! ## Booleans -/

omit [LogosFacts] in
theorem toEo_eqNode (a b : Node) :
    (Node.app (.kind .EQUAL) #[a, b]).toEo = mkEq a.toEo b.toEo := by
  rw [Node.toEo_app]; simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts, mkEq, eoApp2]

omit [LogosFacts] in
theorem toEo_notNode (a : Node) :
    (Node.app (.kind .NOT) #[a]).toEo = Term.Apply (Term.UOp UserOp.not) a.toEo := by
  rw [Node.toEo_app]; simp [Op.eoShape, Kind.eoShape, AppShape.toEo, Arity.accepts]

omit [LogosFacts] in
theorem typeof_not_bool (a : SmtTerm) (h : __smtx_typeof (SmtTerm.not a) = SmtType.Bool) :
    __smtx_typeof a = SmtType.Bool := by
  rw [__smtx_typeof.eq_def] at h
  simp only [native_ite, native_Teq] at h
  by_cases ha : __smtx_typeof a = SmtType.Bool
  · exact ha
  · simp [ha] at h

omit [LogosFacts] in
theorem typeof_false : __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def]

omit [LogosFacts] in
theorem eval_false (M : SmtModel) :
    __smtx_model_eval M (SmtTerm.Boolean false) = SmtValue.Boolean false := by
  rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
theorem valueRel_bool {a b : Bool} (h : SmtValueRel (SmtValue.Boolean a) (SmtValue.Boolean b)) :
    a = b := by
  unfold SmtValueRel __smtx_model_eval_eq at h
  simp only [SmtValue.Boolean.injEq, native_veq] at h
  simpa using h

/-! ## Entries -/

/-- The entries of `P` with position after `i` hold in `M`. -/
def EntriesHold (P : TriPlan) (k : Node) (i : Nat) (M : SmtModel) : Prop :=
  ∀ e ∈ P.entries.toList, i < e.pos → ∀ d, TriPlan.conj k e.pos = some d → TrueIn M d.toEo

/-- The conjuncts of `k` after `i` are Boolean. -/
def LaterBool (k : Node) (i : Nat) : Prop :=
  ∀ j, i < j → ∀ d, TriPlan.conj k j = some d → HasBoolType d.toEo

theorem hasSmtType_of_bool {t : Term} (h : HasBoolType t) : HasSmtType t := by
  unfold HasSmtType; unfold HasBoolType at h; rw [h]; simp

/-- The conjunct of an entry is ground, so closed. -/
theorem entry_closed {P : TriPlan} {k : Node} {e : Entry} (hG : ∀ g, g < P.ground.size → groundItemOk P.ground g = true)
    (he : P.entryOk k e = true) {d : Node} (hd : TriPlan.conj k e.pos = some d)
    (ht : HasSmtType d.toEo) : __eo_is_closed d.toEo = Term.Boolean true := by
  unfold TriPlan.entryOk at he
  rw [hd] at he
  split at he
  · rename_i d' g hd' hg
    cases hd'
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    obtain ⟨hgs, hgv⟩ := Array.getElem?_eq_some_iff.1 hg
    have hc := groundOrder_closed P.ground hG e.ground hgs (by rw [hgv, he.1]; exact ht)
    rw [hgv, he.1] at hc
    exact is_closed_of_closed (fun e => not_translation_stuck (e ▸ ht)) hc
  · simp at he

/-- **The condition is stable**: the conjuncts of the entries are closed. -/
theorem entriesHold_stable {P : TriPlan} {k : Node} {i : Nat}
    (hG : ∀ g, g < P.ground.size → groundItemOk P.ground g = true)
    (hE : ∀ e ∈ P.entries.toList, P.entryOk k e = true) (hT : LaterBool k i) :
    StableCond (EntriesHold P k i) := by
  intro M N _ _ hAgree hM e he hi d hd
  have hc := entry_closed hG (hE e he) hd (hasSmtType_of_bool (hT e.pos hi d hd))
  unfold TrueIn
  rw [← LogosFacts.closed_eval _ hc M N hAgree]
  exact hM e he hi d hd

/-- **An entry relates its sides**, in every model where its conjunct holds. -/
theorem entry_sound {P : TriPlan} {k : Node} {e : Entry} (he : P.entryOk k e = true)
    {d : Node} (hd : TriPlan.conj k e.pos = some d) (ht : HasBoolType d.toEo) :
    HasBoolType (mkEq e.lhs.toEo e.rhs.toEo) ∧
      ∀ M, model_wf M → TrueIn M d.toEo → TrueIn M (mkEq e.lhs.toEo e.rhs.toEo) := by
  unfold TriPlan.entryOk at he
  rw [hd] at he
  split at he
  · rename_i d' g hd' _
    cases hd'
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at he
    rcases he.2 with ((h1 | h2) | ⟨h3, h3'⟩) | ⟨h4, h4'⟩
    · subst h1; rw [toEo_eqNode] at ht; exact ⟨ht, fun M _ h => by rwa [toEo_eqNode] at h⟩
    · subst h2
      rw [toEo_eqNode] at ht
      obtain ⟨hn, heq⟩ := (hasBoolType_mkEq_iff _ _).1 ht
      refine ⟨(hasBoolType_mkEq_iff _ _).2 ⟨fun h => hn (heq.trans h), heq.symm⟩, fun M _ h => ?_⟩
      rw [toEo_eqNode] at h
      exact (trueIn_mkEq_iff _ _ _).2 (LogosFacts.value_rel_symm _ _ ((trueIn_mkEq_iff _ _ _).1 h))
    · subst h3; rw [h3']
      have hb : HasBoolType (Node.const (.boolean true)).toEo := by
        simp [HasBoolType, Node.toEo, Const.toEo]; exact typeof_true
      refine ⟨(hasBoolType_mkEq_iff _ _).2 ⟨hasSmtType_of_bool ht, ht.trans hb.symm⟩, fun M _ h => ?_⟩
      refine (trueIn_mkEq_iff _ _ _).2 ?_
      have : __smtx_model_eval M (__eo_to_smt (Node.const (.boolean true)).toEo) = SmtValue.Boolean true := by
        simp [Node.toEo, Const.toEo]; exact eval_true M
      unfold TrueIn at h
      rw [h, this]; exact LogosFacts.value_rel_refl _
    · subst h4; rw [h4']
      rw [toEo_notNode] at ht
      have hl : HasBoolType e.lhs.toEo := typeof_not_bool _ ht
      have hb : HasBoolType (Node.const (.boolean false)).toEo := by
        simp [HasBoolType, Node.toEo, Const.toEo]; exact typeof_false
      refine ⟨(hasBoolType_mkEq_iff _ _).2 ⟨hasSmtType_of_bool hl, hl.trans hb.symm⟩, fun M hM h => ?_⟩
      rw [toEo_notNode] at h
      obtain ⟨b, hb'⟩ := LogosFacts.eval_bool M _ hM hl
      unfold TrueIn at h
      change __smtx_model_eval M (SmtTerm.not _) = _ at h
      rw [model_eval_not_eq, hb'] at h
      simp only [__smtx_model_eval_not, native_not, SmtValue.Boolean.injEq] at h
      refine (trueIn_mkEq_iff _ _ _).2 ?_
      have hf : __smtx_model_eval M (__eo_to_smt (Node.const (.boolean false)).toEo) = SmtValue.Boolean false := by
        simp [Node.toEo, Const.toEo]; exact eval_false M
      rw [hb', hf]
      cases b <;> simp at h
      exact LogosFacts.value_rel_refl _
  · simp at he

/-! ## Congruence of shapes -/

theorem shape_condCongr {Φ : SmtModel → Prop} (hΦ : StableCond Φ) (sh : AppShape)
    (hsh : sh.substCongruent = true) {xs ys : List Term} (h : List.Forall₂ (CondEquiv Φ) xs ys)
    (ht : HasSmtType (sh.toEo xs)) : CondEquiv Φ (sh.toEo xs) (sh.toEo ys) := by
  have hlen := h.length_eq
  cases sh with
  | spine head arity =>
    by_cases hacc : arity.accepts xs.length = true
    · have hacc' : arity.accepts ys.length = true := hlen ▸ hacc
      rw [AppShape.toEo, ite_eq_left hacc] at ht
      rw [AppShape.toEo, AppShape.toEo, ite_eq_left hacc, ite_eq_left hacc']
      exact condEquiv_spine hΦ head h ht (notTopLevelQuantifier_spine xs (qHead_of hsh))
    · rw [AppShape.toEo, ite_eq_right hacc] at ht
      exact absurd ht not_translation_stuck
  | rightAssocNil op nil =>
    obtain ⟨hf, he⟩ := substCongruent_ne hsh
    by_cases hle : 2 ≤ xs.length
    · have hle' : 2 ≤ ys.length := hlen ▸ hle
      rw [AppShape.toEo, ite_eq_left hle] at ht
      rw [AppShape.toEo, AppShape.toEo, ite_eq_left hle, ite_eq_left hle']
      have hnil : nil.eval op (ys.headD Term.Stuck) = nil.eval op (xs.headD Term.Stuck) := by
        cases nil with
        | const _ => rfl
        | typed =>
          cases h with
          | nil => simp at hle
          | cons hxy _ => exact (CondEquiv.typedNil_congr op hxy).symm
      rw [hnil]
      have hrest : ∀ {x r : Term}, HasSmtType (eoApp2 op x r) → HasSmtType r := by
        cases nil with
        | const _ =>
          simp only [AppShape.substCongruent, Bool.or_eq_true, beq_iff_eq] at hsh
          rcases hsh with hsh | hre
          · exact translation_rest hsh
          · exact translation_rest_re hre
        | typed =>
          simp only [AppShape.substCongruent, Bool.or_eq_true, beq_iff_eq] at hsh
          rcases hsh with hsh | hbv
          · exact translation_rest_arith hsh
          · exact fun h => (typed_nary_args hbv h).2
      exact condEquiv_rightAssocNil hΦ op hf he _ hrest h ht
    · rw [AppShape.toEo, ite_eq_right hle] at ht
      exact absurd ht not_translation_stuck
  | typedList op =>
    simp only [AppShape.substCongruent, beq_iff_eq] at hsh
    subst hsh
    exact condEquiv_distinct h ht
  | none => simp only [AppShape.toEo] at ht; exact absurd ht ChildTyping.typed_stuck
  | _ => simp [AppShape.substCongruent] at hsh

/-! ## Justifications -/

theorem bodyOk_inv {a b : Node} {K : Just} (h : Just.bodyOk a b K = true) :
    ∃ q cs ds, a = .app (.kind q) cs ∧ b = .app (.kind q) ds ∧ (q = .FORALL ∨ q = .EXISTS) ∧
      cs.size = ds.size ∧ cs[0]? = ds[0]? ∧ cs[1]? = some K.a ∧ ds[1]? = some K.b := by
  unfold Just.bodyOk at h
  split at h
  · simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hq, rfl, hsz, h0, -, h1, h1'⟩ := h
    exact ⟨_, _, _, rfl, rfl, hq, hsz, h0, h1, h1'⟩
  · simp at h

/-- The translations of two quantifiers with the same variables. -/
theorem quant_toEo_pair {q : Kind} (hq : q = .FORALL ∨ q = .EXISTS) {cs ds : Array Node}
    (hsz : cs.size = ds.size) (h0 : cs[0]? = ds[0]?)
    {B B' : Node} (h1 : cs[1]? = some B) (h1' : ds[1]? = some B')
    (ht : HasSmtType (Node.app (.kind q) cs).toEo) :
    ∃ op X, IsQuant op ∧ (Node.app (.kind q) cs).toEo = eoApp2 op X B.toEo ∧
      (Node.app (.kind q) ds).toEo = eoApp2 op X B'.toEo := by
  obtain ⟨op, hop, hsh⟩ : ∃ op, IsQuant op ∧ q.eoShape = .binder op := by
    rcases hq with rfl | rfl
    exacts [⟨_, .inl rfl, rfl⟩, ⟨_, .inr rfl, rfl⟩]
  rw [Node.toEo_app] at ht ⊢; rw [Node.toEo_app]
  simp only [Op.eoShape, hsh] at ht ⊢
  obtain ⟨l⟩ := cs; obtain ⟨m⟩ := ds
  simp only [List.size_toArray] at hsz
  simp only [List.getElem?_toArray] at h0 h1 h1'
  rcases l with _ | ⟨v, _ | ⟨b, _ | ⟨p, _ | ⟨r, rest⟩⟩⟩⟩ <;> simp at h1
  all_goals rcases m with _ | ⟨v', _ | ⟨b', _ | ⟨p', _ | ⟨r', rest'⟩⟩⟩⟩ <;> simp at hsz h1' h0
  all_goals first
    | (simp only [List.map, AppShape.toEo] at ht; exact absurd ht ChildTyping.typed_stuck)
    | (subst h0 h1 h1'; exact ⟨op, v.toEo, hop, by simp [AppShape.toEo], by simp [AppShape.toEo]⟩)

theorem justs_sound (P : TriPlan) (k : Node)
    (hJ : ∀ j, j < P.justs.size → P.justOk j = true)
    (hE : ∀ e ∈ P.entries.toList, P.entryOk k e = true)
    (hG : ∀ g, g < P.ground.size → groundItemOk P.ground g = true)
    (i : Nat) (hT : LaterBool k i) :
    ∀ j (hj : j < P.justs.size), i < P.justs[j].minPos → HasSmtType P.justs[j].a.toEo →
      CondEquiv (EntriesHold P k i) P.justs[j].a.toEo P.justs[j].b.toEo := by
  have hΦ := entriesHold_stable hG hE hT
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj hmin ha
  have hok := hJ j hj
  unfold TriPlan.justOk at hok
  rw [Array.getElem?_eq_getElem hj] at hok
  generalize P.justs[j] = J at hok hmin ha ⊢
  obtain ⟨a, b, minPos, kind⟩ := J
  simp only at hok hmin ha ⊢
  cases kind with
  | refl =>
    simp only [beq_iff_eq] at hok
    subst hok; exact CondEquiv.refl _ ha
  | entry e k' =>
    simp only at hok
    cases hE' : P.entries[e]? with
    | none => rw [hE'] at hok; simp at hok
    | some E =>
    cases hK' : P.justs[k']? with
    | none => rw [hE', hK'] at hok; simp at hok
    | some K =>
    rw [hE', hK'] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨hk, hl⟩, hr⟩, hb⟩, hp⟩, hm⟩ := hok
    obtain ⟨hes, hEv⟩ := Array.getElem?_eq_some_iff.1 hE'
    obtain ⟨hks, hKv⟩ := Array.getElem?_eq_some_iff.1 hK'
    have hmem : E ∈ P.entries.toList := by rw [← hEv]; exact Array.getElem_mem_toList hes
    have hpos : i < E.pos := Nat.lt_of_lt_of_le hmin hp
    have hok' := hE E hmem
    have hd : ∃ d, TriPlan.conj k E.pos = some d := by
      unfold TriPlan.entryOk at hok'
      cases hc : TriPlan.conj k E.pos with
      | none => rw [hc] at hok'; simp at hok'
      | some d => exact ⟨d, rfl⟩
    obtain ⟨d, hd⟩ := hd
    obtain ⟨hty, htr⟩ := entry_sound hok' hd (hT E.pos hpos d hd)
    have h₁ : CondEquiv (EntriesHold P k i) a.toEo E.rhs.toEo := by
      rw [← hl]
      exact ⟨hty, fun M hM hH => htr M hM (hH E hmem hpos d hd)⟩
    have h₂ := ih k' hk hks (by rw [hKv]; exact Nat.lt_of_lt_of_le hmin hm)
      (by rw [hKv, hr]; exact h₁.typed_right)
    rw [hKv, hr, hb] at h₂
    exact h₁.trans h₂
  | body k' =>
    simp only at hok
    cases hK' : P.justs[k']? with
    | none => rw [hK'] at hok; simp at hok
    | some K =>
    rw [hK'] at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hk, hm⟩, hbody⟩ := hok
    obtain ⟨q, cs, ds, rfl, rfl, hq, hsz, h0, h1, h1'⟩ := bodyOk_inv hbody
    obtain ⟨hks, hKv⟩ := Array.getElem?_eq_some_iff.1 hK'
    obtain ⟨op, X, hop, ea, eb⟩ := quant_toEo_pair hq hsz h0 h1 h1' ha
    rw [ea] at ha ⊢; rw [eb]
    have hBt : HasSmtType K.a.toEo := by
      have := quant_body_bool hop ha; unfold HasSmtType; rw [this]; simp
    have hB := ih k' hk hks (by rw [hKv]; exact Nat.lt_of_lt_of_le hmin hm) (by rw [hKv]; exact hBt)
    rw [hKv] at hB
    exact condEquiv_quant hΦ hop hB ha
  | congr ks =>
    simp only at hok
    rcases a with ⟨_⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨op, cs⟩ <;>
      rcases b with ⟨_⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ | ⟨op', ds⟩ <;> simp only [Bool.false_eq_true] at hok
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hok
    obtain ⟨⟨⟨⟨hop, hsub⟩, hsz⟩, hks⟩, hall⟩ := hok
    subst hop
    have htc := children_typed_subst (by
      simp only [Op.substOk, Bool.and_eq_true] at hsub; exact hsub.2) ha
    rw [Node.toEo_app] at ha ⊢; rw [Node.toEo_app]
    refine shape_condCongr hΦ _ (by simp only [Op.substOk, Bool.and_eq_true] at hsub; exact hsub.1) ?_ ha
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_iff_get]
    refine ⟨by simpa using hsz, fun t h₁ h₂ => ?_⟩
    have ht : t < ks.size := by rw [hks]; simpa using h₁
    have htc' : t < cs.size := by simpa using h₁
    have htd : t < ds.size := by simpa using h₂
    have := hall t ht
    rw [Array.getElem?_eq_getElem ht, Array.getElem?_eq_getElem htc',
      Array.getElem?_eq_getElem htd] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨hkj, hk⟩ := this
    have hkn : ks[t] < P.justs.size := Nat.lt_trans hkj hj
    rw [Array.getElem?_eq_getElem hkn] at hk
    simp only [Option.map_some, Option.getD_some, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hk
    obtain ⟨⟨hka, hkb⟩, hkm⟩ := hk
    have := ih ks[t] hkj hkn (Nat.lt_of_lt_of_le hmin hkm)
      (by rw [hka]; exact htc _ (by simp))
    rw [hka, hkb] at this
    simpa using this

/-! ## Chains -/

theorem foldl_none (P : TriPlan) (i : Nat) (steps : List ChainStep) :
    steps.foldl (fun acc s => acc.bind fun cur =>
      (P.stepEnds i s).bind fun (a, b) => if a == cur then some b else none) none = none := by
  induction steps with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem chain_fold_sound (P : TriPlan) (k : Node) (i : Nat)
    (hJs : ∀ j (hj : j < P.justs.size), i < P.justs[j].minPos → HasSmtType P.justs[j].a.toEo →
      CondEquiv (EntriesHold P k i) P.justs[j].a.toEo P.justs[j].b.toEo)
    (hrw : ∀ r (hr : r < P.rws.size), P.rws[r].1.WellTyped → P.rws[r].1.Equiv P.rws[r].2) :
    ∀ (steps : List ChainStep) (cur e : Node), HasSmtType cur.toEo →
      steps.foldl (fun acc s => acc.bind fun cur =>
        (P.stepEnds i s).bind fun (a, b) => if a == cur then some b else none) (some cur) = some e →
      CondEquiv (EntriesHold P k i) cur.toEo e.toEo := by
  intro steps
  induction steps with
  | nil => intro cur e hc h; cases h; exact CondEquiv.refl _ hc
  | cons s rest ih =>
    intro cur e hc h
    simp only [List.foldl_cons, Option.bind_some] at h
    cases hs : P.stepEnds i s with
    | none => rw [hs] at h; simp only [Option.bind_none] at h; rw [foldl_none] at h; cases h
    | some ab =>
      obtain ⟨a, b⟩ := ab
      rw [hs] at h
      simp only [Option.bind_some] at h
      by_cases hac : a = cur
      · subst hac
        simp only [beq_self_eq_true, ite_true] at h
        have h₁ : CondEquiv (EntriesHold P k i) a.toEo b.toEo := by
          cases s with
          | subst j =>
            simp only [TriPlan.stepEnds] at hs
            cases hJ : P.justs[j]? with
            | none => rw [hJ] at hs; cases hs
            | some J =>
              rw [hJ] at hs
              simp only [Option.bind_some] at hs
              split at hs
              · rename_i hm
                cases hs
                have hjs := (Array.getElem?_eq_some_iff.1 hJ).1
                have hJv := (Array.getElem?_eq_some_iff.1 hJ).2
                have := hJs j hjs (by rw [hJv]; omega) (by rw [hJv]; exact hc)
                rw [hJv] at this; exact this
              · cases hs
          | rw r =>
            simp only [TriPlan.stepEnds] at hs
            have hrs := (Array.getElem?_eq_some_iff.1 hs).1
            have hrv := (Array.getElem?_eq_some_iff.1 hs).2
            have := hrw r hrs (by rw [hrv]; exact hc)
            rw [hrv] at this
            exact CondEquiv.of_equiv this
        exact h₁.trans (ih b e h₁.typed_right h)
      · have : (a == cur) = false := by simpa using hac
        rw [this] at h; simp only [Bool.false_eq_true, ite_false] at h
        rw [foldl_none] at h; cases h

/-! ## The step -/

omit [LogosFacts] in
theorem TriPlan.ok_shape {P : TriPlan} {n k : Node} (h : P.Ok n k = true) :
    ∃ cs ds, n = .app (.kind .AND) cs ∧ k = .app (.kind .AND) ds := by
  unfold TriPlan.Ok at h
  split at h
  · exact ⟨_, _, rfl, rfl⟩
  · simp at h

theorem trueIn_of_mkEq {M : SmtModel} {a b : Term} (hM : model_wf M) (hb : HasBoolType b)
    (h : TrueIn M (mkEq a b)) (ha : TrueIn M a) : TrueIn M b := by
  obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM hb
  have := (trueIn_mkEq_iff M a b).1 h
  unfold TrueIn at ha ⊢
  rw [ha, hc] at this
  rw [hc, ← valueRel_bool this]

theorem trueIn_of_mkEq' {M : SmtModel} {a b : Term} (hM : model_wf M) (ha : HasBoolType a)
    (h : TrueIn M (mkEq a b)) (hb : TrueIn M b) : TrueIn M a := by
  refine trueIn_of_mkEq hM ha ((trueIn_mkEq_iff M b a).2 ?_) hb
  exact LogosFacts.value_rel_symm _ _ ((trueIn_mkEq_iff M a b).1 h)

/-- A conjunction of at least two conjuncts: its type and value from theirs. -/
theorem and_bool_iff (cs : Array Node) (h : 2 ≤ cs.size) :
    HasBoolType (Node.app (.kind .AND) cs).toEo ↔ ∀ i (hi : i < cs.size), HasBoolType cs[i].toEo := by
  rw [toEo_and cs h]
  unfold HasBoolType
  rw [typeof_andChain]
  constructor
  · intro hall i hi; exact hall _ (List.mem_map_of_mem (Array.getElem_mem_toList hi))
  · intro hall x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    exact hall i (by simpa using hi) |>.trans (by simp)

theorem and_true_iff (cs : Array Node) (h : 2 ≤ cs.size) (M : SmtModel) (hM : model_wf M)
    (hb : ∀ i (hi : i < cs.size), HasBoolType cs[i].toEo) :
    TrueIn M (Node.app (.kind .AND) cs).toEo ↔ ∀ i (hi : i < cs.size), TrueIn M cs[i].toEo := by
  unfold TrueIn
  rw [toEo_and cs h, eval_andChain M hM _ (by
    intro x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    simpa [HasBoolType] using hb i (by simpa using hi))]
  constructor
  · intro hall i hi; exact hall _ (List.mem_map_of_mem (Array.getElem_mem_toList hi))
  · intro hall x hx
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    simpa using hall i (by simpa using hi)

/-- **Triangular substitution steps are equivalences.** -/
theorem tri_equiv (P : TriPlan) (cs ds : Array Node)
    (hok : P.Ok (.app (.kind .AND) cs) (.app (.kind .AND) ds) = true)
    (hrw : ∀ r (hr : r < P.rws.size), P.rws[r].1.WellTyped → P.rws[r].1.Equiv P.rws[r].2)
    (hn : (Node.app (.kind .AND) cs).WellTyped) :
    (Node.app (.kind .AND) cs).Equiv (.app (.kind .AND) ds) := by
  let k : Node := .app (.kind .AND) ds
  simp only [TriPlan.Ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨h2, hsz⟩, _⟩, hG⟩, hE⟩, hJ⟩, hC⟩ := hok
  have h2' : 2 ≤ ds.size := hsz ▸ h2
  have hconj : ∀ j, TriPlan.conj k j = ds[j]? := fun _ => rfl
  have hcb : ∀ i (hi : i < cs.size), HasBoolType cs[i].toEo :=
    (and_bool_iff cs h2).1 (and_smtType_bool cs hn)
  -- each conjunct, from the last down
  have claim : ∀ m i (hi : i < cs.size), cs.size - i = m →
      HasBoolType (ds[i]'(hsz ▸ hi)).toEo ∧
        CondEquiv (EntriesHold P k i) cs[i].toEo (ds[i]'(hsz ▸ hi)).toEo := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro i hi hm
    have hT : LaterBool k i := by
      intro j hj d hd
      rw [hconj] at hd
      obtain ⟨hjs, rfl⟩ := Array.getElem?_eq_some_iff.1 hd
      exact (ih (cs.size - j) (by omega) j (hsz ▸ hjs) rfl).1
    have hc := hC i hi
    rw [Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem (hsz ▸ hi)] at hc
    simp only at hc
    unfold TriPlan.chainOk at hc
    cases hst : P.chains[i]? with
    | none => rw [hst] at hc; simp at hc
    | some steps =>
      rw [hst] at hc
      simp only at hc
      split at hc
      · rename_i e he
        simp only [beq_iff_eq] at hc
        subst hc
        rw [← Array.foldl_toList] at he
        have hJs := justs_sound P k hJ hE hG i hT
        have h := chain_fold_sound P k i hJs hrw steps.toList cs[i] _
          (hasSmtType_of_bool (hcb i hi)) he
        refine ⟨?_, h⟩
        unfold HasBoolType; rw [← h.type_eq]; exact hcb i hi
      · simp at hc
  have hdb : ∀ i (hi : i < ds.size), HasBoolType ds[i].toEo :=
    fun i hi => (claim _ i (hsz ▸ hi) rfl).1
  have hkb : HasBoolType k.toEo := (and_bool_iff ds h2').2 hdb
  have hnb : HasBoolType (Node.app (.kind .AND) cs).toEo := and_smtType_bool cs hn
  refine (Node.equiv_iff _ _).2 ⟨hn, ?_, fun M hM => ?_⟩
  · exact hnb.trans hkb.symm
  · have fwd : (∀ i (hi : i < cs.size), TrueIn M cs[i].toEo) →
        ∀ i (hi : i < ds.size), TrueIn M ds[i].toEo := by
      intro hall
      have : ∀ m i (hi : i < ds.size), ds.size - i = m → TrueIn M ds[i].toEo := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ih =>
        intro i hi hm
        have hH : EntriesHold P k i M := by
          intro e _ hpos d hd
          rw [hconj] at hd
          obtain ⟨hjs, rfl⟩ := Array.getElem?_eq_some_iff.1 hd
          exact ih (ds.size - e.pos) (by omega) e.pos hjs rfl
        have hce := (claim _ i (hsz.symm ▸ hi) rfl).2
        exact trueIn_of_mkEq hM (hdb i hi) (hce.2 M hM hH) (hall i (hsz.symm ▸ hi))
      exact fun i hi => this _ i hi rfl
    have bwd : (∀ i (hi : i < ds.size), TrueIn M ds[i].toEo) →
        ∀ i (hi : i < cs.size), TrueIn M cs[i].toEo := by
      intro hall i hi
      have hH : EntriesHold P k i M := by
        intro e _ _ d hd
        rw [hconj] at hd
        obtain ⟨hjs, rfl⟩ := Array.getElem?_eq_some_iff.1 hd
        exact hall e.pos hjs
      have hce := (claim _ i hi rfl).2
      exact trueIn_of_mkEq' hM (hcb i hi) (hce.2 M hM hH) (hall i (hsz ▸ hi))
    have hn' := and_true_iff cs h2 M hM hcb
    have hk' := and_true_iff ds h2' M hM hdb
    obtain ⟨b, hb⟩ := LogosFacts.eval_bool M _ hM hnb
    obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM hkb
    have hiff : b = true ↔ c = true := by
      unfold TrueIn at hn' hk'
      rw [hb] at hn'; rw [hc] at hk'
      simp only [SmtValue.Boolean.injEq] at hn' hk'
      rw [hn', hk']
      exact ⟨fwd, bwd⟩
    have : b = c := by cases b <;> cases c <;> simp_all
    change SmtValueRel (__smtx_model_eval M (__eo_to_smt (Node.app (.kind .AND) cs).toEo))
      (__smtx_model_eval M (__eo_to_smt k.toEo))
    rw [hb, hc, this]
    exact LogosFacts.value_rel_refl _

end Telos
