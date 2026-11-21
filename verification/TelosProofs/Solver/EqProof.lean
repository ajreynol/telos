import TelosProofs.Core.Learn
import TelosProofs.Rewriter.Rewriter
import Telos.Solver.EqProof

/-!
# Equality proofs are sound

`EqProof.check A p = some (a, b)` (`Telos/Solver/EqProof.lean`): if the
assumptions `A` are Boolean, and the condition that they hold is stable (they
are closed), then `(= a b)` is well typed and true in every well-formed model
of `A` (`check_sound`). So a conflict, a proof of `(true, false)`, means that
no well-formed model satisfies `A` (`checkConflict_sound`).

The cases:
- `assume`: the assumption `(= a b)` is the equation; `(not x)` makes `x`
  false; another literal is true;
- `symm`, `trans`: `CondEquiv` is symmetric and transitive;
- `cong`: the application at the path is well typed, as a subterm of a
  well-typed assumption below operators whose children are well typed when
  they are (`ChildTyping.children_wellTyped`). So are its children, and the
  arguments are related pairwise (by reflexivity for those without a proof).
  Then congruence under a stable condition (`shape_condCongr`) relates the
  applications;
- `eqTrue`: an equation true in a model makes `(= a b)` evaluate to `true`;
- `rw`: the rewriter is correct (`rewrite_correct_of_logos`).
-/

open Eo Smtm SmtEval

namespace Telos.Solver

set_option linter.unusedSectionVars false

variable [LogosFacts]

/-- The assumptions hold in `M`. -/
def Holds (A : Array Node) (M : SmtModel) : Prop := ∀ l ∈ A.toList, TrueIn M l.toEo

theorem condEquiv_symm {Φ : SmtModel → Prop} {a b : Term} (h : CondEquiv Φ a b) :
    CondEquiv Φ b a :=
  ⟨(hasBoolType_mkEq_iff b a).2 ⟨h.typed_right, h.type_eq.symm⟩,
    fun M hM hΦ => (trueIn_mkEq_iff M b a).2
      (LogosFacts.value_rel_symm _ _ ((trueIn_mkEq_iff M a b).1 (h.2 M hM hΦ)))⟩

omit [LogosFacts] in
theorem toEo_true : (Node.mkTrue).toEo = Term.Boolean true := by
  simp [Node.mkTrue, Node.toEo, Const.toEo]

omit [LogosFacts] in
theorem toEo_false : (Node.mkFalse).toEo = Term.Boolean false := by
  simp [Node.mkFalse, Node.toEo, Const.toEo]

omit [LogosFacts] in
theorem typeof_bool (b : Bool) : __smtx_typeof (__eo_to_smt (Term.Boolean b)) = SmtType.Bool := by
  show __smtx_typeof (SmtTerm.Boolean b) = _
  rw [__smtx_typeof.eq_def]

omit [LogosFacts] in
theorem eval_bool_const (M : SmtModel) (b : Bool) :
    __smtx_model_eval M (__eo_to_smt (Term.Boolean b)) = SmtValue.Boolean b := by
  show __smtx_model_eval M (SmtTerm.Boolean b) = _
  rw [__smtx_model_eval.eq_def]

/-- A Boolean term true in `M` equals `true` there, as a well-typed equation. -/
theorem condEquiv_true {Φ : SmtModel → Prop} {t : Term} (ht : HasBoolType t)
    (hv : ∀ M, model_wf M → Φ M → TrueIn M t) : CondEquiv Φ t (Term.Boolean true) := by
  refine ⟨(hasBoolType_mkEq_iff _ _).2 ⟨?_, ?_⟩, fun M hM hΦ => (trueIn_mkEq_iff M _ _).2 ?_⟩
  · unfold HasBoolType at ht; rw [ht]; simp
  · unfold HasBoolType at ht; rw [ht, typeof_bool]
  · have := hv M hM hΦ
    unfold TrueIn at this
    rw [this, eval_bool_const]
    exact LogosFacts.value_rel_refl _

/-- **Literals**: a Boolean literal true in every well-formed model satisfying
`Φ` gives its equation. -/
theorem lit_sound {Φ : SmtModel → Prop} {l : Node} (hb : HasBoolType l.toEo)
    (hv : ∀ M, model_wf M → Φ M → TrueIn M l.toEo) :
    CondEquiv Φ (EqProof.assumptionEq l).1.toEo (EqProof.assumptionEq l).2.toEo := by
  have hdef : CondEquiv Φ l.toEo Node.mkTrue.toEo := by
    rw [toEo_true]; exact condEquiv_true hb hv
  generalize hq : EqProof.assumptionEq l = q
  unfold EqProof.assumptionEq at hq
  split at hq
  · rename_i cs
    split at hq
    · rename_i h2
      subst hq
      have hb' : __smtx_typeof (SmtTerm.eq cs[0].toSmt cs[1].toSmt) = SmtType.Bool := by
        have := hb; unfold HasBoolType at this
        rwa [← Node.toSmt, toSmt_eq h2] at this
      refine ⟨hb', fun M hM hH => ?_⟩
      have := hv M hM hH
      unfold TrueIn at this
      rw [← Node.toSmt, toSmt_eq h2] at this
      exact this
    · subst hq; exact hdef
  · rename_i cs
    split at hq
    · rename_i h1
      subst hq
      simp only [toEo_false]
      have hb' : __smtx_typeof (SmtTerm.not cs[0].toSmt) = SmtType.Bool := by
        have := hb; unfold HasBoolType at this
        rwa [← Node.toSmt, toSmt_not h1] at this
      have hx : __smtx_typeof cs[0].toSmt = SmtType.Bool := typeof_not_bool _ hb'
      refine ⟨(hasBoolType_mkEq_iff _ _).2 ⟨?_, ?_⟩, fun M hM hH => (trueIn_mkEq_iff M _ _).2 ?_⟩
      · show __smtx_typeof cs[0].toSmt ≠ _; rw [hx]; simp
      · show __smtx_typeof cs[0].toSmt = _; rw [hx, typeof_bool]
      · have hv := hv M hM hH
        unfold TrueIn at hv
        rw [← Node.toSmt, toSmt_not h1, eval_not'] at hv
        obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM hx
        rw [hc] at hv
        cases c <;> simp [__smtx_model_eval_not, native_not] at hv
        show SmtValueRel (__smtx_model_eval M cs[0].toSmt) _
        rw [hc, eval_bool_const]
        exact LogosFacts.value_rel_refl _
    · subst hq; exact hdef
  · subst hq; exact hdef

/-- **Assumptions.** -/
theorem assume_sound {A : Array Node} (hT : ∀ l ∈ A.toList, HasBoolType l.toEo) {l : Node}
    (hl : l ∈ A.toList) :
    CondEquiv (Holds A) (EqProof.assumptionEq l).1.toEo (EqProof.assumptionEq l).2.toEo :=
  lit_sound (hT l hl) fun _ _ hH => hH _ hl

/-- A term related to a Boolean constant is Boolean, and has its value. -/
theorem bool_of_condEquiv {Φ : SmtModel → Prop} {t : Term} {b : Bool}
    (h : CondEquiv Φ t (Term.Boolean b)) :
    HasBoolType t ∧ ∀ M, model_wf M → Φ M → __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b := by
  have hT : HasBoolType t := by
    have := h.type_eq; unfold HasBoolType; rw [this]; exact typeof_bool b
  refine ⟨hT, fun M hM hΦ => ?_⟩
  obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM hT
  have hr := (trueIn_mkEq_iff M _ _).1 (h.2 M hM hΦ)
  rw [eval_bool_const, hc] at hr
  rw [hc, valueRel_bool hr]

omit [LogosFacts] in
theorem mem_of_getElem? {A : Array Node} {i : Nat} {l : Node} (h : A[i]? = some l) :
    l ∈ A.toList := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 h
  exact Array.mem_toList_iff.2 (Array.getElem_mem hi)

theorem wellTyped_of_bool {t : Node} (h : HasBoolType t.toEo) : t.WellTyped := by
  unfold Node.WellTyped Node.smtType; unfold HasBoolType at h
  show __smtx_typeof (__eo_to_smt t.toEo) ≠ _
  rw [h]; simp

/-- **Paths** lead to well-typed subterms. -/
theorem follow_wellTyped : ∀ (t : Node) (path : List Nat) (u : Node),
    EqProof.follow t path = some u → t.WellTyped → u.WellTyped
  | t, [], u, h, ht => by
    simp only [EqProof.follow, Option.some.injEq] at h; exact h ▸ ht
  | .app op cs, i :: is, u, h, ht => by
    simp only [EqProof.follow] at h
    split at h
    · rename_i hc
      split at h
      · rename_i c hci
        exact follow_wellTyped c is u h
          (ChildTyping.children_wellTyped hc ht c (mem_of_getElem? hci))
      · simp at h
    · simp at h
  | .const _, _ :: _, _, h, _ => by simp [EqProof.follow] at h
  | .var .., _ :: _, _, h, _ => by simp [EqProof.follow] at h
  | .boundVar .., _ :: _, _, h, _ => by simp [EqProof.follow] at h
  | .skolem .., _ :: _, _, h, _ => by simp [EqProof.follow] at h

omit [LogosFacts] in
/-- An element of a list is its `k`-th or in the rest. -/
theorem mem_or_eraseIdx {L : List Node} {k : Nat} {l x : Node} (hl : L[k]? = some l) (hx : x ∈ L) :
    x = l ∨ x ∈ L.eraseIdx k := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
  by_cases e : i = k
  · subst e; left; simp [List.getElem?_eq_getElem hi] at hl; exact hl
  · right
    rw [List.mem_eraseIdx_iff_getElem]
    exact ⟨i, hi, e, rfl⟩

/-- The relation of the arguments. -/
abbrev ArgRel (A : Array Node) (c d : Node) : Prop := CondEquiv (Holds A) c.toEo d.toEo

/-- **Soundness of the checker.** -/
theorem check_sound (A : Array Node) (hT : ∀ l ∈ A.toList, HasBoolType l.toEo)
    (hS : StableCond (Holds A)) (p : EqProof) :
    ∀ a b, EqProof.check A p = some (a, b) → CondEquiv (Holds A) a.toEo b.toEo := by
  induction p using EqProof.check.induct A
    (motive_1 := fun ls qs => EqProof.check.checkFalses A ls qs = true →
      ∀ l ∈ ls, CondEquiv (Holds A) l.toEo (Term.Boolean false))
    (motive_3 := fun cs args i => ∀ ds, EqProof.check.checkArgs A cs args i = some ds →
      (∀ c ∈ cs.toList, c.WellTyped) →
      List.Forall₂ (ArgRel A) ((cs.toList.drop i).take args.length) ds) with
  | case1 i =>
    intro a b h
    simp only [EqProof.check, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, he⟩ := h
    have := assume_sound hT (mem_of_getElem? hl)
    rw [he] at this; exact this
  | case2 p ih =>
    intro a b h
    simp only [EqProof.check, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨b', a', hp, rfl, rfl⟩ := h
    exact condEquiv_symm (ih _ _ hp)
  | case3 p q ihp ihq =>
    intro a c h
    simp only [EqProof.check, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a', b⟩, hp, ⟨b', c'⟩, hq, h⟩ := h
    split at h
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hb : b = b' := by simpa using hb
      subst hb
      exact (ihp _ _ hp).trans (ihq _ _ hq)
    · simp at h
  | case4 src args ih =>
    intro a b h
    simp only [EqProof.check, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨root, hroot, t, ht, h⟩ := h
    split at h
    · rename_i op cs
      split at h
      · simp at h
      · rename_i hsh
        split at h
        · simp at h
        · rename_i hsz
          simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨ds, hds, rfl, rfl⟩ := h
          simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_or,
            Bool.not_eq_false] at hsh
          have hwt : (Node.app op cs).WellTyped :=
            follow_wellTyped root src.path _ ht (wellTyped_of_bool (hT root (mem_of_getElem? hroot)))
          have hcs := ChildTyping.children_wellTyped hsh.2 hwt
          have hrel := ih cs ds hds hcs
          have hlen : args.toList.length = cs.toList.length := by
            simp only [Array.length_toList]; simpa using hsz
          rw [List.drop_zero, hlen, List.take_length] at hrel
          have hrel' : List.Forall₂ (CondEquiv (Holds A)) (cs.toList.map Node.toEo)
              ((ds.toArray.toList).map Node.toEo) := by
            simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
            exact hrel
          rw [Node.toEo_app, Node.toEo_app]
          refine shape_condCongr hS _ hsh.1 hrel' ?_
          have := hwt; unfold Node.WellTyped Node.smtType Node.toSmt at this
          rwa [Node.toEo_app] at this
    · simp at h
  | case5 p ih =>
    intro a b h
    simp only [EqProof.check, Option.map_eq_some_iff, Prod.exists, Prod.mk.injEq] at h
    obtain ⟨x, y, hp, rfl, rfl⟩ := h
    have hxy := ih _ _ hp
    simp only [toEo_true, Node.eqNode, Node.mkNode, toEo_eqNode]
    exact condEquiv_true hxy.1 hxy.2
  | case6 F cs _ _ =>
    intro a b h
    simp only [EqProof.check] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hTr, hCl⟩, hPr⟩ := hc
      have hV := LogosFacts.checker_sound _ F.toEo hTr hCl hPr
      have := lit_sound (Φ := Holds A) hV.1 fun M hM _ => hV.2 M hM
      rw [h] at this; exact this
    · simp_all (config := { zetaDelta := true })
  | case7 F cs _ _ =>
    intro a b h
    simp only [EqProof.check] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨hTr, hCl⟩, hPr⟩ := hc
      have hV := LogosFacts.checker_sound _ F.toEo hTr hCl hPr
      have := lit_sound (Φ := Holds A) hV.1 fun M hM _ => hV.2 M hM
      rw [h] at this; exact this
    · simp_all (config := { zetaDelta := true })
  | case8 p ih =>
    intro a b h
    simp only [EqProof.check, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨F, t⟩, hp, h⟩ := h
    split at h
    · rename_i ht
      have ht : t = Node.mkTrue := by simpa using ht
      subst ht
      simp only [Option.some.injEq] at h
      have hc := ih _ _ hp
      rw [toEo_true] at hc
      obtain ⟨hb, hev⟩ := bool_of_condEquiv hc
      have := lit_sound (Φ := Holds A) hb fun M hM hH => hev M hM hH
      rw [h] at this; exact this
    · simp at h
  | case9 i p ih =>
    intro a b h
    simp only [EqProof.check, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨F, t⟩, hp, h⟩ := h
    split at h
    · simp at h
    · rename_i ht
      have ht : t = Node.mkTrue := by simpa using ht
      subst ht
      split at h
      · rename_i ls hF
        simp only at hF; subst hF
        split at h
        · simp at h
        · rename_i hsz
          simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨l, hl, rfl, rfl⟩ := h
          have hc := ih _ _ hp
          rw [toEo_true] at hc
          obtain ⟨hb, hev⟩ := bool_of_condEquiv hc
          have h2 : 2 ≤ ls.size := by omega
          rw [toEo_and ls h2] at hb hev
          have hall := (typeof_andChain _).1 hb
          have hmem : l.toEo ∈ ls.toList.map Node.toEo :=
            List.mem_map_of_mem (Array.mem_toList_iff.2 (Array.mem_of_getElem? hl))
          rw [toEo_true]
          exact condEquiv_true (hall _ hmem) fun M hM hH =>
            ((eval_andChain M hM _ hall).1 (hev M hM hH)) _ hmem
      · simp at h
  | case10 k p qs ih ihq =>
    intro a b h
    simp only [EqProof.check, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨F, t⟩, hp, h⟩ := h
    split at h
    · simp at h
    · rename_i ht
      have ht : t = Node.mkTrue := by simpa using ht
      subst ht
      split at h
      · rename_i ls hF
        simp only at hF; subst hF
        split at h
        · simp at h
        · rename_i hsz
          simp only [Option.bind_eq_some_iff] at h
          obtain ⟨l, hl, h⟩ := h
          split at h
          · rename_i hf
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hc := ih _ _ hp
            rw [toEo_true] at hc
            obtain ⟨hb, hev⟩ := bool_of_condEquiv hc
            have h2 : 2 ≤ ls.size := by omega
            rw [toEo_or ls h2] at hb hev
            have hall := (typeof_orChain _).1 hb
            have hmem : l.toEo ∈ ls.toList.map Node.toEo :=
              List.mem_map_of_mem (Array.mem_toList_iff.2 (Array.mem_of_getElem? hl))
            have hfalse := ihq ls hf
            rw [toEo_true]
            refine condEquiv_true (hall _ hmem) fun M hM hH => ?_
            obtain ⟨c, hcv⟩ := LogosFacts.eval_bool M _ hM (hall _ hmem)
            cases c
            · -- all the disjuncts are false: a contradiction
              exfalso
              have hor := (eval_orChain M hM _ hall).2 (by
                intro x hx
                obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
                rcases mem_or_eraseIdx (Array.getElem?_toList ▸ hl) hy with rfl | hy'
                · exact hcv
                · exact (bool_of_condEquiv (hfalse y hy')).2 M hM hH)
              rw [hev M hM hH] at hor
              simp at hor
            · exact hcv
          · simp at h
      · simp at h
  | case11 t args hwt _ =>
    intro a b h
    simp only [EqProof.check, hwt, ↓reduceIte] at h
    simp at h
  | case12 t args _ ih =>
    intro a b h
    simp only [EqProof.check, Option.bind_eq_bind] at h
    split at h
    · simp at h
    · split at h
      · rename_i op cs hwt _
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_not] at hwt
        split at h
        · simp at h
        · rename_i hsh
          split at h
          · simp at h
          · rename_i hsz
            simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨ds, hds, rfl, rfl⟩ := h
            simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, not_or,
              Bool.not_eq_false] at hsh
            have hcs := ChildTyping.children_wellTyped hsh.2 hwt
            have hrel := ih cs ds hds hcs
            have hlen : args.toList.length = cs.toList.length := by
              simp only [Array.length_toList]; simpa using hsz
            rw [List.drop_zero, hlen, List.take_length] at hrel
            have hrel' : List.Forall₂ (CondEquiv (Holds A)) (cs.toList.map Node.toEo)
                ((ds.toArray.toList).map Node.toEo) := by
              simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
              exact hrel
            rw [Node.toEo_app, Node.toEo_app]
            refine shape_condCongr hS _ hsh.1 hrel' ?_
            have := hwt; unfold Node.WellTyped Node.smtType Node.toSmt at this
            rwa [Node.toEo_app] at this
      · simp at h
  | case13 t hwt =>
    intro a b h
    simp only [EqProof.check, hwt, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact CondEquiv.of_equiv (rewrite_correct_of_logos t (of_decide_eq_true hwt))
  | case14 t hwt =>
    intro a b h
    simp [EqProof.check, hwt] at h
  | case15 =>
    rename_i _ l hl; simp at hl
  | case16 l ls q qs ihq ih =>
    rename_i hf x hx
    simp only [EqProof.check.checkFalses, Bool.and_eq_true, beq_iff_eq] at hf
    rcases List.mem_cons.1 hx with rfl | hx
    · have := ihq _ _ hf.1; rwa [toEo_false] at this
    · exact ih hf.2 x hx
  | case17 t x h₁ h₂ =>
    rename_i hf _ _
    exfalso
    cases x <;> cases t <;> simp_all [EqProof.check.checkFalses]
  | case18 cs i =>
    rename_i ds h _
    simp only [EqProof.check.checkArgs, Option.some.injEq] at h
    subst h; simp
  | case19 cs rest i ih =>
    rename_i ds h hcs
    simp only [EqProof.check.checkArgs, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c, hc, ds', hds', rfl⟩ := h
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 hc
    rw [List.drop_eq_getElem_cons (by simpa using hi)]
    simp only [List.length_cons, List.take_succ_cons, Array.getElem_toList]
    refine List.Forall₂.cons ?_ (ih ds' hds' hcs)
    have hw := hcs _ (Array.mem_toList_iff.2 (Array.getElem_mem hi))
    exact CondEquiv.refl _ hw
  | case20 cs q rest i ihq ih =>
    rename_i ds h hcs
    simp only [EqProof.check.checkArgs, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨c, hc, ⟨a, d⟩, hq, h⟩ := h
    split at h
    · simp at h
    · rename_i hac
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ds', hds', rfl⟩ := h
      have hac : a = c := by simpa using hac
      subst hac
      obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.1 hc
      rw [List.drop_eq_getElem_cons (by simpa using hi)]
      simp only [List.length_cons, List.take_succ_cons, Array.getElem_toList]
      exact List.Forall₂.cons (ihq _ _ hq) (ih ds' hds' hcs)

/-- Closed assumptions make the condition that they hold stable. -/
theorem stable_of_closed {A : Array Node} (h : EqProof.closedAssumptions A = true) :
    StableCond (Holds A) := by
  intro M N _ _ hAgree hM l hl
  have hc : __eo_is_closed l.toEo = Term.Boolean true := by
    unfold EqProof.closedAssumptions at h
    rw [Array.all_eq_true_iff_forall_mem] at h
    simpa using h l (Array.mem_toList_iff.1 hl)
  unfold TrueIn
  rw [← LogosFacts.closed_eval _ hc M N hAgree]
  exact hM l hl

/-- **Conflicts are sound**: no well-formed model satisfies the assumptions of
a conflict. -/
theorem checkConflict_sound (A : Array Node) (p : EqProof) (h : EqProof.checkConflict A p = true)
    (hT : ∀ l ∈ A.toList, HasBoolType l.toEo) : ∀ M, model_wf M → ¬ Holds A M := by
  intro M hM hH
  unfold EqProof.checkConflict at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  have hc := check_sound A hT (stable_of_closed h.1) p _ _ h.2
  have := (trueIn_mkEq_iff M _ _).1 (hc.2 M hM hH)
  rw [toEo_true, toEo_false, eval_bool_const, eval_bool_const] at this
  exact absurd (valueRel_bool this) (by decide)

end Telos.Solver
