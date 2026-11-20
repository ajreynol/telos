import TelosProofs.Solver.EqProof
import TelosProofs.Solver.Explain
import TelosProofs.Preprocess.Preprocess
import Telos.Frontend.Solve

/-!
# `unsat` answers are correct

- **The engine** (`run_unsat_sound`): an `unsat` answer is certified
  (`Solver.run_unsat`) by the verified explanation of its conflict
  (`certifyV_sound`, from `EE.explainLitV_sound` and `EE.runFull_sound`), or
  else by a certificate whose assumptions are among the literals and whose
  proof checks (`checkConflict_sound`). Either way no well-formed model
  satisfies the literals.
- **The front end** (`solveScript_unsat`): the literals are those of the
  assertions given to the engine (`conjLiterals_sound`), which hold in every
  model of the input assertions. With preprocessing, they are the conjuncts of
  the pipeline, equivalent to the conjunction of the input assertions
  (`preprocess_correct_of_logos`). So if the engine answers `unsat`, the input
  assertions are unsatisfiable.

The only hypothesis on the input is that its assertions are Boolean.
-/

open Eo Smtm SmtEval

namespace Telos

set_option linter.unusedSectionVars false

variable [LogosFacts]

namespace Solver

/-- A certificate whose assumptions are among the literals refutes them. -/
theorem certifies_sound {lits : List Node} {A : Array Node} {p : EqProof}
    (hc : certifies lits A p = true) (hT : ∀ l ∈ lits, HasBoolType l.toEo) (M : SmtModel)
    (hM : model_wf M) (hall : ∀ l ∈ lits, TrueIn M l.toEo) : False := by
  unfold certifies at hc
  simp only [Bool.and_eq_true] at hc
  have hsub : ∀ l ∈ A.toList, l ∈ lits := by
    intro l hl
    have := (Array.all_eq_true_iff_forall_mem.1 hc.1) l (Array.mem_toList_iff.1 hl)
    simp only [List.any_eq_true, decide_eq_true_eq] at this
    obtain ⟨x, hx, rfl⟩ := this
    exact hx
  exact checkConflict_sound A p hc.2 (fun l hl => hT l (hsub l hl)) M hM
    (fun l hl => hall l (hsub l hl))

omit [LogosFacts] in
/-- A literal and its negation are not both true. -/
theorem not_both (M : SmtModel) (lit : Node) (h₁ : TrueIn M lit.toEo)
    (h₂ : TrueIn M (negate lit).toEo) : False := by
  unfold negate at h₂
  unfold TrueIn at h₁ h₂
  change __smtx_model_eval M lit.toSmt = _ at h₁
  split at h₂
  · rename_i cs
    split at h₂
    · rename_i h1
      change __smtx_model_eval M (Node.app (.kind .NOT) cs).toSmt = _ at h₁
      change __smtx_model_eval M cs[0].toSmt = _ at h₂
      rw [toSmt_not h1, eval_not', h₂] at h₁
      simp [__smtx_model_eval_not, native_not] at h₁
    · change __smtx_model_eval M (Node.app (.kind .NOT) #[Node.app (.kind .NOT) cs]).toSmt = _ at h₂
      rw [toSmt_not (cs := #[Node.app (.kind .NOT) cs]) rfl, eval_not'] at h₂
      simp only [Array.getElem_singleton] at h₂
      rw [h₁] at h₂
      simp [__smtx_model_eval_not, native_not] at h₂
  · change __smtx_model_eval M (Node.app (.kind .NOT) #[lit]).toSmt = _ at h₂
    rw [toSmt_not (cs := #[lit]) rfl, eval_not'] at h₂
    simp only [Array.getElem_singleton] at h₂
    rw [h₁] at h₂
    simp [__smtx_model_eval_not, native_not] at h₂

theorem mem_of_any {lits : List Node} {l : Node} (h : lits.any (fun x => decide (x = l)) = true) :
    l ∈ lits := by
  simp only [List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨x, hx, rfl⟩ := h
  exact hx

/-- The context of `certifyV` is good for reasons among the literals, closed. -/
theorem good_of_lits {lits : List Node} {exp : Array Node} (ee : EE.EqualityEngine)
    (hT : ∀ l ∈ lits, HasBoolType l.toEo)
    (hsub : exp.all (fun l => lits.any (fun x => decide (x = l))) = true)
    (hcl : EqProof.closedAssumptions exp = true) :
    EE.Good { ee, roots := lits.toArray, paths := EE.subtermPaths lits.toArray } exp := by
  have hs : ∀ l ∈ exp.toList, l ∈ lits := fun l hl =>
    mem_of_any ((Array.all_eq_true_iff_forall_mem.1 hsub) l (Array.mem_toList_iff.1 hl))
  exact ⟨fun l hl => hT l (hs l hl), stable_of_closed hcl,
    fun r hr => wellTyped_of_bool (hT r (by simpa using hr))⟩

/-- **A conflict certified by the verified explanation refutes the literals.** -/
theorem certifyV_sound {lits : List Node} {ee : EE.EqualityEngine} {p : Pending} {exp : Array Node}
    (h : certifyV lits ee p = some exp) (hT : ∀ l ∈ lits, HasBoolType l.toEo) (M : SmtModel)
    (hM : model_wf M) (hall : ∀ l ∈ lits, TrueIn M l.toEo) : False := by
  cases p with
  | prop lit =>
    unfold certifyV at h
    dsimp only at h
    split at h
    · rename_i exp' hexp
      split at h
      · rename_i hg
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true] at hg
        obtain ⟨⟨hsub, hneg⟩, hcl⟩ := hg
        have hG := good_of_lits ee hT hsub hcl
        have hH : Holds exp' M := fun l hl =>
          hall l (mem_of_any ((Array.all_eq_true_iff_forall_mem.1 hsub) l (Array.mem_toList_iff.1 hl)))
        exact not_both M lit (EE.explainLitV_sound hexp hG M hM hH) (hall _ (mem_of_any hneg))
      · simp at h
    · simp at h
  | constants a b =>
    unfold certifyV at h
    dsimp only at h
    split at h
    · rename_i i j _ _
      split at h
      · rename_i hg
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hg
        obtain ⟨⟨hi, hj⟩, hab⟩ := hg
        split at h
        · rename_i exp' hexp
          split at h
          · rename_i hg'
            simp only [Option.some.injEq] at h; subst h
            simp only [Bool.and_eq_true] at hg'
            obtain ⟨hsub, hcl⟩ := hg'
            have hG := good_of_lits ee hT hsub hcl
            have hH : Holds exp' M := fun l hl =>
              hall l (mem_of_any ((Array.all_eq_true_iff_forall_mem.1 hsub) l (Array.mem_toList_iff.1 hl)))
            rcases EE.runFull_sound hexp hG with he | hc
            · subst he
              rw [hi] at hj
              rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [Node.mkTrue, Node.mkFalse] at hj
            · rw [hi, hj] at hc
              have hr := (trueIn_mkEq_iff M _ _).1 (hc.2 M hM hH)
              rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
                rw [toEo_true, toEo_false, eval_bool_const, eval_bool_const] at hr <;>
                exact absurd (valueRel_bool hr) (by decide)
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  | dt _ => simp [certifyV] at h

/-- **An `unsat` of the engine is correct**: no well-formed model satisfies the
literals. -/
theorem run_unsat_sound (c : Config) (lits : List Node) (h : (run c lits).answer = .unsat)
    (hT : ∀ l ∈ lits, HasBoolType l.toEo) (M : SmtModel) (hM : model_wf M) :
    ¬ ∀ l ∈ lits, TrueIn M l.toEo := by
  intro hall
  rcases run_unsat c lits h with ⟨_, _, _, hv⟩ | ⟨A, p, hc⟩
  · exact certifyV_sound hv hT M hM hall
  · exact certifies_sound hc hT M hM hall

end Solver

namespace Frontend

open Preprocess

/-- What holds of a node in a model: it is Boolean, and true. -/
abbrev Good (M : SmtModel) (n : Node) : Prop := HasBoolType n.toEo ∧ TrueIn M n.toEo

/-- The conjuncts of a true conjunction (of at least two) are good. -/
theorem and_good {M : SmtModel} (hM : model_wf M) {cs : Array Node} (h2 : 2 ≤ cs.size)
    (h : Good M (Node.app (.kind .AND) cs)) : ∀ c ∈ cs.toList, Good M c := by
  have hb := (and_bool_iff cs h2).1 h.1
  have hv := (and_true_iff cs h2 M hM hb).1 h.2
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
  have hi' : i < cs.size := by simpa using hi
  simp only [Array.getElem_toList]
  exact ⟨hb i hi', hv i hi'⟩

/-- **The literals of a good assertion are good.** -/
theorem conjLiterals_sound {M : SmtModel} (hM : model_wf M) {n : Node} {ls : List Node}
    (h : conjLiterals n = some ls) (hn : Good M n) : ∀ l ∈ ls, Good M l := by
  unfold conjLiterals at h
  split at h
  · simp at h; subst h; simp
  · split at h
    · rename_i cs
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h
        subst h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        exact and_good hM hc.1 hn
      · simp at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h
        intro l hl; simp at hl; subst hl; exact hn
      · simp at h

/-- **The literals of good assertions are good.** -/
theorem literalsOf_sound {M : SmtModel} (hM : model_wf M) :
    ∀ (out acc lits : List Node),
      out.foldlM (fun acc a => match conjLiterals a with
        | some ls => Except.ok (acc ++ ls)
        | none => Except.error a) acc = (Except.ok lits : Except Node (List Node)) →
      (∀ l ∈ acc, Good M l) → (∀ a ∈ out, Good M a) → ∀ l ∈ lits, Good M l
  | [], acc, lits, h, hacc, _ => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h; subst h; exact hacc
  | a :: rest, acc, lits, h, hacc, hout => by
    simp only [List.foldlM] at h
    split at h
    · rename_i ls hls
      refine literalsOf_sound hM rest (acc ++ ls) lits h ?_ (fun b hb => hout b (by simp [hb]))
      intro l hl
      rcases List.mem_append.1 hl with hl | hl
      · exact hacc l hl
      · exact conjLiterals_sound hM hls (hout a (by simp)) l hl
    · simp [bind, Except.bind] at h

/-- `true` is good. -/
theorem good_true (M : SmtModel) : Good M Node.mkTrue := by
  refine ⟨?_, ?_⟩
  · unfold HasBoolType; rw [Solver.toEo_true]; exact Solver.typeof_bool true
  · unfold TrueIn; rw [Solver.toEo_true]; exact Solver.eval_bool_const M true

/-- **The assertions given to the engine hold** in every model of the input. -/
theorem engineAssertions_sound {M : SmtModel} (hM : model_wf M) (as : List Node)
    (opts : PPOptions) (pp : Bool) (hb : ∀ a ∈ as, HasBoolType a.toEo)
    (hv : TrueIn M (inputNode as).toEo) : ∀ a ∈ engineAssertions as opts pp, Good M a := by
  have hsize : 2 ≤ (as ++ [Node.mkTrue, Node.mkTrue]).toArray.size := by simp
  have hgood : Good M (inputNode as) := by
    refine ⟨?_, hv⟩
    have hall : ∀ x ∈ as ++ [Node.mkTrue, Node.mkTrue], HasBoolType x.toEo := by
      intro x hx
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with hx | rfl | rfl
      · exact hb x hx
      · exact (good_true M).1
      · exact (good_true M).1
    unfold inputNode Node.mkNode
    rw [and_bool_iff _ hsize]
    intro i hi
    exact hall _ (by simp)
  have hin : ∀ a ∈ as, Good M a := by
    intro a ha
    have := and_good hM hsize hgood
    exact this a (by simp [ha])
  unfold engineAssertions
  split
  · exact hin
  · -- the pipeline's conjunction holds
    have hwt : (inputNode as).WellTyped := Solver.wellTyped_of_bool hgood.1
    have heq := preprocess_correct_of_logos as hwt opts
    obtain ⟨_, hty, hval⟩ := (Node.equiv_iff _ _).1 heq
    have hP : Good M (preprocessCert as opts).1 := by
      have hbP : HasBoolType (preprocessCert as opts).1.toEo := by
        have := hgood.1
        unfold HasBoolType at this ⊢
        have hty' : __smtx_typeof (inputNode as).toSmt = __smtx_typeof (preprocessCert as opts).1.toSmt :=
          hty
        exact hty' ▸ this
      refine ⟨hbP, ?_⟩
      have hrel := hval M hM
      obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM hbP
      have hv' : __smtx_model_eval M (inputNode as).toSmt = SmtValue.Boolean true := hv
      have hc' : __smtx_model_eval M (preprocessCert as opts).1.toSmt = SmtValue.Boolean c := hc
      rw [hv', hc'] at hrel
      have := valueRel_bool hrel
      unfold TrueIn
      show __smtx_model_eval M (preprocessCert as opts).1.toSmt = _
      rw [hc', ← this]
    split
    · rename_i cs hcs
      rw [hcs] at hP
      split
      · rename_i h2
        intro a ha
        exact and_good hM h2 hP a (List.mem_of_mem_dropLast ha)
      · intro a ha; simp at ha; subst ha; exact hP
    · intro a ha; simp at ha; subst ha; exact hP

/-- **Correctness of `unsat`.** If the engine answers `unsat` on a script whose
assertions are Boolean, no well-formed model satisfies the input assertions. -/
theorem solveScript_unsat (sc : Script) (u : UserOptions) (ee pp wp co : Bool)
    {out : List Node} {r : Solver.Result} (h : solveScript sc u ee pp wp co = .ok (out, r))
    (hu : r.answer = .unsat) {opts : PPOptions} {as : List Node}
    (hin : ppInput sc u = .ok (opts, as)) (hb : ∀ a ∈ as, HasBoolType a.toEo) :
    ∀ M, model_wf M → ¬ TrueIn M (inputNode as).toEo := by
  intro M hM hv
  simp only [solveScript, hin, bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i lits hlits
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hgood := literalsOf_sound hM _ [] lits (engineLiterals_ok hlits) (by simp)
        (engineAssertions_sound hM as opts pp hb hv)
      -- the check of a `sat` answer turns it into `unknown`, never into `unsat`
      generalize hr : Solver.run _ lits = r0 at hu
      have hu' : r0.answer = .unsat := by
        split at hu
        · exact hu
        · split at hu <;> simp_all
      rw [← hr] at hu'
      exact Solver.run_unsat_sound _ lits hu' (fun l hl => (hgood l hl).1) M hM
        (fun l hl => (hgood l hl).2)

end Frontend

end Telos
