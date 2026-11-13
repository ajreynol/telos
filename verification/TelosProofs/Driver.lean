import TelosProofs.Certified

/-!
# Correctness of the rewriting driver

If every theory rewriter returns equivalent nodes, so does the driver
(`rewriteWith_sound`). The proof follows the driver's three steps; rewriting under
operators uses `Node.Equiv.congr` and `Node.Equiv.congr_binder`.

Every theory rewriter does return equivalent nodes (`TheoryRewriter.correct`),
since its responses carry CPC certificates (`Certified.equiv`).
-/

namespace Telos

/-- A function on nodes that maps every well-typed node to an equivalent one. -/
def Sound (f : Node → Node) : Prop :=
  ∀ n : Node, n.WellTyped → n.Equiv (f n)

/-- A theory rewriter whose pre- and post-rewrites return equivalent nodes. -/
def TheoryRewriter.Correct (R : TheoryRewriter) : Prop :=
  ∀ n : Node, n.WellTyped → n.Equiv (R.preRewrite n).node ∧ n.Equiv (R.postRewrite n).node

/-- Every theory rewriter is correct: its responses are certified. -/
theorem TheoryRewriter.correct (R : TheoryRewriter) : R.Correct :=
  fun n h => ⟨(R.preRewrite n).cert.equiv h, (R.postRewrite n).cert.equiv h⟩

variable {R : TheoryId → TheoryRewriter}

theorem preRewriteLoop_sound (hR : ∀ tid, (R tid).Correct) :
    ∀ fuel, Sound (preRewriteLoop R fuel) := by
  intro fuel
  induction fuel with
  | zero => exact fun n h => Node.Equiv.refl n h
  | succ fuel ih =>
    intro n hn
    have h₁ := ((hR (theoryOf n)) n hn).1
    simp only [preRewriteLoop]
    split
    · split
      · exact h₁
      · exact h₁.trans (ih _ h₁.wellTyped_right)
    · exact h₁.trans (ih _ h₁.wellTyped_right)

theorem rewriteChildren_sound {f : Node → Node} (hf : Sound f) : Sound (rewriteChildren f) := by
  intro n hn
  unfold rewriteChildren
  split
  · next op cs =>
    split
    · next hop =>
      split
      · next hall =>
        refine Node.Equiv.congr hop hn ?_
        rw [Array.toList_map, List.forall₂_map_right_iff]
        refine List.forall₂_same.2 fun c hc => hf c ?_
        have := (Array.all_eq_true_iff_forall_mem.1 hall) c (Array.mem_toList_iff.1 hc)
        simpa using this
      · exact Node.Equiv.refl _ hn
    · split
      · next k vs body pats _ =>
        split
        · next hq =>
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
          have hk : k = .FORALL ∨ k = .EXISTS := by
            cases k <;> simp_all [Kind.isQuantifier]
          exact Node.Equiv.congr_binder hk rfl hn (hf body hq.2)
        · exact Node.Equiv.refl _ hn
      · exact Node.Equiv.refl _ hn
  · exact Node.Equiv.refl _ hn

theorem postRewriteLoop_sound (hR : ∀ tid, (R tid).Correct) {full : Node → Node}
    (hfull : Sound full) : ∀ fuel, Sound (postRewriteLoop R full fuel) := by
  intro fuel
  induction fuel with
  | zero => exact fun n h => Node.Equiv.refl n h
  | succ fuel ih =>
    intro n hn
    have h₁ := ((hR (theoryOf n)) n hn).2
    simp only [postRewriteLoop]
    split
    · split
      · exact h₁
      · exact h₁.trans (hfull _ h₁.wellTyped_right)
    · split
      · exact h₁.trans (ih _ h₁.wellTyped_right)
      · exact h₁.trans (hfull _ h₁.wellTyped_right)
    · exact h₁.trans (hfull _ h₁.wellTyped_right)

/-- **Correctness of the driver**, given correct theory rewriters. -/
theorem rewriteWith_sound (hR : ∀ tid, (R tid).Correct) : ∀ fuel, Sound (rewriteWith R fuel) := by
  intro fuel
  induction fuel with
  | zero => exact fun n h => Node.Equiv.refl n h
  | succ fuel ih =>
    intro n hn
    simp only [rewriteWith]
    have h₁ := preRewriteLoop_sound hR fuel n hn
    have h₂ := rewriteChildren_sound ih _ h₁.wellTyped_right
    have h₃ := postRewriteLoop_sound hR ih fuel _ h₂.wellTyped_right
    exact h₁.trans (h₂.trans h₃)

theorem theoryRewriter_correct : ∀ tid, (theoryRewriter tid).Correct :=
  fun tid => (theoryRewriter tid).correct

end Telos
