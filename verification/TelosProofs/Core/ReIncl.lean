import TelosProofs.Core.Template
import TelosProofs.Core.LenConcat
import Telos.Core.Static

/-!
# Inclusions of regular expressions are CPC steps

`reIncl_provesEq`: under `ReIncl.Ok`, Logos's checker accepts
`[re_inter_inclusion (= n m)]`, resp. `re_union_inclusion`. A search (`ReIncl.M`)
is sound for a term `t` (`Sound`) when its result `some b` means that `t` is `b`,
from any cache whose entries are Logos's values; each search of
`Telos/Core/ReIncl.lean` is sound for the Logos program it ports.
-/

open Eo Smtm SmtEval

namespace Telos

namespace ReIncl

/-- The entries of a cache are Logos's values. -/
def Good (c : Cache) : Prop :=
  ∀ a b r, c[(⟨a, b⟩ : Pair)]? = some r → __str_re_includes_rec a b = .Boolean r

/-- A result of `x` is the value of `t`. -/
def Sound (x : M) (t : Term) : Prop :=
  ∀ c, Good c → (∀ b, (x c).1 = some b → t = .Boolean b) ∧ Good (x c).2

theorem good_empty : Good {} := by intro a b r h; simp at h

theorem sound_none (t : Term) : Sound (fun c => (none, c)) t := fun _ hc => ⟨by simp, hc⟩

theorem sound_ret (b : Bool) : Sound (ret b) (.Boolean b) := fun _ hc => ⟨by simp [ret], hc⟩

theorem sound_ofTerm (t : Term) : Sound (ofTerm t) t := by
  intro c hc
  unfold ofTerm
  split
  · simp [ret, hc]
  · simp [hc]

theorem sound_eqv (a b : Term) : Sound (eqv a b) (__eo_eq a b) := by
  intro c hc
  refine ⟨?_, ?_⟩
  · intro r hr
    unfold eqv at hr
    split at hr
    · simp at hr
    · simp at hr
    · rename_i h1 h2
      simp only [Option.some.injEq] at hr
      subst hr
      unfold __eo_eq
      split
      · simp_all
      · simp_all
      · simp [native_teq, eqTerm, eq_comm]
  · unfold eqv; split <;> exact hc

theorem ite_true (u v : Term) : __eo_ite (.Boolean true) u v = u := by simp [__eo_ite, native_ite, native_teq]
theorem ite_false (u v : Term) : __eo_ite (.Boolean false) u v = v := by simp [__eo_ite, native_ite, native_teq]

theorem sound_orElse {x y : M} {t u : Term} (hx : Sound x t) (hy : Sound y u) :
    Sound (orElse x y) (__eo_ite t (.Boolean true) u) := by
  intro c hc
  obtain ⟨h1, h2⟩ := hx c hc
  rcases hxc : x c with ⟨_ | _ | _, c'⟩ <;> rw [hxc] at h1 h2
  · have e : orElse x y c = (none, c') := by simp [orElse, hxc]
    rw [e]; exact ⟨by simp, h2⟩
  · have e : orElse x y c = y c' := by simp [orElse, hxc]
    rw [e, h1 false rfl, ite_false]; exact hy c' h2
  · have e : orElse x y c = (some true, c') := by simp [orElse, hxc]
    rw [e, h1 true rfl, ite_true]; exact ⟨by simp, h2⟩

theorem sound_andThen {x y : M} {t u : Term} (hx : Sound x t) (hy : Sound y u) :
    Sound (andThen x y) (__eo_ite t u (.Boolean false)) := by
  intro c hc
  obtain ⟨h1, h2⟩ := hx c hc
  rcases hxc : x c with ⟨_ | _ | _, c'⟩ <;> rw [hxc] at h1 h2
  · have e : andThen x y c = (none, c') := by simp [andThen, hxc]
    rw [e]; exact ⟨by simp, h2⟩
  · have e : andThen x y c = (some false, c') := by simp [andThen, hxc]
    rw [e, h1 false rfl, ite_false]; exact ⟨by simp, h2⟩
  · have e : andThen x y c = y c' := by simp [andThen, hxc]
    rw [e, h1 true rfl, ite_true]; exact hy c' h2

theorem sound_nonStuck {a t : Term} {x : M} (h : a ≠ .Stuck → Sound x t) : Sound (nonStuck a x) t := by
  unfold nonStuck
  split
  · exact sound_none t
  · rename_i hne; exact h hne

/-- A value that decides another. -/
theorem Sound.map {x : M} {t u : Term} (h : Sound x t) (e : ∀ b, t = .Boolean b → u = .Boolean b) : Sound x u :=
  fun c hc => ⟨fun b hb => e b ((h c hc).1 b hb), (h c hc).2⟩

theorem sound_tf {x : M} {t : Term} (h : Sound x t) : Sound x (__eo_ite t (.Boolean true) (.Boolean false)) :=
  h.map fun b hb => by cases b <;> simp [hb, __eo_ite, native_ite, native_teq]

theorem sound_eqTrue {x : M} {t : Term} (h : Sound x t) : Sound x (__eo_eq t (.Boolean true)) :=
  h.map fun b hb => by cases b <;> simp [hb, __eo_eq, native_teq]

theorem Sound.eq {x : M} {t u : Term} (h : Sound x u) (e : t = u) : Sound x t := e ▸ h

theorem asCat_some {a : Term} {p : Term × Term} (h : asCat a = some p) : a = cat p.1 p.2 := by
  unfold asCat at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · cases h

/-! ## The equations of Logos's programs -/

theorem rec_emp_emp (r1 r3 : Term) : __str_re_includes_rec (cat r1 emp) (cat r3 emp) =
    __eo_ite (__eo_eq r1 r3) (.Boolean true) (__str_re_includes_base_rec r1 r3) := by
  simp only [cat, emp]; rw [__str_re_includes_rec]

theorem rec_emp {r1 b : Term} (hb : b ≠ .Stuck) (h : ∀ r3, b ≠ cat r3 emp) : __str_re_includes_rec (cat r1 emp) b =
    __eo_ite (__eo_eq r1 b) (.Boolean true) (__str_re_includes_base_rec r1 b) := by
  simp only [cat, emp] at *; rw [__str_re_includes_rec] <;> simp_all

theorem rec_cat_emp {r1 r2 r3 : Term} (h : r2 ≠ emp) : __str_re_includes_rec (cat r1 r2) (cat r3 emp) =
    __eo_ite (__eo_ite (__eo_eq (cat r1 r2) r3) (.Boolean true) (__str_re_includes_base_rec (cat r1 r2) r3))
      (.Boolean true) (__str_re_includes_concat r1 r2 r3 emp) := by
  simp only [cat, emp] at *; rw [__str_re_includes_rec]; simp_all

theorem rec_any_emp {a r3 : Term} (ha : a ≠ .Stuck) (h : ∀ x y, a ≠ cat x y) : __str_re_includes_rec a (cat r3 emp) =
    __eo_ite (__eo_eq a r3) (.Boolean true) (__str_re_includes_base_rec a r3) := by
  simp only [cat, emp] at *; rw [__str_re_includes_rec] <;> simp_all

theorem rec_cat_cat {r1 r2 r3 r4 : Term} (h2 : r2 ≠ emp) (h4 : r4 ≠ emp) :
    __str_re_includes_rec (cat r1 r2) (cat r3 r4) = __str_re_includes_concat r1 r2 r3 r4 := by
  simp only [cat, emp] at *; rw [__str_re_includes_rec] <;> simp_all

theorem concat_eq {r1 r2 r3 r4 : Term} (h1 : r1 ≠ .Stuck) (h2 : r2 ≠ .Stuck) (h3 : r3 ≠ .Stuck) (h4 : r4 ≠ .Stuck) :
    __str_re_includes_concat r1 r2 r3 r4 =
    __eo_ite (__eo_ite (__eo_ite (__eo_eq r1 r3) (.Boolean true) (__str_re_includes_base_rec r1 r3))
        (__eo_ite (__eo_eq r2 r4) (.Boolean true) (__str_re_includes_rec r2 r4)) (.Boolean false)) (.Boolean true)
      (__eo_ite (__eo_ite (__re_is_unbound_wildcard (cat r1 r2))
          (__eo_ite (__eo_eq (cat r1 r2) r4) (.Boolean true)
            (__eo_ite (__eo_eq (cat r1 r2) r4) (.Boolean true) (__str_re_includes_rec (cat r1 r2) r4))) (.Boolean false))
        (.Boolean true)
        (__eo_ite (__eo_ite (__eo_eq r1 sigmaStar)
          (__eo_ite (__eo_eq r2 (cat r3 r4)) (.Boolean true) (__str_re_includes_rec r2 (cat r3 r4))) (.Boolean false))
          (.Boolean true) (.Boolean false))) := by
  rw [__str_re_includes_concat] <;> first | rfl | assumption

theorem base_str {a b s : Term} (ha : a = .Apply (.UOp .str_to_re) s) (hb : b ≠ .Stuck)
    (h : ∀ s, b ≠ .Apply (.UOp .str_to_re) s) : __str_re_includes_base_rec a b = .Boolean false := by
  subst ha; rw [__str_re_includes_base_rec] <;> simp_all

theorem base_eq {a b : Term} (ha : a ≠ .Stuck) (hb : b ≠ .Stuck)
    (h1 : ∀ s, b ≠ .Apply (.UOp .str_to_re) s) (h2 : ∀ s, a ≠ .Apply (.UOp .str_to_re) s)
    (h3 : ∀ s1 s2 s3 s4, a = .Apply (.Apply (.UOp .re_range) s1) s2 → b = .Apply (.Apply (.UOp .re_range) s3) s4 → False) :
    __str_re_includes_base_rec a b =
    __eo_ite (__eo_eq (__str_re_includes_lhs_union a b) (.Boolean true)) (.Boolean true)
      (__eo_ite (__eo_eq (__str_re_includes_rhs_inter a b) (.Boolean true)) (.Boolean true)
        (__eo_ite (__eo_eq (__str_re_includes_lhs_star a b) (.Boolean true)) (.Boolean true) (.Boolean false))) := by
  rw [__str_re_includes_base_rec] <;> assumption

/-! ## The searches are sound -/

/-- The searches with the bound `n`. -/
def AllSound (n : Nat) : Prop :=
  (∀ a b, Sound (recF n a b) (__str_re_includes_rec a b)) ∧
  (∀ a b, Sound (recBody n a b) (__str_re_includes_rec a b)) ∧
  (∀ a b c d, Sound (concatF n a b c d) (__str_re_includes_concat a b c d)) ∧
  (∀ a b, Sound (baseF n a b) (__str_re_includes_base_rec a b)) ∧
  (∀ a b, Sound (unionF n a b) (__str_re_includes_lhs_union a b)) ∧
  (∀ a b, Sound (interF n a b) (__str_re_includes_rhs_inter a b)) ∧
  (∀ a b, Sound (starF n a b) (__str_re_includes_lhs_star a b))

theorem sound_memo {n : Nat} {a b : Term} (h : Sound (recBody n a b) (__str_re_includes_rec a b)) :
    Sound (recF (n + 1) a b) (__str_re_includes_rec a b) := by
  intro c hc
  rcases hg : c[(⟨a, b⟩ : Pair)]? with _ | r
  · obtain ⟨h1, h2⟩ := h c hc
    rcases hb : recBody n a b c with ⟨_ | r, c'⟩ <;> rw [hb] at h1 h2
    · have e : recF (n + 1) a b c = (none, c') := by simp [recF, hg, hb]
      rw [e]; exact ⟨by simp, h2⟩
    · have e : recF (n + 1) a b c = (some r, c'.insert ⟨a, b⟩ r) := by simp [recF, hg, hb]
      rw [e]
      refine ⟨fun b' hb' => h1 b' hb', ?_⟩
      intro x y r' hr'
      simp only [Std.HashMap.getElem?_insert] at hr'
      split at hr'
      · rename_i hk
        have := eq_of_beq hk
        simp only [Pair.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        exact h1 r' hr'
      · exact h2 x y r' hr'
  · have e : recF (n + 1) a b c = (some r, c) := by simp [recF, hg]
    rw [e]
    exact ⟨fun b' hb' => by simp at hb'; subst hb'; exact hc a b r hg, hc⟩

theorem eqv_stuck_left (b : Term) (y : M) (t : Term) : Sound (orElse (eqv .Stuck b) y) t := by
  intro c hc
  have e : orElse (eqv .Stuck b) y c = (none, c) := by cases b <;> rfl
  rw [e]; exact ⟨by simp, hc⟩

theorem eqv_stuck_right (a : Term) (y : M) (t : Term) : Sound (orElse (eqv a .Stuck) y) t := by
  intro c hc
  have e : orElse (eqv a .Stuck) y c = (none, c) := by cases a <;> rfl
  rw [e]; exact ⟨by simp, hc⟩

theorem asCat_none {a : Term} (h : asCat a = none) : ∀ x y, a ≠ cat x y := by
  rintro x y rfl; simp [asCat, cat] at h

theorem sound_body {n : Nat} (hn : AllSound n) (a b : Term) :
    Sound (recBody (n + 1) a b) (__str_re_includes_rec a b) := by
  obtain ⟨-, -, hC, hB, -⟩ := hn
  rw [recBody]
  split
  · rename_i r1 r2 r3 r4 ha hb
    obtain rfl := asCat_some ha
    obtain rfl := asCat_some hb
    simp only [eqTerm_iff]
    split
    · rename_i h2
      subst h2
      split
      · rename_i h4
        subst h4
        exact (sound_orElse (sound_eqv _ _) (hB _ _)).eq (rec_emp_emp _ _)
      · rename_i h4
        refine (sound_orElse (sound_eqv _ _) (hB _ _)).eq (rec_emp (by simp [cat]) ?_)
        intro x hx; simp [cat] at hx; exact h4 hx.2
    · rename_i h2
      split
      · rename_i h4
        subst h4
        exact (sound_orElse (sound_orElse (sound_eqv _ _) (hB _ _)) (hC _ _ _ _)).eq (rec_cat_emp h2)
      · rename_i h4
        exact (hC _ _ _ _).eq (rec_cat_cat h2 h4)
  · rename_i r1 r2 ha hb
    obtain rfl := asCat_some ha
    simp only [eqTerm_iff]
    split
    · rename_i h2
      subst h2
      by_cases hs : b = .Stuck
      · subst hs; exact eqv_stuck_right _ _ _
      · exact (sound_orElse (sound_eqv _ _) (hB _ _)).eq (rec_emp hs fun x => asCat_none hb x _)
    · exact sound_ofTerm _
  · rename_i r3 r4 ha hb
    obtain rfl := asCat_some hb
    simp only [eqTerm_iff]
    split
    · rename_i h4
      subst h4
      by_cases hs : a = .Stuck
      · subst hs; exact eqv_stuck_left _ _ _
      · exact (sound_orElse (sound_eqv _ _) (hB _ _)).eq (rec_any_emp hs (asCat_none ha))
    · exact sound_ofTerm _
  · exact sound_ofTerm _

theorem sound_twice {x : M} {t u : Term} (h : Sound x (__eo_ite t (.Boolean true) u)) :
    Sound x (__eo_ite t (.Boolean true) (__eo_ite t (.Boolean true) u)) := by
  refine h.eq ?_
  by_cases h1 : t = .Boolean true
  · subst h1; simp [ite_true]
  · by_cases h2 : t = .Boolean false
    · subst h2; simp [ite_false]
    · simp [__eo_ite, native_ite, native_teq, h1, h2]

theorem sound_concat {n : Nat} (hn : AllSound n) (r1 r2 r3 r4 : Term) :
    Sound (concatF (n + 1) r1 r2 r3 r4) (__str_re_includes_concat r1 r2 r3 r4) := by
  obtain ⟨hR, -, -, hB, -⟩ := hn
  rw [concatF]
  refine sound_nonStuck fun h1 => sound_nonStuck fun h2 => sound_nonStuck fun h3 => sound_nonStuck fun h4 => ?_
  refine Sound.eq ?_ (concat_eq h1 h2 h3 h4)
  exact sound_orElse (sound_andThen (sound_orElse (sound_eqv _ _) (hB _ _)) (sound_orElse (sound_eqv _ _) (hR _ _)))
    (sound_orElse (sound_andThen (sound_ofTerm _) (sound_twice (sound_orElse (sound_eqv _ _) (hR _ _))))
      (sound_tf (sound_andThen (sound_eqv _ _) (sound_orElse (sound_eqv _ _) (hR _ _)))))

theorem sound_base {n : Nat} (hn : AllSound n) (a b : Term) :
    Sound (baseF (n + 1) a b) (__str_re_includes_base_rec a b) := by
  obtain ⟨-, -, -, -, hU, hI, hS⟩ := hn
  unfold baseF
  refine sound_nonStuck fun ha => sound_nonStuck fun hb => ?_
  split
  · exact sound_ofTerm _
  · rename_i h
    refine (sound_ret false).eq (base_str rfl hb ?_)
    intro s hs; exact h s hs
  · exact sound_ofTerm _
  · rename_i h1 h2 h3
    refine Sound.eq ?_ (base_eq ha hb (fun s hs => h2 s hs) (fun s hs => h1 s hs) (fun _ _ _ _ e1 e2 => h3 _ _ _ _ e1 e2))
    exact sound_orElse (sound_eqTrue (hU _ _)) (sound_orElse (sound_eqTrue (hI _ _)) (sound_tf (sound_eqTrue (hS _ _))))

theorem sound_union {n : Nat} (hn : AllSound n) (a b : Term) :
    Sound (unionF (n + 1) a b) (__str_re_includes_lhs_union a b) := by
  obtain ⟨hR, -, -, -, hU, -⟩ := hn
  unfold unionF
  refine sound_nonStuck fun ha => sound_nonStuck fun hb => ?_
  split
  · refine (sound_orElse (sound_orElse (sound_eqv _ _) (hR _ _)) (hU _ _)).eq ?_
    rwa [__str_re_includes_lhs_union]
  · rename_i h
    refine (sound_ret false).eq ?_
    rw [__str_re_includes_lhs_union] <;> simp_all

theorem sound_inter {n : Nat} (hn : AllSound n) (a b : Term) :
    Sound (interF (n + 1) a b) (__str_re_includes_rhs_inter a b) := by
  obtain ⟨hR, -, -, -, -, hI, -⟩ := hn
  unfold interF
  refine sound_nonStuck fun ha => sound_nonStuck fun hb => ?_
  split
  · refine (sound_orElse (sound_orElse (sound_eqv _ _) (hR _ _)) (hI _ _)).eq ?_
    rwa [__str_re_includes_rhs_inter]
  · rename_i h
    refine (sound_ret false).eq ?_
    rw [__str_re_includes_rhs_inter] <;> simp_all

theorem sound_star {n : Nat} (hn : AllSound n) (a b : Term) :
    Sound (starF (n + 1) a b) (__str_re_includes_lhs_star a b) := by
  obtain ⟨hR, -⟩ := hn
  unfold starF
  refine sound_nonStuck fun ha => sound_nonStuck fun hb => ?_
  split
  · rename_i r1
    simp only [eqTerm_iff]
    split
    · rename_i h
      subst h
      refine (sound_ret true).eq ?_
      simp only [cat, emp]
      rwa [__str_re_includes_lhs_star]
    · rename_i h
      simp only [cat, emp] at h
      split
      · refine (sound_orElse (sound_eqv _ _) (hR _ _)).eq ?_
        rw [__str_re_includes_lhs_star]; simp_all
      · refine (sound_orElse (sound_eqv _ _) (hR _ _)).eq ?_
        rw [__str_re_includes_lhs_star] <;> simp_all
  · rename_i h
    refine (sound_ret false).eq ?_
    rw [__str_re_includes_lhs_star] <;> simp_all

theorem allSound : ∀ n, AllSound n
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> first
      | (rw [recF]; exact sound_none _)
      | (rw [recBody]; exact sound_none _)
      | (rw [concatF]; exact sound_none _)
      | (rw [baseF]; exact sound_none _)
      | (rw [unionF]; exact sound_none _)
      | (rw [interF]; exact sound_none _)
      | (rw [starF]; exact sound_none _)
  | n + 1 =>
    have hn := allSound n
    ⟨fun a b => sound_memo (hn.2.1 a b), sound_body hn, sound_concat hn, sound_base hn, sound_union hn,
      sound_inter hn, sound_star hn⟩

theorem includes_sound {a b : Term} (h : includes a b = true) :
    __eo_ite (__eo_eq (__re_flatten (.Boolean true) a) (__re_flatten (.Boolean true) b)) (.Boolean true)
      (__str_re_includes_rec (__re_flatten (.Boolean true) a) (__re_flatten (.Boolean true) b)) = .Boolean true := by
  unfold includes at h
  simp only [beq_iff_eq] at h
  exact (sound_orElse (sound_eqv _ _) ((allSound fuel).1 _ _) {} good_empty).1 true h

/-! ## The steps -/

open Template LenConcat

/-- The rules' programs, on an inclusion. -/
theorem prog_inter {r s : Term} (h : includes s r = true) :
    let F := eoApp2 .eq (eoApp2 .re_inter r (eoApp2 .re_inter (.Apply (.UOp .re_comp) s) (.UOp .re_all))) (.UOp .re_none)
    __eo_prog_re_inter_inclusion F = F := by
  have := includes_sound h
  simp only [eoApp2, __eo_prog_re_inter_inclusion]
  rw [this, requires_true]

theorem prog_union {r s : Term} (h : includes r s = true) :
    let F := eoApp2 .eq (eoApp2 .re_union r (eoApp2 .re_union (.Apply (.UOp .re_comp) s) (.UOp .re_none)))
      (.Apply (.UOp .re_mult) (.UOp .re_allchar))
    __eo_prog_re_union_inclusion F = F := by
  have := includes_sound h
  simp only [eoApp2, __eo_prog_re_union_inclusion]
  rw [this, requires_true]

theorem toEo_comp (a : Node) : (Node.mkNode .REGEXP_COMPLEMENT #[a]).toEo = .Apply (.UOp .re_comp) a.toEo :=
  toEo_spine1 rfl a

theorem toEo_inter (r s : Node) : (node true r s).toEo =
    eoApp2 .re_inter r.toEo (eoApp2 .re_inter (.Apply (.UOp .re_comp) s.toEo) (.UOp .re_all)) := by
  show (Node.app (.kind .REGEXP_INTER) _).toEo = _
  rw [Node.toEo_app, ← toEo_comp]; rfl

theorem toEo_union (r s : Node) : (node false r s).toEo =
    eoApp2 .re_union r.toEo (eoApp2 .re_union (.Apply (.UOp .re_comp) s.toEo) (.UOp .re_none)) := by
  show (Node.app (.kind .REGEXP_UNION) _).toEo = _
  rw [Node.toEo_app, ← toEo_comp]; rfl

theorem toEo_result (inter : Bool) : (result inter).toEo =
    if inter then .UOp .re_none else .Apply (.UOp .re_mult) (.UOp .re_allchar) := by
  cases inter
  · show (Node.mkNode .REGEXP_STAR #[Node.mkNode .REGEXP_ALLCHAR #[]]).toEo = _
    rw [show (Node.mkNode .REGEXP_STAR #[Node.mkNode .REGEXP_ALLCHAR #[]]).toEo =
      .Apply (.UOp .re_mult) (Node.mkNode .REGEXP_ALLCHAR #[]).toEo from toEo_spine1 rfl _]
    rw [Node.mkNode, Node.toEo_app]; rfl
  · show (Node.mkNode .REGEXP_NONE #[]).toEo = _
    rw [Node.mkNode, Node.toEo_app]; rfl

end ReIncl

open ReIncl Template in
/-- **An inclusion step is a CPC step.** -/
theorem reIncl_provesEq [LogosFacts] {inter : Bool} {r s n m : Node} (h : ReIncl.Ok inter r s n m) :
    ProvesEq ((StaticProc.reIncl inter r s).cmds n m) n m := by
  obtain ⟨rfl, rfl, hty, hi⟩ := h
  have hty' : __smtx_typeof (__eo_to_smt (eqFormula (node inter r s) (result inter))) = SmtType.Bool := by
    rw [Node.smtTypeF_eq] at hty
    rw [← toEo_eq]; exact hty
  have ht : eoHasSmtTranslation (eqFormula (node inter r s) (result inter)) := by
    rw [eoHasSmtTranslation, hty']; simp
  cases inter
  · refine provesEq_one (r := .re_union_inclusion) ⟨ht, trivial⟩ ?_ hty'
    show __eo_prog_re_union_inclusion (eqFormula _ _) = _
    rw [eqFormula, toEo_union, toEo_result]
    exact prog_union hi
  · refine provesEq_one (r := .re_inter_inclusion) ⟨ht, trivial⟩ ?_ hty'
    show __eo_prog_re_inter_inclusion (eqFormula _ _) = _
    rw [eqFormula, toEo_inter, toEo_result]
    exact prog_inter hi

end Telos
