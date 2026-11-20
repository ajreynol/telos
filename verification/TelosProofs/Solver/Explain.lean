import TelosProofs.Solver.EqProof
import Telos.Solver.Explain

/-!
# Verified explanations are sound

`EE.qFull C n x y` (`Telos/Solver/Explain.lean`) appends reasons to the state's
output. If it succeeds, then for every set of literals `L` that contains the
output and is *good* (Boolean, with a stable condition, and well-typed roots),
the terms of `x` and `y` are equal in every well-formed model of `L`
(`qFull_sound`). Likewise for the argument prefixes of internal nodes
(`qArgs_sound`), position by position.

The proof is by induction on the fuel, in layers: the claims of the queries
at fuel `n` give those of the edges and steps at fuel `n`, which give those of
the queries at fuel `n + 1`. The claims hold whatever the engine's state: they
rest only on the checks the explanation makes:
- an asserted edge: its reason relates its terms (`assume_sound`);
- a congruence edge: the application at `cur` is well typed (a path from a
  root), its arguments are related as the explanations of the arguments say
  (`argsMatch`), so congruence under a stable condition relates the
  applications (`shape_condCongr`);
- a reflexivity edge: `(= a b)` is well typed and `a`, `b` are related, so it
  equals `true` (`condEquiv_true`);
- a path: consecutive steps share their nodes (`chainOk`), so their claims
  compose by transitivity; positions compose likewise (`Rel.compose`).
The caches hold only claims already proven, for every good extension of the
output, which grows.
-/

open Eo Smtm SmtEval

namespace Telos.Solver.EE

open Telos.Solver

set_option linter.unusedSectionVars false

variable [LogosFacts]

/-- `L` is good for `C`: Boolean literals with a stable condition, and
well-typed roots. -/
structure Good (C : ExCtx) (L : Array Node) : Prop where
  bool : ∀ l ∈ L.toList, HasBoolType l.toEo
  stable : StableCond (Holds L)
  roots : ∀ r ∈ C.roots.toList, r.WellTyped

/-- The claim of a query between terms. -/
def FullOk (C : ExCtx) (L : Array Node) (x y : Nat) : Prop :=
  x = y ∨ CondEquiv (Holds L) (C.node x).toEo (C.node y).toEo

def RelOk (L : Array Node) : Rel → Prop
  | .same => True
  | .eq a b => CondEquiv (Holds L) a.toEo b.toEo

def RelsOk (L : Array Node) (rs : List Rel) : Prop := ∀ r ∈ rs, RelOk L r

/-- `L` contains the output of `s`. -/
def Ext (s : ExState) (L : Array Node) : Prop := ∀ l ∈ s.out.toList, l ∈ L.toList

def Sub (s s' : ExState) : Prop := ∀ l ∈ s.out.toList, l ∈ s'.out.toList

/-- The caches hold proven claims, for every good extension of the output. -/
def Inv (C : ExCtx) (s : ExState) : Prop :=
  ∀ L, Ext s L → Good C L →
    (∀ x y, s.fullCache.contains (x, y) = true → FullOk C L x y) ∧
    (∀ x y rs, s.argsCache.get? (x, y) = some rs → RelsOk L rs)

theorem sub_refl (s : ExState) : Sub s s := fun _ h => h

theorem sub_trans {a b c : ExState} (h₁ : Sub a b) (h₂ : Sub b c) : Sub a c :=
  fun l h => h₂ l (h₁ l h)

theorem ext_of_sub {s s' : ExState} {L : Array Node} (h : Sub s s') (hL : Ext s' L) : Ext s L :=
  fun l hl => hL l (h l hl)

theorem inv_of_sub {C : ExCtx} {s s' : ExState} (hI : Inv C s) (h : Sub s s')
    (hf : s'.fullCache = s.fullCache) (ha : s'.argsCache = s.argsCache) : Inv C s' := by
  intro L hL hG
  rw [hf, ha]
  exact hI L (ext_of_sub h hL) hG

/-! ## Claims -/

theorem fullOk_trans {C : ExCtx} {L : Array Node} {x y z : Nat} (h₁ : FullOk C L x y)
    (h₂ : FullOk C L y z) : FullOk C L x z := by
  rcases h₁ with rfl | h₁
  · exact h₂
  · rcases h₂ with rfl | h₂
    · exact .inr h₁
    · exact .inr (h₁.trans h₂)

theorem fullOk_symm {C : ExCtx} {L : Array Node} {x y : Nat} (h : FullOk C L x y) :
    FullOk C L y x := by
  rcases h with rfl | h
  · exact .inl rfl
  · exact .inr (condEquiv_symm h)

/-- A path whose steps hold, chained from `x` to `y`, makes `x` and `y` equal. -/
theorem chain_sound {C : ExCtx} {L : Array Node} :
    ∀ (x : Nat) (path : List (Nat × Nat × Edge)) (y : Nat), chainOk x path y = true →
      (∀ st ∈ path, FullOk C L st.1 st.2.1) → FullOk C L x y
  | x, [], y, h, _ => by
    simp only [chainOk, beq_iff_eq] at h; exact .inl h
  | x, (c, n, e) :: rest, y, h, hs => by
    simp only [chainOk, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, h⟩ := h
    exact fullOk_trans (hs _ (List.mem_cons_self ..))
      (chain_sound n rest y h fun st hst => hs st (List.mem_cons_of_mem _ hst))

theorem rel_compose_sound {L : Array Node} {r q x : Rel} (h : r.compose q = some x)
    (hr : RelOk L r) (hq : RelOk L q) : RelOk L x := by
  cases r <;> cases q <;> simp only [Rel.compose, Option.some.injEq] at h
  · subst h; trivial
  · subst h; exact hq
  · subst h; exact hr
  · rename_i a b c d
    split at h
    · rename_i hbc
      simp only [Option.some.injEq] at h; subst h
      have : b = c := by simpa using hbc
      subst this
      exact CondEquiv.trans hr hq
    · simp at h

theorem composeAll_sound {L : Array Node} :
    ∀ (a b c : List Rel), composeAll a b = some c → RelsOk L a → RelsOk L b → RelsOk L c
  | [], [], c, h, _, _ => by simp [composeAll] at h; subst h; intro r hr; simp at hr
  | r :: rs, q :: qs, c, h, ha, hb => by
    simp only [composeAll, Option.bind_eq_bind, Option.bind_eq_some_iff, pure,
      Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact rel_compose_sound hx (ha _ (List.mem_cons_self ..)) (hb _ (List.mem_cons_self ..))
    · exact composeAll_sound rs qs xs hxs (fun r hr => ha r (List.mem_cons_of_mem _ hr))
        (fun r hr => hb r (List.mem_cons_of_mem _ hr)) z hz
  | [], _ :: _, _, h, _, _ => by simp [composeAll] at h
  | _ :: _, [], _, h, _, _ => by simp [composeAll] at h

/-- Folding the composition of the steps keeps the claims. -/
theorem foldr_compose_sound {L : Array Node} :
    ∀ (steps : List (List Rel)) (init : List Rel) (rs : List Rel),
      steps.foldr (fun st acc => acc.bind fun a => composeAll a st) (some init) = some rs →
      RelsOk L init → (∀ st ∈ steps, RelsOk L st) → RelsOk L rs
  | [], init, rs, h, hi, _ => by simp at h; subst h; exact hi
  | st :: rest, init, rs, h, hi, hs => by
    simp only [List.foldr_cons, Option.bind_eq_some_iff] at h
    obtain ⟨a, ha, h⟩ := h
    exact composeAll_sound a st rs h
      (foldr_compose_sound rest init a ha hi fun s hs' => hs s (List.mem_cons_of_mem _ hs'))
      (hs st (List.mem_cons_self ..))

/-! ## Edges -/

/-- An asserted edge: its reason, among `L`, relates its terms. -/
theorem assumption_edge {C : ExCtx} {L : Array Node} (hG : Good C L) {r : Node} (hr : r ∈ L.toList)
    {cur next : Nat}
    (h : (EqProof.assumptionEq r == (C.node cur, C.node next) ||
      EqProof.assumptionEq r == (C.node next, C.node cur)) = true) : FullOk C L cur next := by
  have ha := assume_sound hG.bool hr
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · rw [h] at ha; exact .inr ha
  · rw [h] at ha; exact .inr (condEquiv_symm ha)

omit [LogosFacts] in
theorem typeof_eq_bool_of_ne {T U : SmtType} (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    __smtx_typeof_eq T U = SmtType.Bool := by
  unfold __smtx_typeof_eq __smtx_typeof_guard at *
  by_cases hT : T = SmtType.None <;> by_cases hTU : T = U <;>
    simp_all [native_ite, native_Teq]

/-- A term reached from a root is well typed. -/
theorem typedBelowRoot_wellTyped {C : ExCtx} {L : Array Node} (hG : Good C L) {t : Node}
    (h : C.typedBelowRoot t = true) : t.WellTyped := by
  unfold ExCtx.typedBelowRoot at h
  split at h
  · rename_i p _
    split at h
    · rename_i r hr
      have hf : EqProof.follow r p.path = some t := by simpa using h
      exact follow_wellTyped r p.path t hf (hG.roots r (mem_of_getElem? hr))
    · simp at h
  · simp at h

/-- A well-typed equality is Boolean. -/
theorem hasBoolType_of_eq_wellTyped {a b : Node} (h : (Node.eqNode a b).WellTyped) :
    HasBoolType (mkEq a.toEo b.toEo) := by
  unfold Node.WellTyped Node.smtType Node.toSmt at h
  rw [show (Node.eqNode a b).toEo = mkEq a.toEo b.toEo from toEo_eqNode a b] at h
  unfold HasBoolType
  change __smtx_typeof (SmtTerm.eq _ _) = _
  change __smtx_typeof (SmtTerm.eq _ _) ≠ _ at h
  rw [typeof_eq_eq] at h ⊢
  exact typeof_eq_bool_of_ne h

/-- A reflexivity edge: a well-typed `(= a b)`, with `a` and `b` related, is
`true`. -/
theorem refl_edge {C : ExCtx} {L : Array Node} (hG : Good C L) {a b : Node}
    (ht : C.typedBelowRoot (Node.eqNode a b) = true)
    (hab : a = b ∨ CondEquiv (Holds L) a.toEo b.toEo) :
    CondEquiv (Holds L) (Node.eqNode a b).toEo Node.mkTrue.toEo := by
  have hb := hasBoolType_of_eq_wellTyped (typedBelowRoot_wellTyped hG ht)
  rw [show (Node.eqNode a b).toEo = mkEq a.toEo b.toEo from toEo_eqNode a b, toEo_true]
  refine condEquiv_true hb fun M hM hH => ?_
  rcases hab with rfl | hab
  · exact (trueIn_mkEq_iff M _ _).2 (LogosFacts.value_rel_refl _)
  · exact hab.2 M hM hH

/-- The arguments related as `argsMatch` says are related pairwise. -/
theorem argsMatch_forall₂ {L : Array Node} {cs ds : Array Node} {rs : List Rel}
    (hm : argsMatch cs ds rs = true) (hrs : RelsOk L rs) (hcs : ∀ c ∈ cs.toList, c.WellTyped) :
    List.Forall₂ (CondEquiv (Holds L)) (cs.toList.map Node.toEo) (ds.toList.map Node.toEo) := by
  unfold argsMatch at hm
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at hm
  obtain ⟨⟨hlr, hlcd⟩, hall⟩ := hm
  rw [List.forall₂_iff_get]
  refine ⟨by simp [hlcd], fun i h₁ h₂ => ?_⟩
  simp only [List.length_map, Array.length_toList] at h₁ h₂
  simp only [List.get_eq_getElem, List.getElem_map, Array.getElem_toList]
  have hi := hall i h₁
  have hr : rs[i]? = some rs[i] := List.getElem?_eq_getElem (by omega)
  rw [hr, Array.getElem?_eq_getElem h₁, Array.getElem?_eq_getElem h₂] at hi
  have hrm : rs[i] ∈ rs := List.getElem_mem (by omega)
  have hok := hrs _ hrm
  cases hri : rs[i] with
  | same =>
    rw [hri] at hi
    have : cs[i] = ds[i] := by simpa using hi
    rw [← this]
    exact CondEquiv.refl _ (hcs _ (Array.mem_toList_iff.2 (Array.getElem_mem h₁)))
  | eq a b =>
    rw [hri] at hi hok
    simp only [Bool.and_eq_true, beq_iff_eq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    exact hok

/-- A congruence edge between applications: the application `t` is reached
from a root, its operator allows congruence, and the arguments are related as
the explanations of the arguments say. -/
theorem congruence_edge {C : ExCtx} {L : Array Node} (hG : Good C L) {op : Op} {cs ds : Array Node}
    {rs : List Rel} (hsh : op.eoShape.substCongruent = true) (hc : op.childrenTypedOfParent = true)
    (ht : C.typedBelowRoot (.app op cs) = true) (hm : argsMatch cs ds rs = true) (hrs : RelsOk L rs) :
    CondEquiv (Holds L) (Node.app op cs).toEo (Node.app op ds).toEo := by
  have hwt := typedBelowRoot_wellTyped hG ht
  have hcs := ChildTyping.children_wellTyped hc hwt
  have hrel := argsMatch_forall₂ hm hrs hcs
  rw [Node.toEo_app, Node.toEo_app]
  refine shape_condCongr hG.stable _ hsh hrel ?_
  have := hwt; unfold Node.WellTyped Node.smtType Node.toSmt at this
  rwa [Node.toEo_app] at this

/-! ## The monad -/

omit [LogosFacts] in
theorem bind_eq_some {α β : Type} {m : ExM α} {f : α → ExM β} {s s' : ExState} {b : β} :
    StateT.bind m f s = some (b, s') ↔ ∃ a s₁, m s = some (a, s₁) ∧ f a s₁ = some (b, s') := by
  simp only [StateT.bind]
  constructor
  · intro h
    cases hm : m s with
    | none => simp [hm] at h
    | some p => obtain ⟨a, s₁⟩ := p; exact ⟨a, s₁, rfl, by simpa [hm] using h⟩
  · rintro ⟨a, s₁, hm, hf⟩; simp [hm, hf]

omit [LogosFacts] in
theorem bind_eq_some' {α β : Type} {m : ExM α} {f : α → ExM β} {s s' : ExState} {b : β} :
    (m >>= f) s = some (b, s') ↔ ∃ a s₁, m s = some (a, s₁) ∧ f a s₁ = some (b, s') :=
  bind_eq_some

omit [LogosFacts] in
theorem get_apply (s : ExState) : (get : ExM ExState) s = some (s, s) := rfl

omit [LogosFacts] in
theorem modify_apply (f : ExState → ExState) (s : ExState) :
    (modify f : ExM Unit) s = some ((), f s) := rfl

omit [LogosFacts] in
theorem pure_apply {α : Type} (a : α) (s : ExState) : (pure a : ExM α) s = some (a, s) := rfl

omit [LogosFacts] in
theorem fail_apply {α : Type} (s : ExState) : (fail : ExM α) s = none := rfl

omit [LogosFacts] in
theorem ite_t {α : Sort _} {c : Bool} {a b : α} (h : c = true) : (if c = true then a else b) = a := by
  simp [h]

omit [LogosFacts] in
theorem ite_f {α : Sort _} {c : Bool} {a b : α} (h : ¬ c = true) : (if c = true then a else b) = b := by
  simp [h]

/-- The claims of the queries at fuel `n`. -/
def QF (C : ExCtx) (n : Nat) : Prop :=
  ∀ x y s s', qFull C n x y s = some ((), s') → Inv C s →
    Inv C s' ∧ Sub s s' ∧ ∀ L, Ext s' L → Good C L → FullOk C L x y

def QA (C : ExCtx) (n : Nat) : Prop :=
  ∀ x y s rs s', qArgs C n x y s = some (rs, s') → Inv C s →
    Inv C s' ∧ Sub s s' ∧ ∀ L, Ext s' L → Good C L → RelsOk L rs

/-- A query that does not change the state's cache keeps the invariant. -/
theorem inv_push {C : ExCtx} {s : ExState} (hI : Inv C s) (r : Node) :
    Inv C { s with out := s.out.push r } :=
  inv_of_sub hI (fun l hl => by simp [hl]) rfl rfl

theorem preArgs_sound {C : ExCtx} {n : Nat} (hF : QF C n) (hA : QA C n) (f₁ f₂ : FunApp) (k : Nat)
    (s s' : ExState) (rs : List Rel) (h : preArgs C n f₁ f₂ k s = some (rs, s')) (hI : Inv C s) :
    Inv C s' ∧ Sub s s' ∧ ∀ L, Ext s' L → Good C L → RelsOk L rs := by
  unfold preArgs at h
  cases hty : f₁.type
  · simp only [hty] at h
    rw [bind_eq_some'] at h
    obtain ⟨_, s₁, h₁, h₂⟩ := h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h₂
    obtain ⟨rfl, rfl⟩ := h₂
    obtain ⟨hI₁, hS₁, hC₁⟩ := hF _ _ _ _ h₁ hI
    refine ⟨hI₁, hS₁, fun L hL hG r hr => ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    split
    · trivial
    · rename_i hne
      rcases hC₁ L hL hG with heq | hc
      · exact absurd (by simp [heq]) hne
      · exact hc
  all_goals
    simp only [hty] at h
    split at h
    · split at h
      · simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hI, sub_refl _, fun _ _ _ r hr => by simp at hr⟩
      · simp [fail_apply] at h
    · exact hA _ _ _ _ _ h hI

omit [LogosFacts] in
theorem bind_failure {α β : Type} {f : α → ExM β} {s s' : ExState} {b : β} :
    ((fail : ExM α) >>= f) s ≠ some (b, s') := by
  rw [Ne, bind_eq_some']; rintro ⟨_, _, h, _⟩; simp [fail_apply] at h

/-- The relation of the last arguments, from their query. -/
theorem last_rel {C : ExCtx} {L : Array Node} {x y : Nat} (h : FullOk C L x y) :
    RelOk L (if (x == y) = true then Rel.same else .eq (C.node x) (C.node y)) := by
  split
  · trivial
  · rename_i hne
    rcases h with heq | hc
    · exact absurd (by simp [heq]) hne
    · exact hc

theorem edgeFull_sound {C : ExCtx} {n : Nat} (hF : QF C n) (hA : QA C n) (cur next : Nat) (e : Edge)
    (s s' : ExState) (h : edgeFull C n cur next e s = some ((), s')) (hI : Inv C s) :
    Inv C s' ∧ Sub s s' ∧ ∀ L, Ext s' L → Good C L → FullOk C L cur next := by
  unfold edgeFull at h
  cases he : e.type <;> rw [he] at h <;> dsimp only at h
  · -- congruence
    cases hf₁ : C.app cur with
    | none => rw [hf₁] at h; exact absurd h (by simp [fail_apply])
    | some f₁ =>
    cases hf₂ : C.app next with
    | none => rw [hf₁, hf₂] at h; exact absurd h (by simp [fail_apply])
    | some f₂ =>
    rw [hf₁, hf₂] at h
    dsimp only at h
    cases hcur : C.node cur with
    | const _ | var _ _ | boundVar _ _ | skolem _ _ =>
      rw [hcur] at h; exact absurd h (by simp [fail_apply])
    | app op cs =>
    rw [hcur] at h
    dsimp only at h
    cases hnext : C.node next with
    | const _ | var _ _ | boundVar _ _ | skolem _ _ =>
      rw [hnext] at h; exact absurd h (by simp [fail_apply])
    | app op' ds =>
    rw [hnext] at h
    dsimp only at h
    by_cases hop : (op != op') = true
    · rw [ite_t hop] at h; exact absurd h bind_failure
    rw [ite_f hop] at h
    by_cases hsh : (!(op.eoShape.substCongruent && op.childrenTypedOfParent)) = true
    · rw [ite_t hsh] at h; exact absurd h bind_failure
    rw [ite_f hsh] at h
    by_cases hty : (!C.typedBelowRoot (Node.app op cs)) = true
    · rw [ite_t hty] at h; exact absurd h bind_failure
    rw [ite_f hty] at h
    rw [bind_eq_some'] at h
    obtain ⟨pre, s₁, h₁, h⟩ := h
    rw [bind_eq_some'] at h
    obtain ⟨_, s₂, h₂, h⟩ := h
    by_cases hm : (!argsMatch cs ds (pre ++ [if (f₁.b == f₂.b) = true then Rel.same
        else Rel.eq (C.node f₁.b) (C.node f₂.b)])) = true
    · rw [ite_t hm] at h; exact absurd h (by simp [fail_apply])
    rw [ite_f hm] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨hI₁, hS₁, hC₁⟩ := preArgs_sound hF hA _ _ _ _ _ _ h₁ hI
    obtain ⟨hI₂, hS₂, hC₂⟩ := hF _ _ _ _ h₂ hI₁
    refine ⟨hI₂, sub_trans hS₁ hS₂, fun L hL hG => .inr ?_⟩
    have hop' : op = op' := by simpa using hop
    subst hop'
    have hsh' : op.eoShape.substCongruent = true ∧ op.childrenTypedOfParent = true := by
      simpa using hsh
    have hty' : C.typedBelowRoot (.app op cs) = true := by simpa using hty
    have hm' := (by simpa using hm : argsMatch cs ds _ = true)
    rw [hcur, hnext]
    refine congruence_edge hG hsh'.1 hsh'.2 hty' hm' ?_
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hC₁ L (ext_of_sub hS₂ hL) hG r hr
    · simp only [List.mem_singleton] at hr; subst hr
      have := last_rel (hC₂ L hL hG)
      simpa using this
  · -- equality
    by_cases hab : (EqProof.assumptionEq e.reason == (C.node cur, C.node next) ||
        EqProof.assumptionEq e.reason == (C.node next, C.node cur)) = true
    · rw [ite_t hab] at h
      simp only [modify_apply, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨inv_push hI _, fun l hl => by simp [hl], fun L hL hG => ?_⟩
      exact assumption_edge hG (hL _ (by simp)) hab
    · rw [ite_f hab] at h; exact absurd h (by simp [fail_apply])
  · -- reflexivity
    generalize hk : (if (cur == C.ee.trueId) = true then next else cur) = k at h
    cases hf : C.app k with
    | none => rw [hf] at h; exact absurd h (by simp [fail_apply])
    | some f =>
    rw [hf] at h
    dsimp only at h
    by_cases h₁ : (f.type != AppType.equality) = true
    · rw [ite_t h₁] at h; exact absurd h bind_failure
    rw [ite_f h₁] at h
    by_cases htrue : (C.node C.ee.trueId != Node.mkTrue) = true
    · rw [ite_t htrue] at h; exact absurd h bind_failure
    rw [ite_f htrue] at h
    by_cases heq : (C.node k != Node.eqNode (C.node f.a) (C.node f.b)) = true
    · rw [ite_t heq] at h; exact absurd h bind_failure
    rw [ite_f heq] at h
    by_cases hty : (!C.typedBelowRoot (C.node k)) = true
    · rw [ite_t hty] at h; exact absurd h bind_failure
    rw [ite_f hty] at h
    by_cases hend : (!(cur == C.ee.trueId || next == C.ee.trueId)) = true
    · rw [ite_t hend] at h; exact absurd h bind_failure
    rw [ite_f hend] at h
    obtain ⟨hI₁, hS₁, hC₁⟩ := hF _ _ _ _ h hI
    refine ⟨hI₁, hS₁, fun L hL hG => ?_⟩
    have htrue' : C.node C.ee.trueId = Node.mkTrue := by simpa using htrue
    have heq' : C.node k = Node.eqNode (C.node f.a) (C.node f.b) := by simpa using heq
    have hty' : C.typedBelowRoot (Node.eqNode (C.node f.a) (C.node f.b)) = true := by
      rw [← heq']; simpa using hty
    have hab : C.node f.a = C.node f.b ∨
        CondEquiv (Holds L) (C.node f.a).toEo (C.node f.b).toEo := by
      rcases hC₁ L hL hG with h' | h'
      · exact .inl (by rw [h'])
      · exact .inr h'
    have hc := refl_edge hG hty' hab
    rw [← heq', ← htrue'] at hc
    by_cases hct : cur = C.ee.trueId
    · have : k = next := by rw [← hk]; simp [hct]
      subst this
      rw [hct]; exact .inr (condEquiv_symm hc)
    · have : k = cur := by rw [← hk]; simp [hct]
      subst this
      have hnt : next = C.ee.trueId := by simpa [hct] using hend
      rw [hnt]; exact .inr hc
  · -- constants
    exact absurd h (by simp [fail_apply])

theorem stepsFull_sound {C : ExCtx} {n : Nat} (hF : QF C n) (hA : QA C n) :
    ∀ (path : List (Nat × Nat × Edge)) (s s' : ExState), stepsFull C n path s = some ((), s') →
      Inv C s → Inv C s' ∧ Sub s s' ∧ ∀ L, Ext s' L → Good C L →
        ∀ st ∈ path, FullOk C L st.1 st.2.1
  | [], s, s', h, hI => by
    unfold stepsFull at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hI, sub_refl _, fun _ _ _ st hst => by simp at hst⟩
  | (cur, next, e) :: rest, s, s', h, hI => by
    unfold stepsFull at h
    rw [bind_eq_some'] at h
    obtain ⟨_, s₁, h₁, h₂⟩ := h
    obtain ⟨hI₁, hS₁, hC₁⟩ := edgeFull_sound hF hA cur next e s s₁ h₁ hI
    obtain ⟨hI₂, hS₂, hC₂⟩ := stepsFull_sound hF hA rest s₁ s' h₂ hI₁
    refine ⟨hI₂, sub_trans hS₁ hS₂, fun L hL hG st hst => ?_⟩
    rcases List.mem_cons.1 hst with rfl | hst
    · exact hC₁ L (ext_of_sub hS₂ hL) hG
    · exact hC₂ L hL hG st hst

theorem edgeArgs_sound {C : ExCtx} {n : Nat} (hF : QF C n) (hA : QA C n) (cur next : Nat) (e : Edge)
    (s s' : ExState) (rs : List Rel) (h : edgeArgs C n cur next e s = some (rs, s')) (hI : Inv C s) :
    Inv C s' ∧ Sub s s' ∧ ∀ L, Ext s' L → Good C L → RelsOk L rs := by
  unfold edgeArgs at h
  by_cases hty : (e.type != MergeReason.congruence) = true
  · rw [ite_t hty] at h; exact absurd h bind_failure
  rw [ite_f hty] at h
  cases hf₁ : C.app cur with
  | none => rw [hf₁] at h; exact absurd h (by simp [fail_apply])
  | some f₁ =>
  cases hf₂ : C.app next with
  | none => rw [hf₁, hf₂] at h; exact absurd h (by simp [fail_apply])
  | some f₂ =>
  rw [hf₁, hf₂] at h
  dsimp only at h
  -- the prefix: the explanation of internal nodes, or nothing for the same operator
  have key : ∀ (m : ExM (List Rel)) (pre : List Rel → Prop),
      (∀ s₁ ps, m s = some (ps, s₁) → Inv C s₁ ∧ Sub s s₁ ∧ ∀ L, Ext s₁ L → Good C L → RelsOk L ps) →
      (do let pre ← m; qFull C n f₁.b f₂.b
          pure (pre ++ [if (f₁.b == f₂.b) = true then Rel.same else Rel.eq (C.node f₁.b) (C.node f₂.b)])) s =
        some (rs, s') →
      Inv C s' ∧ Sub s s' ∧ ∀ L, Ext s' L → Good C L → RelsOk L rs := by
    intro m _ hm h
    rw [bind_eq_some'] at h
    obtain ⟨pre, s₁, h₁, h⟩ := h
    rw [bind_eq_some'] at h
    obtain ⟨_, s₂, h₂, h⟩ := h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hI₁, hS₁, hC₁⟩ := hm _ _ h₁
    obtain ⟨hI₂, hS₂, hC₂⟩ := hF _ _ _ _ h₂ hI₁
    refine ⟨hI₂, sub_trans hS₁ hS₂, fun L hL hG r hr => ?_⟩
    rcases List.mem_append.1 hr with hr | hr
    · exact hC₁ L (ext_of_sub hS₂ hL) hG r hr
    · simp only [List.mem_singleton] at hr; subst hr
      exact last_rel (hC₂ L hL hG)
  by_cases hp : (C.app f₁.a).isSome = true
  · rw [ite_t hp] at h
    exact key _ (fun _ => True) (fun s₁ ps h₁ => hA _ _ _ _ _ h₁ hI) h
  rw [ite_f hp] at h
  by_cases ha : (f₁.a == f₂.a) = true
  · rw [ite_t ha] at h
    refine key _ (fun _ => True) (fun s₁ ps h₁ => ?_) h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h₁
    obtain ⟨rfl, rfl⟩ := h₁
    exact ⟨hI, sub_refl _, fun _ _ _ r hr => by simp at hr⟩
  · rw [ite_f ha] at h; exact absurd h bind_failure

theorem stepsArgs_sound {C : ExCtx} {n : Nat} (hF : QF C n) (hA : QA C n) :
    ∀ (path : List (Nat × Nat × Edge)) (s s' : ExState) (steps : List (List Rel)),
      stepsArgs C n path s = some (steps, s') →
      Inv C s → Inv C s' ∧ Sub s s' ∧ ∀ L, Ext s' L → Good C L → ∀ st ∈ steps, RelsOk L st
  | [], s, s', steps, h, hI => by
    unfold stepsArgs at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, sub_refl _, fun _ _ _ st hst => by simp at hst⟩
  | (cur, next, e) :: rest, s, s', steps, h, hI => by
    unfold stepsArgs at h
    rw [bind_eq_some'] at h
    obtain ⟨r, s₁, h₁, h⟩ := h
    rw [bind_eq_some'] at h
    obtain ⟨rs, s₂, h₂, h⟩ := h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hI₁, hS₁, hC₁⟩ := edgeArgs_sound hF hA cur next e s s₁ r h₁ hI
    obtain ⟨hI₂, hS₂, hC₂⟩ := stepsArgs_sound hF hA rest s₁ _ rs h₂ hI₁
    refine ⟨hI₂, sub_trans hS₁ hS₂, fun L hL hG st hst => ?_⟩
    rcases List.mem_cons.1 hst with rfl | hst
    · exact hC₁ L (ext_of_sub hS₂ hL) hG
    · exact hC₂ L hL hG st hst

/-- The queries between terms at fuel `n + 1`. -/
theorem qFull_succ {C : ExCtx} {n : Nat} (hF : QF C n) (hA : QA C n) : QF C (n + 1) := by
  intro x y s s' h hI
  rw [qFull] at h
  by_cases hxy : (x == y) = true
  · rw [ite_t hxy] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hI, sub_refl _, fun _ _ _ => .inl (by simpa using hxy)⟩
  rw [ite_f hxy] at h
  rw [bind_eq_some'] at h
  obtain ⟨g, s₁, hg, h⟩ := h
  rw [get_apply] at hg
  simp only [Option.some.injEq, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  by_cases hc : (s.fullCache.contains (x, y)) = true
  · rw [ite_t hc] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨hI, sub_refl _, fun L hL hG => (hI L hL hG).1 x y hc⟩
  rw [ite_f hc] at h
  cases hp : findPath C.ee x y with
  | none => rw [hp] at h; exact absurd h (by simp [fail_apply])
  | some path =>
  rw [hp] at h
  dsimp only at h
  by_cases hch : (!chainOk x path.toList y) = true
  · rw [ite_t hch] at h; exact absurd h bind_failure
  rw [ite_f hch] at h
  rw [bind_eq_some'] at h
  obtain ⟨_, s₂, h₂, h⟩ := h
  simp only [modify_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  obtain ⟨hI₂, hS₂, hC₂⟩ := stepsFull_sound hF hA _ _ _ h₂ hI
  have hchain : chainOk x path.toList y = true := by simpa using hch
  have hclaim : ∀ L, Ext s₂ L → Good C L → FullOk C L x y := fun L hL hG =>
    chain_sound x path.toList y hchain fun st hst => hC₂ L hL hG st (List.mem_reverse.2 hst)
  refine ⟨?_, hS₂, hclaim⟩
  intro L hL hG
  obtain ⟨hf, ha⟩ := hI₂ L hL hG
  refine ⟨fun a b hab => ?_, ha⟩
  rw [Std.HashSet.contains_insert] at hab
  rcases Bool.or_eq_true_iff.1 hab with hab | hab
  · have : (x, y) = (a, b) := by simpa using hab
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
    exact hclaim L hL hG
  · exact hf a b hab

/-- The queries between internal nodes at fuel `n + 1`. -/
theorem qArgs_succ {C : ExCtx} {n : Nat} (hF : QF C n) (hA : QA C n) : QA C (n + 1) := by
  intro x y s rs s' h hI
  rw [qArgs] at h
  rw [bind_eq_some'] at h
  obtain ⟨g, s₁, hg, h⟩ := h
  rw [get_apply] at hg
  simp only [Option.some.injEq, Prod.mk.injEq] at hg
  obtain ⟨rfl, rfl⟩ := hg
  cases hc : s.argsCache.get? (x, y) with
  | some rs₀ =>
    rw [hc] at h
    simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hI, sub_refl _, fun L hL hG => (hI L hL hG).2 x y _ hc⟩
  | none =>
  rw [hc] at h
  dsimp only at h
  cases hp : findPath C.ee x y with
  | none => rw [hp] at h; exact absurd h (by simp [fail_apply])
  | some path =>
  rw [hp] at h
  dsimp only at h
  by_cases hch : (!chainOk x path.toList y) = true
  · rw [ite_t hch] at h; exact absurd h bind_failure
  rw [ite_f hch] at h
  rw [bind_eq_some'] at h
  obtain ⟨steps, s₂, h₂, h⟩ := h
  cases hl : steps.getLast? with
  | none => rw [hl] at h; exact absurd h (by simp [fail_apply])
  | some first =>
  rw [hl] at h
  dsimp only at h
  cases hfold : steps.dropLast.foldr (fun st acc => acc.bind fun a => composeAll a st) (some first) with
  | none => rw [hfold] at h; exact absurd h (by simp [fail_apply])
  | some rs₁ =>
  rw [hfold] at h
  dsimp only at h
  rw [bind_eq_some'] at h
  obtain ⟨_, s₃, h₃, h⟩ := h
  rw [modify_apply] at h₃
  simp only [Option.some.injEq, Prod.mk.injEq] at h₃
  obtain ⟨-, rfl⟩ := h₃
  simp only [pure_apply, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hI₂, hS₂, hC₂⟩ := stepsArgs_sound hF hA _ _ _ _ h₂ hI
  have hclaim : ∀ L, Ext s₂ L → Good C L → RelsOk L rs₁ := fun L hL hG =>
    foldr_compose_sound steps.dropLast first rs₁ hfold
      (hC₂ L hL hG first (List.mem_of_getLast? hl))
      (fun st hst => hC₂ L hL hG st (List.dropLast_subset _ hst))
  refine ⟨?_, hS₂, hclaim⟩
  intro L hL hG
  obtain ⟨hf, ha⟩ := hI₂ L hL hG
  refine ⟨hf, fun a b rs' hab => ?_⟩
  rw [Std.HashMap.get?_insert] at hab
  split at hab
  · rename_i hk
    have : (x, y) = (a, b) := by simpa using hk
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj this
    simp only [Option.some.injEq] at hab; subst hab
    exact hclaim L hL hG
  · exact ha a b rs' hab

/-- **The queries are sound**, at every fuel. -/
theorem queries_sound (C : ExCtx) : ∀ n, QF C n ∧ QA C n
  | 0 => ⟨fun _ _ _ _ h => by rw [qFull] at h; exact absurd h (by simp [fail_apply]),
          fun _ _ _ _ _ h => by rw [qArgs] at h; exact absurd h (by simp [fail_apply])⟩
  | n + 1 =>
    let ⟨hF, hA⟩ := queries_sound C n
    ⟨qFull_succ hF hA, qArgs_succ hF hA⟩

/-! ## Literals -/

omit [LogosFacts] in
/-- Removing duplicates keeps every element. -/
theorem mem_dedup {arr : Array Node} {l : Node} (h : l ∈ arr.toList) :
    l ∈ (arr.foldl (fun acc a => if acc.contains a then acc else acc.push a) #[]).toList := by
  rw [← Array.foldl_toList]
  suffices ∀ (xs : List Node) (acc : Array Node), (l ∈ xs ∨ l ∈ acc.toList) →
      l ∈ (xs.foldl (fun acc a => if acc.contains a then acc else acc.push a) acc).toList from
    this _ _ (.inl h)
  intro xs
  induction xs with
  | nil => intro acc h; simpa using h
  | cons x xs ih =>
    intro acc h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · rcases List.mem_cons.1 h with rfl | h
      · right
        split
        · rename_i hc; exact Array.mem_toList_iff.2 (Array.mem_of_contains_eq_true hc)
        · simp
      · exact .inl h
    · right
      split
      · exact h
      · simp [h]

/-- **A query from the empty state is sound**: its reasons make the terms equal. -/
theorem runFull_sound {C : ExCtx} {x y : Nat} {exp : Array Node} (h : runFull C x y = some exp)
    (hG : Good C exp) : FullOk C exp x y := by
  unfold runFull at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨⟨_, st⟩, hq, rfl⟩ := h
  have hI : Inv C ExState.empty := fun _ _ _ =>
    ⟨fun _ _ h => by simp [ExState.empty] at h, fun _ _ _ h => by simp [ExState.empty] at h⟩
  obtain ⟨-, -, hC⟩ := (queries_sound C C.fuel).1 _ _ _ _ hq hI
  exact hC _ (fun l hl => mem_dedup hl) hG

omit [LogosFacts] in
theorem trueIn_not {M : SmtModel} {a : Node} {b : Node} (hb : b = Node.app (.kind .NOT) #[a])
    (h : __smtx_model_eval M a.toSmt = SmtValue.Boolean false) : TrueIn M b.toEo := by
  subst hb
  unfold TrueIn
  show __smtx_model_eval M (Node.app (.kind .NOT) #[a]).toSmt = _
  rw [toSmt_not (cs := #[a]) rfl, eval_not']
  simp only [Array.getElem_singleton]
  rw [h]; simp [__smtx_model_eval_not, native_not]

/-- A literal related to a Boolean constant has its value. -/
theorem eval_of_condEquiv_bool {L : Array Node} {t : Node} {b : Bool}
    (h : CondEquiv (Holds L) t.toEo (Node.mkBool b).toEo) (M : SmtModel) (hM : model_wf M)
    (hH : Holds L M) : __smtx_model_eval M t.toSmt = SmtValue.Boolean b := by
  have hb' : (Node.mkBool b).toEo = Term.Boolean b := by
    cases b <;> simp [Node.mkBool, Node.toEo, Const.toEo]
  have hT : HasBoolType t.toEo := by
    have := h.type_eq
    unfold HasBoolType
    rw [this, hb']
    exact Solver.typeof_bool b
  obtain ⟨c, hc⟩ := LogosFacts.eval_bool M _ hM hT
  have hr := (trueIn_mkEq_iff M _ _).1 (h.2 M hM hH)
  rw [hb', Solver.eval_bool_const] at hr
  have hc' : __smtx_model_eval M (__eo_to_smt t.toEo) = SmtValue.Boolean c := hc
  rw [hc'] at hr
  have := valueRel_bool hr
  show __smtx_model_eval M (__eo_to_smt t.toEo) = _
  rw [hc', this]

/-- **A verified explanation is sound**: in every well-formed model of its
reasons, the literal is true. -/
theorem explainLitV_sound {C : ExCtx} {lit : Node} {exp : Array Node}
    (h : explainLitV C lit = some exp) (hG : Good C exp) (M : SmtModel) (hM : model_wf M)
    (hH : Holds exp M) : TrueIn M lit.toEo := by
  -- the predicate case, for an atom `atom` of polarity `pol` of `lit`
  have pred : ∀ atom pol, explainPredV C atom pol = some exp →
      (pol = true → lit = atom) → (pol = false → lit = Node.app (.kind .NOT) #[atom]) →
      TrueIn M lit.toEo := by
    intro atom pol hp hpos hneg
    unfold explainPredV at hp
    split at hp
    · rename_i i _
      dsimp only at hp
      generalize hbdef : (if pol = true then C.ee.trueId else C.ee.falseId) = b at hp
      split at hp
      · rename_i hg
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hg
        obtain ⟨⟨hb, hia⟩, hib⟩ := hg
        rcases runFull_sound hp hG with he | hc
        · exact absurd he hib
        · rw [hia, hb] at hc
          have hv := eval_of_condEquiv_bool hc M hM hH
          cases pol
          · exact trueIn_not (hneg rfl) hv
          · rw [hpos rfl]; exact hv
      · simp at hp
    · simp at hp
  unfold explainLitV at h
  -- the atom and polarity
  have hlit : ∀ atom pol, litAtom lit = (atom, pol) →
      (pol = true → lit = atom) ∧ (pol = false → lit = Node.app (.kind .NOT) #[atom]) := by
    intro atom pol hl
    unfold litAtom at hl
    split at hl
    · rename_i cs
      split at hl
      · rename_i h1
        simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
        refine ⟨fun h => by simp at h, fun _ => ?_⟩
        congr 1
        exact Array.ext (by simp [h1]) (fun i hi _ => by
          have : i = 0 := by omega
          subst this; simp)
      · simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
        exact ⟨fun _ => rfl, fun h => by simp at h⟩
    · simp only [Prod.mk.injEq] at hl; obtain ⟨rfl, rfl⟩ := hl
      exact ⟨fun _ => rfl, fun h => by simp at h⟩
  generalize hl : litAtom lit = ap at h
  obtain ⟨atom, pol⟩ := ap
  obtain ⟨hpos, hneg⟩ := hlit atom pol hl
  dsimp only at h
  split at h
  · rename_i cs
    split at h
    · rename_i h2
      -- the equality `(= cs[0] cs[1])`
      have hatom : ∀ N : SmtModel, __smtx_model_eval N (Node.app (.kind .EQUAL) cs).toSmt =
          __smtx_model_eval_eq (__smtx_model_eval N cs[0].toSmt) (__smtx_model_eval N cs[1].toSmt) := by
        intro N; rw [toSmt_eq h2, model_eval_eq_eq]
      cases pol
      · -- a disequality
        simp only [Bool.false_eq_true, ite_false] at h
        unfold explainDiseqV at h
        split at h
        · rename_i i j _ _
          split at h
          · rename_i lo hi _
            split at h
            · rename_i x y _
              split at h
              · rename_i hg
                simp only [Bool.and_eq_true, beq_iff_eq] at hg
                obtain ⟨⟨-, hx⟩, hy⟩ := hg
                rcases runFull_sound h hG with he | hc
                · subst he; rw [hx] at hy; simp [Node.eqNode, Node.mkNode, Node.mkFalse] at hy
                · rw [hx, hy] at hc
                  have hv := eval_of_condEquiv_bool (b := false) hc M hM hH
                  refine trueIn_not (hneg rfl) ?_
                  rw [hatom]
                  have : (Node.eqNode cs[0] cs[1]).toSmt = SmtTerm.eq cs[0].toSmt cs[1].toSmt :=
                    toSmt_eq (cs := #[cs[0], cs[1]]) rfl
                  rw [this, model_eval_eq_eq] at hv
                  exact hv
              · simp at h
            · simp at h
          · simp at h
        · simp at h
      · -- an equality
        simp only [ite_true] at h
        unfold explainEqV at h
        split at h
        · rename_i i j _ _
          split at h
          · rename_i hg
            simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hg
            obtain ⟨⟨hi, hj⟩, hne⟩ := hg
            rcases runFull_sound h hG with he | hc
            · subst he; exact absurd (hi.symm.trans hj) hne
            · rw [hi, hj] at hc
              have := hc.2 M hM hH
              rw [hpos rfl]
              unfold TrueIn at this ⊢
              show __smtx_model_eval M (Node.app (.kind .EQUAL) cs).toSmt = _
              rw [hatom]
              exact this
          · simp at h
        · simp at h
    · exact pred _ _ h hpos hneg
  · exact pred _ _ h hpos hneg

end Telos.Solver.EE
