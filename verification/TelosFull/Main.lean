import TelosProofs.Solver.Frontend
import TelosProofs.Solver.Correct
import TelosProofs.Axioms
import TelosFull.ChildArgs
import Cpc.Proofs.ProvenFromEmpty
import Cpc.Proofs.RuleSupport.Cong.Spine
import Cpc.Proofs.RuleSupport.SpineArgsSupport
import Cpc.Proofs.RuleSupport.SubstituteTypeSupport
import Cpc.Proofs.TypePreservation.Full
import Cpc.Proofs.RuleSupport.Cong.TrueSpine
import Cpc.Proofs.RuleSupport.Cong.TypeSpine
import Cpc.Proofs.Closed.Support
import Cpc.Proofs.RuleSupport.SetsEvalOpSupport
import Cpc.Proofs.Canonical.Ops
import Cpc.Proofs.Canonical.Eval
import Cpc.Proofs.Canonical.Maps

/-!
# The unconditional theorem

The default build (`TelosProofs`) proves `Telos.rewrite_correct_of_logos`, which
takes the Logos theorems it uses as the class `LogosFacts`
(`TelosProofs/Core/LogosFacts.lean`), so that it does not need Logos's proofs. This
library, built with `lake build TelosFull`, imports them and proves the instance,
each field from the Logos theorem it restates. So the restatements stay in sync
with the pinned Logos. Then it derives the unconditional `Telos.rewrite_correct`
and audits its axioms.
-/

open Eo
open Smtm
open SmtEval

namespace Telos

/-- Logos's `eo_interprets M t true`, unfolded. -/
theorem eo_interprets_true_iff (M : SmtModel) (t : Term) :
    eo_interprets M t true ↔ HasBoolType t ∧ TrueIn M t := by
  constructor
  · intro h
    cases h with
    | intro_true hTy hEval => exact ⟨hTy, hEval⟩
  · intro ⟨hTy, hEval⟩
    exact smt_interprets.intro_true M _ hTy hEval

/-- `Valid` is Logos's notion of a valid formula. -/
theorem valid_iff (t : Term) :
    Valid t ↔ RuleProofs.eo_has_bool_type t ∧ ∀ M, model_wf M → eo_interprets M t true := by
  constructor
  · intro ⟨hTy, hTrue⟩
    exact ⟨hTy, fun M hM => (eo_interprets_true_iff M t).2 ⟨hTy, hTrue M hM⟩⟩
  · intro ⟨hTy, hInt⟩
    exact ⟨hTy, fun M hM => ((eo_interprets_true_iff M t).1 (hInt M hM)).2⟩

theorem agrees_of {M N : SmtModel} (h : AgreesOnGlobals M N) : model_agrees_on_globals M N :=
  ⟨h.consts, h.funs, h.usortDom⟩

theorem agrees_to {M N : SmtModel} (h : model_agrees_on_globals M N) : AgreesOnGlobals M N :=
  ⟨h.consts, h.funs, h.usortDom⟩

/-- A true spine over `xs` and `ys`, extending one between the heads. -/
theorem congTrueSpine_foldl (M : SmtModel) (hM : model_wf M) :
    ∀ {h₁ h₂ : Term} {xs ys : List Term},
      CongSupport.CongTrueSpine M h₁ h₂ →
      List.Forall₂ (fun x y => HasBoolType (mkEq x y) ∧
        ∀ N, model_wf N → AgreesOnGlobals M N → TrueIn N (mkEq x y)) xs ys →
      CongSupport.CongTrueSpine M (xs.foldl Term.Apply h₁) (ys.foldl Term.Apply h₂) := by
  intro h₁ h₂ xs ys hh h
  induction h generalizing h₁ h₂ with
  | nil => exact hh
  | cons hxy _ ih =>
    refine ih (CongSupport.CongTrueSpine.app hh ?_ ?_)
    · exact (eo_interprets_true_iff M _).2 ⟨hxy.1, hxy.2 M hM (agrees_to (model_agrees_on_globals_refl M))⟩
    · intro N hN hAgree
      exact (eo_interprets_true_iff N _).2 ⟨hxy.1, hxy.2 N hN (agrees_to hAgree)⟩

/-- telos's default leaf of a map is Logos's. -/
theorem mapLeaf_eq : ∀ m : SmtMap, mapLeaf m = Smtm.smt_map_default_leaf m
  | SmtMap.cons _ _ m => by simp only [mapLeaf, Smtm.smt_map_default_leaf, mapLeaf_eq m]
  | SmtMap.default _ _ => rfl

instance logosFacts : LogosFacts where
  checker_sound cs P hT hC hP := (valid_iff P).2 (proven_from_empty_valid cs P hT hC hP)
  cong_spine head xs ys ht h :=
    (valid_iff _).2 (CongSupport.cong_spine_valid head xs ys ht (h.imp fun _ _ h => (valid_iff _).1 h))
  eq_valid_iff a b := (valid_iff _).trans (RuleProofs.eq_valid_iff a b)
  value_rel_refl := RuleProofs.smt_value_rel_refl
  value_rel_symm := RuleProofs.smt_value_rel_symm
  value_rel_trans := RuleProofs.smt_value_rel_trans
  and_or_rest op x r hop h := by
    have hHead : SpineArgsSupport.SpineArgsHead (Term.UOp op) [x, r].length := by
      rcases hop with rfl | rfl
      exacts [.and, .or]
    exact SpineArgsSupport.spine_args_have_smt_translation _ [x, r] hHead h r (by simp)
  seq_type_wf x _ hNN hTy := smt_term_seq_type_wf_of_non_none x hNN hTy
  eo_typeof_bool t h := by
    apply SubstituteSupport.eo_typeof_eq_of_smt_type_eq _ _
    · show __smtx_typeof (__eo_to_smt t) ≠ SmtType.None
      rw [h]; simp
    · simp [__eo_to_smt_type, __smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
        SmtEval.native_and]
    · rw [h]; rfl
  eval_typed M t hM h := type_preservation M hM t h
  eval_canonical M t hM h := model_eval_canonical M hM t h
  eval_bool M t hM h := by
    have hP := type_preservation M hM t (by unfold term_has_non_none_type; rw [h]; simp)
    rw [h] at hP
    exact bool_value_canonical hP
  eval_real M t hM h := by
    have hP := type_preservation M hM t (by unfold term_has_non_none_type; rw [h]; simp)
    rw [h] at hP
    exact real_value_canonical hP
  eval_int M t hM h := by
    have hP := type_preservation M hM t (by unfold term_has_non_none_type; rw [h]; simp)
    rw [h] at hP
    exact int_value_canonical hP
  cong_spine_model M hM head xs ys hq hb h :=
    ((eo_interprets_true_iff M _).1 (CongSupport.congTrueSpine_eq_true M hM _ _ ⟨hq.1, hq.2⟩ hb
      (congTrueSpine_foldl M hM (CongSupport.CongTrueSpine.refl head) h))).2
  cong_type_spine head xs ys ht h :=
    CongSupport.congTypeSpine_eq_has_bool_type _ _ ht
      (CongSupport.congTypeSpine_foldl (fun _ _ hxy => hxy) (CongSupport.CongTypeSpine.refl head) h)
  closed_eval P hc M N h := smt_model_eval_eq_of_eo_closed P hc M N (agrees_of h)
  uf_args i T xs h x hx :=
    SpineArgsSupport.spine_args_have_smt_translation (Term.UConst i T) xs (.uconst i T _) h x hx
  type_no_none := ChildArgs.type_no_none
  tuple_args := ChildArgs.tuple_args
  uop1_arg := ChildArgs.uop1_arg
  update_args op idx x y hop h := by
    rcases hop with rfl | rfl
    exacts [ChildArgs.tuple_update_args idx x y h, ChildArgs.update_args idx x y h]
  dt_sel_arg := ChildArgs.dt_sel_arg
  dt_cons_args := ChildArgs.dt_cons_args
  type_default_ok _ huc T h := type_default_typed_canonical_of_type_wf huc T h
  map_update_canonical uc _ _ _ hm hi he := Smtm.map_update_aux_canonical (uc := uc) hm hi he
  map_lookup_update_same uc _ _ _ hm := Smtm.map_lookup_update_aux_same (uc := uc) hm
  map_lookup_update_other uc _ _ _ _ hm hij := Smtm.map_lookup_update_aux_other (uc := uc) hm hij
  map_ext uc _ _ h1 h2 hl hk :=
    Smtm.map_ext_of_lookup_eq (uc := uc) h1 h2 (by rw [← mapLeaf_eq, ← mapLeaf_eq]; exact hl) hk
  map_update_leaf ed m i e := by rw [mapLeaf_eq, mapLeaf_eq]; exact Smtm.map_update_aux_default_leaf ed m i e
  map_update_default ed m i e := Smtm.map_update_aux_get_default ed m i e
  map_update_typed _ _ _ _ _ hm hi he := Smtm.map_canon_insert_typed hm hi he
  set_union_lookup uc m1 m2 A v h1 h2 h3 h4 h5 :=
    SetsEvalOpSupport.set_union_lookup (uc := uc) m1 m2 A v h1 h2 h3 h4 h5
  set_inter_lookup uc m1 m2 A v h1 h2 h3 h4 := SetsEvalOpSupport.set_inter_lookup (uc := uc) m1 m2 A v h1 h2 h3 h4
  set_minus_lookup uc m1 m2 A v h1 h2 h3 h4 := SetsEvalOpSupport.set_minus_lookup (uc := uc) m1 m2 A v h1 h2 h3 h4
  set_union_canonical uc _ _ h1 h2 := Smtm.model_eval_set_union_canonical (uc := uc) h1 h2
  set_inter_canonical uc _ _ h1 h2 := Smtm.model_eval_set_inter_canonical (uc := uc) h1 h2
  set_minus_canonical uc _ _ h1 h2 := Smtm.model_eval_set_minus_canonical (uc := uc) h1 h2

/-- **Correctness of the rewriter.** Rewriting a well-typed node gives an
equivalent node. -/
theorem rewrite_correct (t : Node) (h : t.WellTyped) : t.Equiv (rewrite t) :=
  rewrite_correct_of_logos t h

/-- **Correctness of the preprocessor.** The conjunction of the preprocessed
assertions is equivalent to that of the input assertions (and `true`). -/
theorem preprocess_correct (as : List Node) (h : (Preprocess.inputNode as).WellTyped)
    (opts : Preprocess.PPOptions := {}) :
    (Preprocess.inputNode as).Equiv (Preprocess.preprocessCert as opts).1 :=
  preprocess_correct_of_logos as h opts

/-- **Correctness of `unsat`** (`telos --solve`): if telos answers `unsat`, the
script's input is unsatisfiable in Logos's semantics. -/
theorem solve_unsat_correct {sc : Frontend.Script} {u : Preprocess.UserOptions} {vs : Bool}
    (h : Frontend.solve sc u vs = .ok .unsat) : sc.satisfiability false :=
  Frontend.solve_unsat h

/-- **Correctness of `sat`** (`telos --solve`): if telos answers `sat`, the
script's input is satisfiable in Logos's semantics. -/
theorem solve_sat_correct {sc : Frontend.Script} {u : Preprocess.UserOptions} {vs : Bool}
    (h : Frontend.solve sc u vs = .ok .sat) : sc.satisfiability true :=
  Frontend.solve_sat h

/-- `solve_unsat_correct` for `solveScript` with any options (also
`telos --theory-events`): if the theory engine answers `unsat` on a script whose
assertions are Boolean, no well-formed model satisfies them. -/
theorem solveScript_unsat_correct (sc : Frontend.Script) (u : Preprocess.UserOptions) (ee pp wp co vs te ev : Bool)
    {out : List Node} {r : Solver.Result} (h : Frontend.solveScript sc u ee pp wp co vs te ev = .ok (out, r))
    (hu : r.answer = .unsat) {opts : Preprocess.PPOptions} {as : List Node}
    (hin : Frontend.ppInput sc u = .ok (opts, as)) (hb : ∀ a ∈ as, HasBoolType a.toEo) :
    ∀ M, model_wf M → ¬ TrueIn M (Preprocess.inputNode as).toEo :=
  Frontend.solveScript_unsat sc u ee pp wp co vs te ev h hu hin hb

/-- `solve_sat_correct` for `solveScript` with any options: if the theory
engine answers `sat`, its model satisfies the assertions: they are true in a
well-formed model. -/
theorem solveScript_sat_correct (sc : Frontend.Script) (u : Preprocess.UserOptions) (ee pp wp co vs te ev : Bool)
    {out : List Node} {r : Solver.Result} (h : Frontend.solveScript sc u ee pp wp co vs te ev = .ok (out, r))
    (hs : r.answer = .sat) {opts : Preprocess.PPOptions} {as : List Node}
    (hin : Frontend.ppInput sc u = .ok (opts, as)) (hb : ∀ a ∈ as, HasBoolType a.toEo) :
    ∃ M, model_wf M ∧ TrueIn M (Preprocess.inputNode as).toEo :=
  Frontend.solveScript_sat sc u ee pp wp co vs te ev h hs hin hb

end Telos

#assert_axioms Telos.rewrite_correct
#assert_axioms Telos.preprocess_correct
#assert_axioms Telos.solve_unsat_correct
#assert_axioms Telos.solve_sat_correct
#assert_axioms Telos.solveScript_unsat_correct
#assert_axioms Telos.solveScript_sat_correct
