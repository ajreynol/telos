import TelosProofs.Solver.Model
import TelosProofs.Solver.LinCert
import Telos.Solver.SatProof

/-!
# Certificates of refutations are sound

`Telos/Solver/SatProof.lean`: a certificate that checks (`Cert.check`) refutes
its inputs. In a well-formed model that makes every input true:
- each clause with a justification is true: the clauses of an input formula
  (`input_sat`), the definitions of connectives (`defClauses_sat`), and the
  negations of theory conflicts (`theory_sat`, from the certificates'
  soundness, `checkConflict_sound`), and the clauses of theory lemmas, valid
  by their certificates from no assumptions (`lemma_true`, from `check_sound`);
  and the clauses of linear arithmetic, whose certificates refute the negations
  of some of their literals (`arith_sat`, from `linCert_sound`);
- a clause that follows from true clauses by unit propagation is true
  (`rup_sound`), so each learned clause is, and so is the empty clause, which
  is impossible (`Cert.check_sound`).

The semantics of the connectives is Logos's, through the evaluation of
connectives on Boolean values (`combine_sound_in`).
-/

open Eo Smtm SmtEval

namespace Telos.Solver

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable [LogosFacts]

namespace SatProof

/-! ## Literals -/

/-- A clause is true in a model: one of its literals is. -/
def SatIn (N : SmtModel) (c : Clause) : Prop := ∃ l ∈ c.toList, TrueIn N l.toEo

/-- A node evaluates to a Boolean. -/
def BoolVal (N : SmtModel) (l : Node) : Prop := ∃ b, __smtx_model_eval N l.toSmt = SmtValue.Boolean b

omit [LogosFacts] in
theorem trueIn_iff (N : SmtModel) (l : Node) :
    TrueIn N l.toEo ↔ __smtx_model_eval N l.toSmt = SmtValue.Boolean true := Iff.rfl

theorem boolVal_of_isBool {N : SmtModel} (hN : model_wf N) {l : Node} (h : isBool l = true) : BoolVal N l := by
  unfold isBool at h
  rw [Node.smtTypeF_eq] at h
  exact LogosFacts.eval_bool N _ hN (by simpa [Node.smtType] using h)

omit [LogosFacts] in
theorem eval_notNode (N : SmtModel) (x : Node) :
    __smtx_model_eval N (Node.notNode x).toSmt = __smtx_model_eval_not (__smtx_model_eval N x.toSmt) := by
  have : (Node.notNode x).toSmt = SmtTerm.not x.toSmt := toSmt_not (cs := #[x]) rfl
  rw [this, eval_not']

omit [LogosFacts] in
theorem notNode_sem {N : SmtModel} {x : Node} (hx : BoolVal N x) :
    BoolVal N (Node.notNode x) ∧ (TrueIn N (Node.notNode x).toEo ↔ ¬ TrueIn N x.toEo) := by
  obtain ⟨b, hb⟩ := hx
  rw [trueIn_iff, trueIn_iff, eval_notNode, hb]
  refine ⟨⟨!b, by rw [eval_notNode, hb]; rfl⟩, ?_⟩
  cases b <;> simp [__smtx_model_eval_not, native_not]

omit [LogosFacts] in
/-- The negation of a Boolean literal is true iff the literal is not. -/
theorem negate_sem {N : SmtModel} {l : Node} (hl : BoolVal N l) :
    BoolVal N (negate l) ∧ (TrueIn N (negate l).toEo ↔ ¬ TrueIn N l.toEo) := by
  unfold negate
  split
  · rename_i cs
    split
    · rename_i h1
      -- l is (not x): its value is the negation of x's
      obtain ⟨b, hb⟩ := hl
      have e : __smtx_model_eval N (Node.app (.kind .NOT) cs).toSmt =
          __smtx_model_eval_not (__smtx_model_eval N cs[0].toSmt) := by
        rw [toSmt_not h1, eval_not']
      rw [e] at hb
      have hx : __smtx_model_eval N cs[0].toSmt = SmtValue.Boolean (!b) := by
        revert hb
        cases __smtx_model_eval N cs[0].toSmt <;> simp [__smtx_model_eval_not, native_not]
      refine ⟨⟨!b, hx⟩, ?_⟩
      rw [trueIn_iff, trueIn_iff, hx, e, hx]
      cases b <;> simp [__smtx_model_eval_not, native_not]
    · exact notNode_sem hl
  · exact notNode_sem hl

/-- A literal is true or its negation is. -/
theorem lit_or_negate {N : SmtModel} {l : Node} (hl : BoolVal N l) :
    TrueIn N l.toEo ∨ TrueIn N (negate l).toEo := by
  by_cases h : TrueIn N l.toEo
  · exact .inl h
  · exact .inr ((negate_sem hl).2.2 h)

/-! ## Reverse unit propagation -/

/-- The literals of a set are true. -/
def Inv (N : SmtModel) (S : Std.HashSet Key) : Prop := ∀ k : Key, k ∈ S → TrueIn N k.node.toEo

omit [LogosFacts] in
theorem inv_insert {N : SmtModel} {S : Std.HashSet Key} (hS : Inv N S) {l : Node} (hl : TrueIn N l.toEo) :
    Inv N (S.insert ⟨l⟩) := by
  intro k hk
  rcases Std.HashSet.mem_insert.1 hk with e | e
  · have : k = ⟨l⟩ := by simpa using (eq_of_beq e).symm
    subst this; exact hl
  · exact hS k e

omit [LogosFacts] in
theorem not_true_of_negate {N : SmtModel} {S : Std.HashSet Key} (hS : Inv N S) {l : Node}
    (h : S.contains ⟨negate l⟩ = true) : ¬ TrueIn N l.toEo := fun ht =>
  not_both N l ht (hS _ (Std.HashSet.contains_iff_mem.1 h))

/-- A clause whose literals are all false but the open ones has a true open
literal. -/
theorem open_true {N : SmtModel} {S : Std.HashSet Key} (hS : Inv N S) {d : Clause} (hd : SatIn N d) :
    ∃ l ∈ (d.filter fun l => !S.contains ⟨negate l⟩).toList, TrueIn N l.toEo := by
  obtain ⟨l, hl, ht⟩ := hd
  refine ⟨l, ?_, ht⟩
  rw [Array.toList_filter, List.mem_filter]
  refine ⟨hl, ?_⟩
  cases e : S.contains ⟨negate l⟩
  · rfl
  · exact absurd ht (not_true_of_negate hS e)

/-- One pass of propagation over true clauses: no conflict, and the literals
added are true. -/
theorem pass_sound {N : SmtModel} {db : Array Clause} (hdb : ∀ d ∈ db.toList, SatIn N d) :
    ∀ {S : Std.HashSet Key}, Inv N S →
      (propagatePass db S = none → False) ∧ ∀ S', propagatePass db S = some S' → Inv N S' := by
  intro S hS
  unfold propagatePass
  rw [← Array.foldlM_toList]
  generalize db.toList = L at hdb
  revert hdb
  induction L generalizing S with
  | nil =>
    intro _
    refine ⟨fun h => by simp at h, fun S' h => ?_⟩
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; exact hS
  | cons d L ih =>
    intro hdb
    simp only [List.foldlM_cons]
    have hd := hdb d (List.mem_cons_self ..)
    have hrest : ∀ d ∈ L, SatIn N d := fun d h => hdb d (List.mem_cons_of_mem _ h)
    obtain ⟨l, hl, ht⟩ := open_true hS hd
    split
    · rename_i hemp
      exact absurd (Array.isEmpty_iff.1 hemp ▸ (Array.mem_toList_iff.1 hl)) (by simp)
    · split
      · rename_i hemp h1
        -- the open literal is the only one: it is the true one
        have hS' : Inv N (S.insert ⟨(d.filter fun l => !S.contains ⟨negate l⟩)[0]⟩) := by
          have hl' := Array.mem_toList_iff.1 hl
          obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 hl'
          have : i = 0 := by omega
          subst this
          exact inv_insert hS (e ▸ ht)
        simpa using ih hS' hrest
      · simpa using ih hS hrest

theorem propagates_sound {N : SmtModel} {db : Array Clause} (hdb : ∀ d ∈ db.toList, SatIn N d) :
    ∀ (fuel : Nat) {S : Std.HashSet Key}, Inv N S → propagates db fuel S = true → False
  | 0, _, _, h => by simp [propagates] at h
  | f + 1, S, hS, h => by
    unfold propagates at h
    have hp := pass_sound hdb hS
    split at h
    · exact hp.1 ‹_›
    · rename_i S' hS'
      split at h
      · cases h
      · exact propagates_sound hdb f (hp.2 S' hS') h

/-- **Reverse unit propagation is sound**: a clause whose literals are
Boolean, and whose negation propagates to a conflict over true clauses, is
true. -/
theorem rup_sound {N : SmtModel} (hN : model_wf N) {db : Array Clause} (hdb : ∀ d ∈ db.toList, SatIn N d)
    {c : Clause} (hc : c.all isBool = true) (h : rup db c = true) : SatIn N c := by
  by_contra hne
  have hall : ∀ l ∈ c.toList, TrueIn N (negate l).toEo := by
    intro l hl
    have hb := boolVal_of_isBool hN ((Array.all_eq_true_iff_forall_mem.1 hc) l (Array.mem_toList_iff.1 hl))
    exact (negate_sem hb).2.2 fun ht => hne ⟨l, hl, ht⟩
  unfold rup at h
  refine propagates_sound hdb _ ?_ h
  rw [← Array.foldl_toList]
  generalize c.toList = L at hall
  suffices ∀ (S : Std.HashSet Key), Inv N S → Inv N (L.foldl (fun S l => S.insert ⟨negate l⟩) S) from
    this {} (fun k hk => by simp at hk)
  induction L with
  | nil => exact fun S hS => hS
  | cons l L ih =>
    intro S hS
    exact ih (fun l' h => hall l' (List.mem_cons_of_mem _ h)) _
      (inv_insert hS (hall l (List.mem_cons_self ..)))

/-! ## Connectives -/

open Classical in
/-- The truth value of a node. -/
noncomputable def bval (N : SmtModel) (c : Node) : Bool := decide (TrueIn N c.toEo)

omit [LogosFacts] in
theorem eval_bval {N : SmtModel} {c : Node} (h : BoolVal N c) :
    __smtx_model_eval N c.toSmt = SmtValue.Boolean (bval N c) := by
  obtain ⟨b, hb⟩ := h
  rw [hb]; cases b <;> simp [bval, trueIn_iff, hb]

omit [LogosFacts] in
theorem vals_bval {N : SmtModel} : ∀ {l : List Node}, (∀ c ∈ l, BoolVal N c) →
    ValsIn N l (l.map fun c => MVal.bool (bval N c))
  | [], _ => .nil
  | c :: l, h => .cons (by rw [eval_bval (h c (List.mem_cons_self ..))]; rfl)
      (vals_bval fun c hc => h c (List.mem_cons_of_mem _ hc))

omit [LogosFacts] in
theorem bools_map (l : List Bool) : Model.bools (l.map MVal.bool) = some l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [Model.bools, ih]

/-- A connective of Boolean children has the value its kind gives them. -/
theorem conn_sem {N : SmtModel} {k : Kind} {cs : Array Node} (hc : ∀ c ∈ cs.toList, BoolVal N c) {r : Bool}
    (h : Model.combine k cs (cs.toList.map fun c => MVal.bool (bval N c)) = some (.bool r)) :
    BoolVal N (.app (.kind k) cs) ∧ (TrueIn N (Node.app (.kind k) cs).toEo ↔ r = true) := by
  have e := combine_sound_in N (vals_bval hc) h
  refine ⟨⟨r, e⟩, ?_⟩
  rw [trueIn_iff, e]; simp [toVal]

/-- The children of a connective whose tree is Boolean. -/
theorem boolTree_app {k : Kind} {cs : Array Node} (h : boolTree (.app (.kind k) cs) = true)
    (hc : isConnOrNot (.app (.kind k) cs) = true) :
    isBool (.app (.kind k) cs) = true ∧ arityOk (.app (.kind k) cs) = true ∧ ∀ c ∈ cs.toList, boolTree c = true := by
  unfold boolTree at h
  simp only [Bool.and_eq_true, hc, Bool.not_true, Bool.false_or, Array.all_eq_true_iff_forall_mem] at h
  refine ⟨h.1, h.2.1, fun c hm => ?_⟩
  have := h.2.2 ⟨c, Array.mem_toList_iff.1 hm⟩ (by simp)
  simpa using this

theorem isBool_of_boolTree {n : Node} (h : boolTree n = true) : isBool n = true := by
  unfold boolTree at h; simp only [Bool.and_eq_true] at h; exact h.1

omit [LogosFacts] in
/-- The literal of a Boolean formula `c` itself, negated or not. -/
theorem neg_sem {N : SmtModel} {c : Node} (hb : BoolVal N c) (neg : Bool) :
    BoolVal N (if neg then Node.notNode c else c) ∧
      (TrueIn N (if neg then Node.notNode c else c).toEo ↔ (TrueIn N c.toEo ↔ neg = false)) := by
  cases neg
  · simp only [Bool.false_eq_true, ↓reduceIte]; exact ⟨hb, by simp⟩
  · simp only [↓reduceIte]
    exact ⟨(notNode_sem hb).1, by rw [(notNode_sem hb).2]; simp⟩

/-- The literal of a formula: negated or not, as asked. -/
theorem litOf_sem {N : SmtModel} (hN : model_wf N) (c : Node) (neg : Bool) (h : boolTree c = true) :
    BoolVal N (litOf c neg) ∧ (TrueIn N (litOf c neg).toEo ↔ (TrueIn N c.toEo ↔ neg = false)) := by
  unfold litOf
  split
  · rename_i cs
    split
    · rename_i h1
      obtain ⟨-, -, hd⟩ := boolTree_app h (by simp [isConnOrNot])
      have hd : boolTree cs[0] = true := hd cs[0] (by simp)
      obtain ⟨hb, hiff⟩ := litOf_sem hN cs[0] (!neg) hd
      have hnd := (notNode_sem (boolVal_of_isBool hN (isBool_of_boolTree hd)))
      refine ⟨hb, ?_⟩
      rw [hiff]
      have : (Node.app (.kind .NOT) cs) = Node.notNode cs[0] := by
        rcases cs with ⟨l⟩; match l, h1 with | [_], _ => rfl
      rw [this, hnd.2]
      cases neg <;> simp
    · exact neg_sem (boolVal_of_isBool hN (isBool_of_boolTree h)) neg
  · exact neg_sem (boolVal_of_isBool hN (isBool_of_boolTree h)) neg
termination_by sizeOf c
decreasing_by
  all_goals
    subst_vars
    have := Array.sizeOf_getElem ‹Array Node› 0 (by omega)
    simp only [Node.app.sizeOf_spec]
    omega

/-- A clause of literals with one true. -/
theorem sat_of_subsumes {N : SmtModel} {d : List Node} {c : Clause} (hd : ∃ l ∈ d, TrueIn N l.toEo)
    (h : subsumes d c = true) : SatIn N c := by
  obtain ⟨l, hl, ht⟩ := hd
  unfold subsumes at h
  have := (List.all_eq_true.1 h) l hl
  exact ⟨l, Array.mem_toList_iff.2 (Array.contains_iff_mem.1 this), ht⟩

omit [LogosFacts] in
theorem combine_two {N : SmtModel} {cs : Array Node} (h2 : cs.size = 2) :
    (cs.toList.map fun c => MVal.bool (bval N c)) = [.bool (bval N cs[0]), .bool (bval N cs[1])] := by
  rw [toList_two h2]; rfl

omit [LogosFacts] in
theorem tv {N : SmtModel} {c : Node} : bval N c = true ↔ TrueIn N c.toEo := by simp [bval]

omit [LogosFacts] in
theorem tvf {N : SmtModel} {c : Node} : bval N c = false ↔ ¬ TrueIn N c.toEo := by simp [bval]

theorem and_sem {N : SmtModel} {cs : Array Node} (hc : ∀ c ∈ cs.toList, BoolVal N c) (h2 : 2 ≤ cs.size) :
    BoolVal N (.app (.kind .AND) cs) ∧ (TrueIn N (Node.app (.kind .AND) cs).toEo ↔ ∀ c ∈ cs.toList, TrueIn N c.toEo) := by
  have hm : (cs.toList.map fun c => MVal.bool (bval N c)) = (cs.toList.map (bval N)).map MVal.bool := by simp
  have e : Model.combine .AND cs (cs.toList.map fun c => MVal.bool (bval N c)) =
      some (.bool ((cs.toList.map (bval N)).all id)) := by
    rw [hm]; simp only [Model.combine, List.length_map, Array.length_toList, h2, ↓reduceIte, bools_map, Option.map_some]
  obtain ⟨hb, hiff⟩ := conn_sem hc e
  refine ⟨hb, hiff.trans ?_⟩
  rw [List.all_eq_true]
  constructor
  · intro h c hc; exact tv.1 (h _ (List.mem_map_of_mem hc))
  · intro h x hx; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx; exact tv.2 (h c hc)

theorem or_sem {N : SmtModel} {cs : Array Node} (hc : ∀ c ∈ cs.toList, BoolVal N c) (h2 : 2 ≤ cs.size) :
    BoolVal N (.app (.kind .OR) cs) ∧ (TrueIn N (Node.app (.kind .OR) cs).toEo ↔ ∃ c ∈ cs.toList, TrueIn N c.toEo) := by
  have hm : (cs.toList.map fun c => MVal.bool (bval N c)) = (cs.toList.map (bval N)).map MVal.bool := by simp
  have e : Model.combine .OR cs (cs.toList.map fun c => MVal.bool (bval N c)) =
      some (.bool ((cs.toList.map (bval N)).any id)) := by
    rw [hm]; simp only [Model.combine, List.length_map, Array.length_toList, h2, ↓reduceIte, bools_map, Option.map_some]
  obtain ⟨hb, hiff⟩ := conn_sem hc e
  refine ⟨hb, hiff.trans ?_⟩
  rw [List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxt⟩; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx; exact ⟨c, hc, tv.1 hxt⟩
  · rintro ⟨c, hc, ht⟩; exact ⟨_, List.mem_map_of_mem hc, tv.2 ht⟩

theorem bin_sem {N : SmtModel} {k : Kind} {cs : Array Node} (hc : ∀ c ∈ cs.toList, BoolVal N c) (h2 : cs.size = 2)
    {f : Bool → Bool → Bool}
    (hf : ∀ a b, Model.combine k cs [.bool a, .bool b] = some (.bool (f a b))) :
    BoolVal N (.app (.kind k) cs) ∧
      (TrueIn N (Node.app (.kind k) cs).toEo ↔ f (bval N cs[0]) (bval N cs[1]) = true) := by
  have e := hf (bval N cs[0]) (bval N cs[1])
  rw [← combine_two h2] at e
  exact conn_sem hc e

open Classical in
theorem ite_sem {N : SmtModel} {cs : Array Node} (hc : ∀ c ∈ cs.toList, BoolVal N c) (h3 : cs.size = 3) :
    BoolVal N (.app (.kind .ITE) cs) ∧ (TrueIn N (Node.app (.kind .ITE) cs).toEo ↔
      (if TrueIn N cs[0].toEo then TrueIn N cs[1].toEo else TrueIn N cs[2].toEo)) := by
  have hm : (cs.toList.map fun c => MVal.bool (bval N c)) =
      [.bool (bval N cs[0]), .bool (bval N cs[1]), .bool (bval N cs[2])] := by rw [toList_three h3]; rfl
  have e : Model.combine .ITE cs (cs.toList.map fun c => MVal.bool (bval N c)) =
      some (.bool (if bval N cs[0] then bval N cs[1] else bval N cs[2])) := by
    rw [hm]; simp only [Model.combine]; split <;> rfl
  obtain ⟨hb, hiff⟩ := conn_sem hc e
  refine ⟨hb, hiff.trans ?_⟩
  by_cases h0 : TrueIn N cs[0].toEo
  · have : bval N cs[0] = true := tv.2 h0
    simp only [this, ↓reduceIte, h0, tv]
  · have : bval N cs[0] = false := by
      cases e : bval N cs[0]
      · rfl
      · exact absurd (tv.1 e) h0
    simp only [this, Bool.false_eq_true, ↓reduceIte, h0, tv]

/-! ## The justifications -/

/-- The literal facts of a Boolean child: its literal, and the literal's
negation. -/
theorem child_lits {N : SmtModel} (hN : model_wf N) {c : Node} (h : boolTree c = true) :
    BoolVal N c ∧ (TrueIn N (litOf c false).toEo ↔ TrueIn N c.toEo) ∧
      (TrueIn N (negate (litOf c false)).toEo ↔ ¬ TrueIn N c.toEo) ∧
      (TrueIn N (litOf c true).toEo ↔ ¬ TrueIn N c.toEo) := by
  obtain ⟨hb, hi⟩ := litOf_sem hN c false h
  obtain ⟨-, hi'⟩ := litOf_sem hN c true h
  refine ⟨boolVal_of_isBool hN (isBool_of_boolTree h), by rw [hi]; simp, ?_, by rw [hi']; simp⟩
  rw [(negate_sem hb).2, hi]; simp

omit [LogosFacts] in
theorem sat_list {N : SmtModel} {l : List Node} (h : l.any (bval N) = true) : ∃ x ∈ l, TrueIn N x.toEo := by
  obtain ⟨x, hx, hb⟩ := List.any_eq_true.1 h; exact ⟨x, hx, tv.1 hb⟩

omit [LogosFacts] in
theorem bval_of_iff {N : SmtModel} {x y : Node} (h : TrueIn N x.toEo ↔ TrueIn N y.toEo) : bval N x = bval N y := by
  simp [bval, h]

omit [LogosFacts] in
theorem bval_of_iff_not {N : SmtModel} {x y : Node} (h : TrueIn N x.toEo ↔ ¬ TrueIn N y.toEo) :
    bval N x = !bval N y := by
  unfold bval
  by_cases hy : TrueIn N y.toEo
  · simp [hy, h]
  · simp [hy, h.2 hy]

omit [LogosFacts] in
theorem bval_of_iff_eq {N : SmtModel} {x : Node} {b : Bool} (h : TrueIn N x.toEo ↔ b = true) : bval N x = b := by
  cases b <;> simp_all [bval]

open Classical in
/-- **The definitions of connectives are true.** -/
theorem defClauses_sat {N : SmtModel} (hN : model_wf N) {n : Node} (hconn : isConn n = true)
    (ht : boolTree n = true) : ∀ d ∈ defClauses n, ∃ l ∈ d, TrueIn N l.toEo := by
  intro d hd
  match n, hconn, ht with
  | .app (.kind k) cs, hconn, ht =>
  obtain ⟨hbn, har, hch⟩ := boolTree_app ht (by simp [isConnOrNot, hconn])
  have hbv : ∀ c ∈ cs.toList, BoolVal N c := fun c hc => (child_lits hN (hch c hc)).1
  have hn := notNode_sem (boolVal_of_isBool hN hbn)
  unfold defClauses at hd
  simp only at hd
  split at hd
  · rename_i hk
    have hk : k = .AND := by simpa using hk
    subst hk
    have h2 : 2 ≤ cs.size := by simpa [arityOk] using har
    have hs := (and_sem hbv h2).2
    rcases List.mem_append.1 hd with hd | hd
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
      have := child_lits hN (hch c hc)
      by_cases h : TrueIn N (Node.app (.kind .AND) cs).toEo
      · exact ⟨_, by simp, this.2.1.2 (hs.1 h c hc)⟩
      · exact ⟨_, by simp, hn.2.2 h⟩
    · simp only [List.mem_singleton] at hd; subst hd
      by_cases h : TrueIn N (Node.app (.kind .AND) cs).toEo
      · exact ⟨_, by simp, h⟩
      · obtain ⟨c, hc, hf⟩ : ∃ c ∈ cs.toList, ¬ TrueIn N c.toEo := by
          by_contra hne
          exact h (hs.2 fun c hc => by_contra fun hf => hne ⟨c, hc, hf⟩)
        exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hc), (child_lits hN (hch c hc)).2.2.1.2 hf⟩
  · split at hd
    · rename_i hk' hk
      have hk : k = .OR := by simpa using hk
      subst hk
      have h2 : 2 ≤ cs.size := by simpa [arityOk] using har
      have hs := (or_sem hbv h2).2
      rcases List.mem_append.1 hd with hd | hd
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hd
        have := child_lits hN (hch c hc)
        by_cases h : TrueIn N (Node.app (.kind .OR) cs).toEo
        · exact ⟨_, by simp, h⟩
        · exact ⟨_, by simp, this.2.2.1.2 fun hc' => h (hs.2 ⟨c, hc, hc'⟩)⟩
      · simp only [List.mem_singleton] at hd; subst hd
        by_cases h : TrueIn N (Node.app (.kind .OR) cs).toEo
        · obtain ⟨c, hc, ht⟩ := hs.1 h
          exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem hc), (child_lits hN (hch c hc)).2.1.2 ht⟩
        · exact ⟨_, by simp, hn.2.2 h⟩
    · -- the binary connectives and ite: truth tables
      have L := fun (c : Node) (hc : c ∈ cs.toList) => child_lits hN (hch c hc)
      split at hd
      · rename_i _ _ hk
        obtain ⟨rfl, h2⟩ := hk
        have hs := (bin_sem (k := .XOR) hbv h2 (f := fun a b => a != b) (fun a b => rfl)).2
        have l0 := L cs[0] (by simp); have l1 := L cs[1] (by simp)
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
        have e0 := bval_of_iff l0.2.1; have e0' := bval_of_iff_not l0.2.2.1
        have e1 := bval_of_iff l1.2.1; have e1' := bval_of_iff_not l1.2.2.1
        have en := bval_of_iff_not hn.2; have es := bval_of_iff_eq hs
        rcases hd with rfl | rfl | rfl | rfl <;> apply sat_list <;>
          simp only [List.any_cons, List.any_nil, Bool.or_false, e0, e0', e1, e1', en, es] <;>
          cases bval N cs[0] <;> cases bval N cs[1] <;> rfl
      · split at hd
        · rename_i _ _ _ hk
          obtain ⟨rfl, h2⟩ := hk
          have hs := (bin_sem (k := .EQUAL) hbv h2 (f := fun a b => a == b)
            (fun a b => by cases a <;> cases b <;> simp [Model.combine])).2
          have l0 := L cs[0] (by simp); have l1 := L cs[1] (by simp)
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
          have e0 := bval_of_iff l0.2.1; have e0' := bval_of_iff_not l0.2.2.1
          have e1 := bval_of_iff l1.2.1; have e1' := bval_of_iff_not l1.2.2.1
          have en := bval_of_iff_not hn.2; have es := bval_of_iff_eq hs
          rcases hd with rfl | rfl | rfl | rfl <;> apply sat_list <;>
            simp only [List.any_cons, List.any_nil, Bool.or_false, e0, e0', e1, e1', en, es] <;>
            cases bval N cs[0] <;> cases bval N cs[1] <;> rfl
        · split at hd
          · rename_i _ _ _ _ hk
            obtain ⟨rfl, h2⟩ := hk
            have hs := (bin_sem (k := .IMPLIES) hbv h2 (f := fun a b => !a || b) (fun a b => rfl)).2
            have l0 := L cs[0] (by simp); have l1 := L cs[1] (by simp)
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
            have e0 := bval_of_iff l0.2.1; have e0' := bval_of_iff_not l0.2.2.1
            have e1 := bval_of_iff l1.2.1; have e1' := bval_of_iff_not l1.2.2.1
            have en := bval_of_iff_not hn.2; have es := bval_of_iff_eq hs
            rcases hd with rfl | rfl | rfl <;> apply sat_list <;>
              simp only [List.any_cons, List.any_nil, Bool.or_false, e0, e0', e1, e1', en, es] <;>
              cases bval N cs[0] <;> cases bval N cs[1] <;> rfl
          · split at hd
            · rename_i _ _ _ _ _ hk
              obtain ⟨rfl, h3⟩ := hk
              have hs := (ite_sem hbv h3).2
              have l0 := L cs[0] (by simp); have l1 := L cs[1] (by simp); have l2 := L cs[2] (by simp)
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
              have e0 := bval_of_iff l0.2.1; have e0' := bval_of_iff_not l0.2.2.1
              have e1 := bval_of_iff l1.2.1; have e1' := bval_of_iff_not l1.2.2.1
              have e2 := bval_of_iff l2.2.1; have e2' := bval_of_iff_not l2.2.2.1
              have en := bval_of_iff_not hn.2
              have es : bval N (Node.app (.kind .ITE) cs) =
                  (if bval N cs[0] then bval N cs[1] else bval N cs[2]) := by
                apply bval_of_iff_eq; rw [hs]
                cases h0 : bval N cs[0]
                · have : ¬ TrueIn N cs[0].toEo := fun h => by simp [tv.2 h] at h0
                  simp [this, tv]
                · simp [tv.1 h0, tv]
              rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> apply sat_list <;>
                simp only [List.any_cons, List.any_nil, Bool.or_false, e0, e0', e1, e1', e2, e2', en, es] <;>
                cases bval N cs[0] <;> cases bval N cs[1] <;> cases bval N cs[2] <;> rfl
            · simp at hd

/-- **The negation of a theory conflict is true.** -/
theorem theory_sat {N : SmtModel} (hN : model_wf N) {A : Array Node} {p : EqProof} {c : Clause}
    (hc : EqProof.checkConflict A p = true) (hb : A.all isBool = true)
    (hneg : (A.all fun a => c.contains (negate a)) = true) : SatIn N c := by
  by_contra hne
  have hbA : ∀ a ∈ A.toList, isBool a = true := fun a ha =>
    (Array.all_eq_true_iff_forall_mem.1 hb) a (Array.mem_toList_iff.1 ha)
  refine checkConflict_sound A p hc (fun l hl => by
    have := hbA l hl; unfold isBool at this; rw [Node.smtTypeF_eq] at this
    exact by simpa [HasBoolType, Node.toSmt, Node.smtType] using this) N hN ?_
  intro a ha
  rcases lit_or_negate (boolVal_of_isBool hN (hbA a ha)) with h | h
  · exact h
  · have hm := (Array.all_eq_true_iff_forall_mem.1 hneg) a (Array.mem_toList_iff.1 ha)
    exact absurd ⟨_, Array.mem_toList_iff.2 (Array.contains_iff_mem.1 hm), h⟩ hne

omit [LogosFacts] in
theorem push_true {N : SmtModel} {A : Array Node} (hA : ∀ a ∈ A.toList, TrueIn N a.toEo) {l : Node}
    (hl : TrueIn N l.toEo) : ∀ a ∈ (A.push l).toList, TrueIn N a.toEo := by
  intro a ha
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at ha
  rcases ha with ha | rfl
  · exact hA a ha
  · exact hl

omit [LogosFacts] in
/-- The parts of a negated conjunction. -/
theorem notAndParts_spec {l : Node} {cs : Array Node} (h : notAndParts l = some cs) :
    ∃ cs0 : Array Node, ∃ h1 : cs0.size = 1, l = .app (.kind .NOT) cs0 ∧
      cs0[0] = .app (.kind .AND) cs ∧ 2 ≤ cs.size := by
  unfold notAndParts at h
  split at h
  · rename_i k cs0
    split at h
    · rename_i hk
      have hk : k = .NOT := by simpa using hk
      subst hk
      split at h
      · rename_i h1
        split at h
        · rename_i k' ds he
          split at h
          · rename_i hk'
            simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hk'
            obtain ⟨rfl, h2⟩ := hk'
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨cs0, h1, rfl, he, h2⟩
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

/-- **A certificate of linear arithmetic refutes its literals**: Farkas
combinations (`checkFarkas_sound`), splits of disequalities (`split_sem`),
cuts, and cases on a negated conjunction. -/
theorem linCert_sound {N : SmtModel} (hN : model_wf N) : ∀ (p : LinCert) (A : Array Node),
    p.check A = true → (∀ a ∈ A.toList, TrueIn N a.toEo) → False
  | .farkas cs, A, h, hA => LinCertProof.checkFarkas_sound (by simpa [LinCert.check] using h) N hN hA
  | .split l lt gt, A, h, hA => by
    simp only [LinCert.check] at h
    split at h
    · rename_i a b hd
      simp only [Bool.and_eq_true, Bool.or_eq_true] at h
      obtain ⟨⟨⟨hm, hty⟩, hlt⟩, hgt⟩ := h
      have hl := hA l (Array.mem_toList_iff.2 (Array.contains_iff_mem.1 hm))
      have hor : TrueIn N (Node.mkNode .LT #[a, b]).toEo ∨ TrueIn N (Node.mkNode .GT #[a, b]).toEo := by
        rcases hty with ⟨hra, hrb⟩ | ⟨hia, hib⟩
        · obtain ⟨ra, ha⟩ := LinCertProof.real_of_isRealTerm hN hra
          obtain ⟨rb, hb⟩ := LinCertProof.real_of_isRealTerm hN hrb
          exact LinCertProof.split_sem hd hl ha hb
        · obtain ⟨ia, ha⟩ := LinCertProof.int_of_isIntTerm hN hia
          obtain ⟨ib, hb⟩ := LinCertProof.int_of_isIntTerm hN hib
          exact LinCertProof.split_isem hd hl ha hb
      rcases hor with h1 | h1
      · exact linCert_sound hN lt _ hlt (push_true hA h1)
      · exact linCert_sound hN gt _ hgt (push_true hA h1)
    · cases h
  | .cut l pos neg, A, h, hA => by
    simp only [LinCert.check, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hb, hpos⟩, hneg⟩ := h
    have hbv : BoolVal N l := boolVal_of_isBool hN (by unfold isBool; simpa using hb)
    rcases lit_or_negate hbv with h1 | h1
    · exact linCert_sound hN pos _ hpos (push_true hA h1)
    · exact linCert_sound hN neg _ hneg (push_true hA h1)
  | .cases l subs, A, h, hA => by
    simp only [LinCert.check] at h
    split at h
    · rename_i cs hcs
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hm, hall⟩, hsub⟩ := h
      have hl := hA l (Array.mem_toList_iff.2 (Array.contains_iff_mem.1 hm))
      obtain ⟨cs0, h1, rfl, he, h2⟩ := notAndParts_spec hcs
      -- each conjunct has an entry
      have hentry : ∀ c ∈ cs.toList, ∃ e ∈ subs.toList, e.1 = c := by
        intro c hc
        have := (Array.all_eq_true_iff_forall_mem.1 hall) c (Array.mem_toList_iff.1 hc)
        obtain ⟨e, he, hec⟩ := Array.any_eq_true'.1 this
        exact ⟨e, Array.mem_toList_iff.2 he, by simpa using hec⟩
      have hsub' : ∀ e ∈ subs.toList, e.1.smtTypeF = SmtType.Bool ∧ e.2.check (A.push (negate e.1)) = true := by
        intro e he
        have := (Array.all_eq_true_iff_forall_mem.1 hsub) ⟨e, Array.mem_toList_iff.1 he⟩ (by simp)
        simpa using this
      have hbool : ∀ c ∈ cs.toList, BoolVal N c := by
        intro c hc
        obtain ⟨e, he, rfl⟩ := hentry c hc
        exact boolVal_of_isBool hN (by unfold isBool; simpa using (hsub' e he).1)
      obtain ⟨hband, hiff⟩ := and_sem hbool h2
      -- the conjunction is false
      have hfalse : ¬ TrueIn N (Node.app (.kind .AND) cs).toEo := by
        intro ht
        have := (LinCertProof.not_true_iff h1).1 hl
        rw [he] at this
        unfold TrueIn at ht
        rw [show __eo_to_smt (Node.app (.kind .AND) cs).toEo = (Node.app (.kind .AND) cs).toSmt from rfl, this] at ht
        simp at ht
      have : ∃ c ∈ cs.toList, ¬ TrueIn N c.toEo := by
        by_contra hc
        push Not at hc
        exact hfalse (hiff.2 hc)
      obtain ⟨c, hc, hcf⟩ := this
      obtain ⟨e, hem, rfl⟩ := hentry c hc
      have hneg := (negate_sem (hbool e.1 hc)).2.2 hcf
      have := Array.sizeOf_lt_of_mem (Array.mem_toList_iff.1 hem)
      exact linCert_sound hN e.2 _ (hsub' e hem).2 (push_true hA hneg)
    · cases h
termination_by p => sizeOf p
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (rcases e with ⟨c', p'⟩; simp at this ⊢; omega)

/-- **A clause of linear arithmetic is true**: it has the negations of literals
that its certificate refutes. -/
theorem arith_sat {N : SmtModel} (hN : model_wf N) {A : Array Node} {p : LinCert} {c : Clause}
    (hc : p.check A = true) (hb : A.all isBool = true)
    (hneg : (A.all fun a => c.contains (negate a)) = true) : SatIn N c := by
  by_contra hne
  have hbA : ∀ a ∈ A.toList, isBool a = true := fun a ha =>
    (Array.all_eq_true_iff_forall_mem.1 hb) a (Array.mem_toList_iff.1 ha)
  refine linCert_sound hN p A hc fun a ha => ?_
  rcases lit_or_negate (boolVal_of_isBool hN (hbA a ha)) with h | h
  · exact h
  · have hm := (Array.all_eq_true_iff_forall_mem.1 hneg) a (Array.mem_toList_iff.1 ha)
    exact absurd ⟨_, Array.mem_toList_iff.2 (Array.contains_iff_mem.1 hm), h⟩ hne

omit [LogosFacts] in
theorem bval_not_of {N : SmtModel} {x : Node} {b : Bool} (h : TrueIn N x.toEo ↔ b = false) : bval N x = !b := by
  cases b <;> simp_all [bval]

theorem bin_children {k : Kind} {cs : Array Node} {N : SmtModel} (hN : model_wf N)
    (ht : boolTree (.app (.kind k) cs) = true) (hc : isConnOrNot (.app (.kind k) cs) = true) :
    (∀ c ∈ cs.toList, BoolVal N c) ∧ ∀ c ∈ cs.toList, boolTree c = true := by
  obtain ⟨-, -, hch⟩ := boolTree_app ht hc
  exact ⟨fun c h => boolVal_of_isBool hN (isBool_of_boolTree (hch c h)), hch⟩

/-- **The clauses of a true input formula are true** (of a false one, with
`neg`). -/
theorem input_sat {N : SmtModel} (hN : model_wf N) (f : Node) (neg : Bool) (ht : boolTree f = true)
    (hf : TrueIn N f.toEo ↔ neg = false) : ∀ d ∈ inputClauses f neg, ∃ l ∈ d, TrueIn N l.toEo := by
  intro d hd
  -- the default: the formula's literal
  have dflt : d ∈ [[litOf f neg]] → ∃ l ∈ d, TrueIn N l.toEo := by
    intro hm
    simp only [List.mem_singleton] at hm; subst hm
    exact ⟨_, by simp, (litOf_sem hN f neg ht).2.2 hf⟩
  unfold inputClauses at hd
  split at hd
  · rename_i k cs
    have hcon : ∀ c ∈ cs, boolTree c = true → (∀ neg', (TrueIn N c.toEo ↔ neg' = false) →
        ∀ d ∈ inputClauses c neg', ∃ l ∈ d, TrueIn N l.toEo) := fun c _ hc neg' h =>
      input_sat hN c neg' hc h
    split at hd
    · rename_i hk
      have hk : k = .AND := by simpa using hk
      subst hk
      obtain ⟨-, har, hch⟩ := boolTree_app ht (by simp [isConnOrNot, isConn])
      have hbv : ∀ c ∈ cs.toList, BoolVal N c := fun c h => boolVal_of_isBool hN (isBool_of_boolTree (hch c h))
      have hs := (and_sem hbv (by simpa [arityOk] using har)).2
      split at hd
      · rename_i hn
        have hn : neg = false := by simpa using hn
        subst hn
        obtain ⟨_, hm, hd⟩ := List.mem_flatten.1 hd
        obtain ⟨⟨c, hc⟩, -, rfl⟩ := List.mem_map.1 hm
        have hc' : c ∈ cs.toList := Array.mem_toList_iff.2 hc
        exact hcon c hc (hch c hc') false (by simpa using hs.1 (hf.2 rfl) c hc') d hd
      · rename_i hn
        have hn : neg = true := by simpa using hn
        subst hn
        simp only [List.mem_singleton] at hd; subst hd
        have hnf : ¬ TrueIn N (Node.app (.kind .AND) cs).toEo := fun h => by simpa using hf.1 h
        obtain ⟨c, hc, hfc⟩ : ∃ c ∈ cs.toList, ¬ TrueIn N c.toEo := by
          by_contra hne; exact hnf (hs.2 fun c hc => by_contra fun h => hne ⟨c, hc, h⟩)
        exact ⟨_, List.mem_map_of_mem hc, (child_lits hN (hch c hc)).2.2.2.2 hfc⟩
    · split at hd
      · rename_i _ hk
        have hk : k = .OR := by simpa using hk
        subst hk
        obtain ⟨-, har, hch⟩ := boolTree_app ht (by simp [isConnOrNot, isConn])
        have hbv : ∀ c ∈ cs.toList, BoolVal N c := fun c h => boolVal_of_isBool hN (isBool_of_boolTree (hch c h))
        have hs := (or_sem hbv (by simpa [arityOk] using har)).2
        split at hd
        · rename_i hn
          have hn : neg = false := by simpa using hn
          subst hn
          simp only [List.mem_singleton] at hd; subst hd
          obtain ⟨c, hc, htc⟩ := hs.1 (hf.2 rfl)
          exact ⟨_, List.mem_map_of_mem hc, (child_lits hN (hch c hc)).2.1.2 htc⟩
        · rename_i hn
          have hn : neg = true := by simpa using hn
          subst hn
          have hnf : ¬ TrueIn N (Node.app (.kind .OR) cs).toEo := fun h => by simpa using hf.1 h
          obtain ⟨_, hm, hd⟩ := List.mem_flatten.1 hd
          obtain ⟨⟨c, hc⟩, -, rfl⟩ := List.mem_map.1 hm
          have hc' : c ∈ cs.toList := Array.mem_toList_iff.2 hc
          exact hcon c hc (hch c hc') true (by simp; exact fun h => hnf (hs.2 ⟨c, hc', h⟩)) d hd
      · split at hd
        · -- xor
          rename_i _ _ hk
          obtain ⟨rfl, h2⟩ := hk
          obtain ⟨hbv, hch⟩ := bin_children hN ht (by simp [isConnOrNot, isConn])
          have hs := bval_of_iff_eq (bin_sem (k := .XOR) hbv h2 (f := fun a b => a != b) (fun a b => rfl)).2
          have hfb := bval_not_of hf
          have l0 := child_lits hN (hch cs[0] (by simp)); have l1 := child_lits hN (hch cs[1] (by simp))
          have e0 := bval_of_iff l0.2.1; have e0' := bval_of_iff_not l0.2.2.2
          have e1 := bval_of_iff l1.2.1; have e1' := bval_of_iff_not l1.2.2.2
          rw [hs] at hfb
          split at hd <;>
            (rename_i hn
             cases neg <;> simp at hn
             all_goals
               simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
               rcases hd with rfl | rfl <;> apply sat_list <;>
                 simp only [List.any_cons, List.any_nil, Bool.or_false, e0, e0', e1, e1'] <;>
                 revert hfb <;> cases bval N cs[0] <;> cases bval N cs[1] <;> simp)
        · split at hd
          · -- implies
            rename_i _ _ _ hk
            obtain ⟨rfl, h2⟩ := hk
            obtain ⟨hbv, hch⟩ := bin_children hN ht (by simp [isConnOrNot, isConn])
            have hs := (bin_sem (k := .IMPLIES) hbv h2 (f := fun a b => !a || b) (fun a b => rfl)).2
            have l0 := child_lits hN (hch cs[0] (by simp)); have l1 := child_lits hN (hch cs[1] (by simp))
            split at hd
            · rename_i hn
              have hn : neg = false := by simpa using hn
              subst hn
              have hfb : (!bval N cs[0] || bval N cs[1]) = true := hs.1 (hf.2 rfl)
              have e0' := bval_of_iff_not l0.2.2.2; have e1 := bval_of_iff l1.2.1
              simp only [List.mem_singleton] at hd; subst hd
              apply sat_list
              simp only [List.any_cons, List.any_nil, Bool.or_false, e0', e1]
              revert hfb; cases bval N cs[0] <;> cases bval N cs[1] <;> simp
            · rename_i hn
              have hn : neg = true := by simpa using hn
              subst hn
              have hnf : ¬ TrueIn N (Node.app (.kind .IMPLIES) cs).toEo := fun h => by simpa using hf.1 h
              have h0 : TrueIn N cs[0].toEo := by
                by_contra h; exact hnf (hs.2 (by simp [show bval N cs[0] = false by simpa [bval] using h]))
              have h1 : ¬ TrueIn N cs[1].toEo := fun h =>
                hnf (hs.2 (by simp [show bval N cs[1] = true from tv.2 h]))
              rcases List.mem_append.1 hd with hd | hd
              · exact input_sat hN cs[0] false (hch cs[0] (by simp)) (by simpa using h0) d hd
              · exact input_sat hN cs[1] true (hch cs[1] (by simp)) (by simpa using h1) d hd
          · split at hd
            · -- ite
              rename_i _ _ _ _ hk
              obtain ⟨rfl, h3⟩ := hk
              obtain ⟨hbv, hch⟩ := bin_children hN ht (by simp [isConnOrNot, isConn])
              have hs := (ite_sem hbv h3).2
              have l0 := child_lits hN (hch cs[0] (by simp)); have l1 := child_lits hN (hch cs[1] (by simp))
              have l2 := child_lits hN (hch cs[2] (by simp))
              have e0 := bval_of_iff l0.2.1; have e0' := bval_of_iff_not l0.2.2.2
              have es : bval N (Node.app (.kind .ITE) cs) =
                  (if bval N cs[0] then bval N cs[1] else bval N cs[2]) := by
                apply bval_of_iff_eq; rw [hs]
                cases h0 : bval N cs[0]
                · have : ¬ TrueIn N cs[0].toEo := fun h => by simp [tv.2 h] at h0
                  simp [this, tv]
                · simp [tv.1 h0, tv]
              have hfb := bval_not_of hf
              rw [es] at hfb
              have et := (litOf_sem hN cs[1] neg (hch cs[1] (by simp))).2
              have ee := (litOf_sem hN cs[2] neg (hch cs[2] (by simp))).2
              have et' : bval N (litOf cs[1] neg) = (bval N cs[1] == !neg) := by
                apply bval_of_iff_eq; rw [et]; cases neg <;> simp [tv, tvf]
              have ee' : bval N (litOf cs[2] neg) = (bval N cs[2] == !neg) := by
                apply bval_of_iff_eq; rw [ee]; cases neg <;> simp [tv, tvf]
              simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
              rcases hd with rfl | rfl <;> apply sat_list <;>
                simp only [List.any_cons, List.any_nil, Bool.or_false, e0, e0', et', ee'] <;>
                revert hfb <;> cases bval N cs[0] <;> cases bval N cs[1] <;> cases bval N cs[2] <;>
                cases neg <;> simp
            · split at hd
              · -- not
                rename_i _ _ _ _ _ hk
                obtain ⟨rfl, h1⟩ := hk
                obtain ⟨-, hch⟩ := bin_children (N := N) hN ht (by simp [isConnOrNot])
                have hn := notNode_sem (boolVal_of_isBool hN (isBool_of_boolTree (hch cs[0] (by simp))))
                have e : (Node.app (.kind .NOT) cs) = Node.notNode cs[0] := by
                  rcases cs with ⟨l⟩; match l, h1 with | [_], _ => rfl
                rw [e] at hf
                refine input_sat hN cs[0] (!neg) (hch cs[0] (by simp)) ?_ d hd
                rw [hn.2] at hf
                cases neg <;> simp_all
              · split at hd
                · -- a Boolean equality
                  rename_i _ _ _ _ _ _ hk
                  obtain ⟨rfl, h2, hty⟩ := hk
                  have hconn : isConn (.app (.kind .EQUAL) cs) = true := by
                    have : cs[0]? = some cs[0] := by simp [h2]
                    have e : cs[0]! = cs[0] := by simp [getElem!_pos, h2]
                    simp [isConn, this, ← e, hty]
                  obtain ⟨hbv, hch⟩ := bin_children hN ht (by simp [isConnOrNot, hconn])
                  have hs := bval_of_iff_eq (bin_sem (k := .EQUAL) hbv h2 (f := fun a b => a == b)
                    (fun a b => by cases a <;> cases b <;> simp [Model.combine])).2
                  have hfb := bval_not_of hf
                  have l0 := child_lits hN (hch cs[0] (by simp)); have l1 := child_lits hN (hch cs[1] (by simp))
                  have e0 := bval_of_iff l0.2.1; have e0' := bval_of_iff_not l0.2.2.2
                  have e1 := bval_of_iff l1.2.1; have e1' := bval_of_iff_not l1.2.2.2
                  rw [hs] at hfb
                  split at hd <;>
                    (rename_i hn
                     cases neg <;> simp at hn
                     all_goals
                       simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd
                       rcases hd with rfl | rfl <;> apply sat_list <;>
                         simp only [List.any_cons, List.any_nil, Bool.or_false, e0, e0', e1, e1'] <;>
                         revert hfb <;> cases bval N cs[0] <;> cases bval N cs[1] <;> simp)
                · exact dflt hd
  · exact dflt hd
termination_by sizeOf f
decreasing_by
  all_goals
    subst_vars
    first
    | (have := Array.sizeOf_lt_of_mem ‹_›; simp only [Node.app.sizeOf_spec]; omega)
    | (have := Array.sizeOf_getElem ‹Array Node› 0 (by simp_all); simp only [Node.app.sizeOf_spec]; omega)
    | (have := Array.sizeOf_getElem ‹Array Node› 1 (by simp_all); simp only [Node.app.sizeOf_spec]; omega)

/-- **A lemma proven from no assumptions is true.** -/
theorem lemma_true {N : SmtModel} (hN : model_wf N) {F : Node} {p : EqProof}
    (h : EqProof.check #[] p = some (F, Node.mkTrue)) : TrueIn N F.toEo := by
  have hc := check_sound #[] (by simp) (stable_of_closed (by simp [EqProof.closedAssumptions])) p _ _ h
  rw [toEo_true] at hc
  exact (bool_of_condEquiv hc).2 N hN (by simp [Holds])

/-- A clause with a justification that checks is true. -/
theorem just_sat {N : SmtModel} (hN : model_wf N) {inputs : Array Node}
    (hin : ∀ f ∈ inputs.toList, TrueIn N f.toEo) {c : Clause} {j : Just} (h : j.check inputs c = true) :
    SatIn N c := by
  cases j with
  | input i =>
    simp only [Just.check] at h
    split at h
    · rename_i f hf
      simp only [Bool.and_eq_true, List.any_eq_true] at h
      obtain ⟨ht, d, hd, hs⟩ := h
      have hft : TrueIn N f.toEo := hin f (Array.mem_toList_iff.2 (Array.mem_of_getElem? hf))
      exact sat_of_subsumes (input_sat hN f false ht (by simpa using hft) d hd) hs
    · cases h
  | defn n =>
    simp only [Just.check, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨hc, ht⟩, d, hd, hs⟩ := h
    exact sat_of_subsumes (defClauses_sat hN hc ht d hd) hs
  | theory A p =>
    simp only [Just.check, Bool.and_eq_true] at h
    exact theory_sat hN h.1.1 h.1.2 h.2
  | «lemma» F p =>
    simp only [Just.check, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at h
    obtain ⟨⟨hp, ht⟩, d, hd, hs⟩ := h
    exact sat_of_subsumes (input_sat hN F false ht (by simpa using lemma_true hN hp) d hd) hs
  | arith A p =>
    simp only [Just.check, Bool.and_eq_true] at h
    exact arith_sat hN h.1.1 h.1.2 h.2

/-- The learned clauses follow, and then the empty clause: impossible if the
clauses are true. -/
theorem checkLearned_sound {N : SmtModel} (hN : model_wf N) :
    ∀ (L : List Clause) (db : Array Clause), (∀ d ∈ db.toList, SatIn N d) → checkLearned db L = true → False
  | [], db, hdb, h => by
    simp only [checkLearned] at h
    obtain ⟨l, hl, -⟩ := rup_sound hN hdb (by simp) h
    simp at hl
  | c :: L, db, hdb, h => by
    simp only [checkLearned, Bool.and_eq_true] at h
    have hc := rup_sound hN hdb h.1.1 h.1.2
    refine checkLearned_sound hN L (db.push c) ?_ h.2
    intro d hd
    rcases (by simpa using hd : d ∈ db ∨ d = c) with hd | hd
    · exact hdb d (Array.mem_toList_iff.2 hd)
    · subst hd; exact hc

/-- **A certificate that checks refutes its inputs**: no well-formed model
makes them all true. -/
theorem Cert.check_sound {inputs : Array Node} {cert : Cert} (h : cert.check inputs = true) :
    ∀ N, model_wf N → (∀ f ∈ inputs.toList, TrueIn N f.toEo) → False := by
  intro N hN hin
  unfold Cert.check at h
  simp only [Bool.and_eq_true] at h
  refine checkLearned_sound hN _ _ ?_ h.2
  intro d hd
  rw [Array.toList_map] at hd
  obtain ⟨⟨c, j⟩, hm, rfl⟩ := List.mem_map.1 hd
  have := (Array.all_eq_true_iff_forall_mem.1 h.1) (c, j) (Array.mem_toList_iff.1 hm)
  simp only [Bool.and_eq_true] at this
  exact just_sat hN hin this.2

end SatProof

end Telos.Solver
