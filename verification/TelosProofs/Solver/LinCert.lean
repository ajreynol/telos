import TelosProofs.Solver.Model
import Telos.Solver.LinCert

/-!
# Linear-arithmetic refutations are sound

`Telos/Solver/LinCert.lean`: a Farkas combination that checks
(`checkFarkas`) refutes its literals. In a well-formed model where they are
true, each literal bounds the real difference of its sides (`linParts_sem`),
so each term `q · d` of the sum is `≥ 0`, or `> 0` for a strict bound with a
positive coefficient (`entry_sem`); so the sum is (`plusChain_sem`), and the
comparison of the sum with `0` is true. But the rewriter, which is correct
(`rewrite_correct_of_logos`), rewrites it to `false`.

A disequality `(not (= a b))` of reals that is true makes `(< a b)` or
`(> a b)` true (`split_sem`). The soundness of the whole certificate, with its
cuts, is `LinCert.check_sound` (`TelosProofs/Solver/SatProof.lean`).
-/

open Eo Smtm SmtEval

namespace Telos.Solver

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable [LogosFacts]

namespace LinCertProof

/-- A node has the real value `r` in a model. -/
def RVal (N : SmtModel) (t : Node) (r : ℝ) : Prop := __smtx_model_eval N t.toSmt = SmtValue.Real r

theorem real_of_isRealTerm {N : SmtModel} (hN : model_wf N) {t : Node} (h : isRealTerm t = true) :
    ∃ r, RVal N t r := by
  unfold isRealTerm at h
  exact LogosFacts.eval_real N _ hN (by simpa using h)

omit [LogosFacts] in
theorem toSmt_two {k : Kind} {op : UserOp} (hk : k.eoShape = .spine (Term.UOp op) (.exactly 2)) (a b : Node) :
    (Node.mkNode k #[a, b]).toSmt = __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) a.toEo) b.toEo) := by
  unfold Node.mkNode
  rw [toSmt_bin hk (cs := #[a, b]) rfl]
  rfl

omit [LogosFacts] in
theorem eval_ratNode (N : SmtModel) (q : Rat) : RVal N (ratNode q) (q : ℝ) := by
  simpa [RVal, ratNode, Node.toSmt, Node.toEo, Const.toEo, native_rat_to_real] using eval_rational_term N q

omit [LogosFacts] in
theorem typeof_ratNode (q : Rat) : __smtx_typeof (ratNode q).toSmt = SmtType.Real := by
  simp only [ratNode, Node.toSmt, Node.toEo, Const.toEo]
  rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q from rfl, __smtx_typeof.eq_def]

omit [LogosFacts] in
theorem eval_mult' (N : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval N (SmtTerm.mult x y) = __smtx_model_eval_mult (__smtx_model_eval N x) (__smtx_model_eval N y) := by
  rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
theorem eval_plus' (N : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval N (SmtTerm.plus x y) = __smtx_model_eval_plus (__smtx_model_eval N x) (__smtx_model_eval N y) := by
  rw [__smtx_model_eval.eq_def]

omit [LogosFacts] in
/-- A product of two reals, the first a real constant (which gives the typed nil). -/
theorem eval_mult2 {N : SmtModel} {x y : Node} {rx ry : ℝ} (hx : RVal N x rx) (hy : RVal N y ry)
    (hT : __smtx_typeof x.toSmt = SmtType.Real) :
    RVal N (Node.mkNode .MULT #[x, y]) (rx * ry) := by
  unfold RVal Node.mkNode
  unfold Node.toSmt
  rw [toEo_typedChain (op := UserOp.mult) rfl _ (by simp)]
  have hnil := eval_typedNil N .MULT UserOp.mult x (.rat 1) (.inr ⟨rfl, rfl⟩) (by rw [hT]; rfl)
  have hl : (#[x, y].toList.map Node.toEo) = [x.toEo, y.toEo] := rfl
  have h0 : #[x, y][0] = x := rfl
  rw [hl, h0, eoRightAssocNil, eoRightAssocNil, eoRightAssocNil]
  rw [show ∀ a b, __eo_to_smt (eoApp2 UserOp.mult a b) = SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)
    from fun _ _ => rfl, show ∀ a b, __eo_to_smt (eoApp2 UserOp.mult a b) = SmtTerm.mult (__eo_to_smt a) (__eo_to_smt b)
    from fun _ _ => rfl, eval_mult', eval_mult', hnil]
  rw [show __eo_to_smt x.toEo = x.toSmt from rfl, show __eo_to_smt y.toEo = y.toSmt from rfl, hx, hy]
  simp [toVal, __smtx_model_eval_mult, native_rmult]

omit [LogosFacts] in
theorem eval_sub {N : SmtModel} {a b : Node} {ra rb : ℝ} (ha : RVal N a ra) (hb : RVal N b rb) :
    RVal N (Node.mkNode .SUB #[a, b]) (ra - rb) := by
  unfold RVal at *
  rw [toSmt_two (op := UserOp.neg) rfl, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y)
    = SmtTerm.neg (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt a.toEo = a.toSmt from rfl, show __eo_to_smt b.toEo = b.toSmt from rfl, ha, hb]
  simp [__smtx_model_eval__, native_rplus, native_rneg, sub_eq_add_neg]

omit [LogosFacts] in
theorem eval_linTerm {N : SmtModel} {q : Rat} {a b : Node} {ra rb : ℝ} (ha : RVal N a ra) (hb : RVal N b rb) :
    RVal N (linTerm q a b) ((q : ℝ) * (ra - rb)) :=
  eval_mult2 (eval_ratNode N q) (eval_sub ha hb) (typeof_ratNode q)

omit [LogosFacts] in
/-- A sum of nonnegative reals is nonnegative, and positive if one is. -/
theorem eval_plusChain {N : SmtModel} {nil : Term} (hnil : __smtx_model_eval N (__eo_to_smt nil) = SmtValue.Real 0) :
    ∀ (xs : List Node), (∀ x ∈ xs, ∃ v, RVal N x v ∧ 0 ≤ v) →
    ∃ s, __smtx_model_eval N (__eo_to_smt (eoRightAssocNil UserOp.plus nil (xs.map Node.toEo))) = SmtValue.Real s ∧
      0 ≤ s ∧ ((∃ x ∈ xs, ∃ v, RVal N x v ∧ 0 < v) → 0 < s)
  | [], _ => ⟨0, hnil, le_refl _, fun ⟨_, h, _⟩ => by simp at h⟩
  | x :: xs, h => by
    obtain ⟨v, hv, hv0⟩ := h x (by simp)
    obtain ⟨s, hs, hs0, hpos⟩ := eval_plusChain hnil xs (fun y hy => h y (by simp [hy]))
    refine ⟨v + s, ?_, by linarith, ?_⟩
    · rw [List.map_cons, eoRightAssocNil,
        show ∀ a b, __eo_to_smt (eoApp2 UserOp.plus a b) = SmtTerm.plus (__eo_to_smt a) (__eo_to_smt b)
          from fun _ _ => rfl, eval_plus', hs, show __eo_to_smt x.toEo = x.toSmt from rfl, hv]
      simp [__smtx_model_eval_plus, native_rplus]
    · rintro ⟨y, hy, w, hw, hw0⟩
      rcases List.mem_cons.1 hy with rfl | hy
      · have : w = v := by unfold RVal at hw hv; rw [hw] at hv; exact SmtValue.Real.inj hv
        subst this; linarith
      · linarith [hpos ⟨y, hy, w, hw, hw0⟩]

/-! ## Literals -/

omit [LogosFacts] in
theorem toSmt_cmp {k : Kind} {op : UserOp} (hk : k.eoShape = .spine (Term.UOp op) (.exactly 2))
    {ds : Array Node} (h : ds.size = 2) :
    (Node.app (.kind k) ds).toSmt = __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) ds[0].toEo) ds[1].toEo) :=
  toSmt_bin hk h

omit [LogosFacts] in
theorem eval_geq {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : ℝ} (hx : RVal N ds[0] x) (hy : RVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .GEQ) ds).toSmt = SmtValue.Boolean (decide (y ≤ x)) := by
  rw [toSmt_cmp (op := UserOp.geq) rfl h, show ∀ a b, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b)
    = SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt ds[0].toEo = ds[0].toSmt from rfl, show __eo_to_smt ds[1].toEo = ds[1].toSmt from rfl, hx, hy]
  simp [__smtx_model_eval_geq, __smtx_model_eval_leq, native_rleq]

omit [LogosFacts] in
theorem eval_gt {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : ℝ} (hx : RVal N ds[0] x) (hy : RVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .GT) ds).toSmt = SmtValue.Boolean (decide (y < x)) := by
  rw [toSmt_cmp (op := UserOp.gt) rfl h, show ∀ a b, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b)
    = SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt ds[0].toEo = ds[0].toSmt from rfl, show __eo_to_smt ds[1].toEo = ds[1].toSmt from rfl, hx, hy]
  simp [__smtx_model_eval_gt, __smtx_model_eval_lt, native_rlt]

omit [LogosFacts] in
theorem eval_leq {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : ℝ} (hx : RVal N ds[0] x) (hy : RVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .LEQ) ds).toSmt = SmtValue.Boolean (decide (x ≤ y)) := by
  rw [toSmt_cmp (op := UserOp.leq) rfl h, show ∀ a b, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b)
    = SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt ds[0].toEo = ds[0].toSmt from rfl, show __eo_to_smt ds[1].toEo = ds[1].toSmt from rfl, hx, hy]
  simp [__smtx_model_eval_leq, native_rleq]

omit [LogosFacts] in
theorem eval_lt {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : ℝ} (hx : RVal N ds[0] x) (hy : RVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .LT) ds).toSmt = SmtValue.Boolean (decide (x < y)) := by
  rw [toSmt_cmp (op := UserOp.lt) rfl h, show ∀ a b, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b)
    = SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt ds[0].toEo = ds[0].toSmt from rfl, show __eo_to_smt ds[1].toEo = ds[1].toSmt from rfl, hx, hy]
  simp [__smtx_model_eval_lt, native_rlt]

omit [LogosFacts] in
theorem eval_equal {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : ℝ} (hx : RVal N ds[0] x) (hy : RVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .EQUAL) ds).toSmt = SmtValue.Boolean (decide (x = y)) := by
  rw [toSmt_eq h, eval_eq', hx, hy]
  simp [__smtx_model_eval_eq, native_veq]

omit [LogosFacts] in
theorem not_true_iff {N : SmtModel} {cs : Array Node} (h : cs.size = 1) :
    __smtx_model_eval N (Node.app (.kind .NOT) cs).toSmt = SmtValue.Boolean true ↔
      __smtx_model_eval N cs[0].toSmt = SmtValue.Boolean false := by
  rw [toSmt_not h, eval_not']
  cases __smtx_model_eval N cs[0].toSmt <;> simp [__smtx_model_eval_not, native_not]

/-- The bound `d ⋈ 0` of a relation. -/
def RelHolds : LinRel → ℝ → Prop
  | .ge, d => 0 ≤ d
  | .gt, d => 0 < d
  | .eq, d => d = 0

omit [LogosFacts] in
/-- A true literal bounds the difference of its sides. -/
theorem linParts_sem {N : SmtModel} {l a b : Node} {r : LinRel} (h : linParts l = some (a, b, r))
    (hl : TrueIn N l.toEo) {ra rb : ℝ} (ha : RVal N a ra) (hb : RVal N b rb) : RelHolds r (ra - rb) := by
  unfold TrueIn at hl
  rw [show __eo_to_smt l.toEo = l.toSmt from rfl] at hl
  unfold linParts at h
  split at h
  · rename_i k cs
    split at h
    · rename_i hk
      have hk : k = .NOT := by simpa using hk
      subst hk
      split at h
      · rename_i h1
        rw [not_true_iff h1] at hl
        split at h
        · rename_i k' ds he
          split at h
          · rename_i h2
            rw [he] at hl
            unfold negParts at h
            split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
              obtain ⟨rfl, rfl, rfl⟩ := h
            · rw [eval_geq h2 hb ha] at hl; simp at hl; simp [RelHolds]; linarith
            · rw [eval_gt h2 hb ha] at hl; simp at hl; simp [RelHolds]; linarith
            · rw [eval_leq h2 ha hb] at hl; simp at hl; simp [RelHolds]; linarith
            · rw [eval_lt h2 ha hb] at hl; simp at hl; simp [RelHolds]; linarith
          · simp at h
        · simp at h
      · simp at h
    · split at h
      · rename_i h2
        unfold cmpParts at h
        split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
          obtain ⟨rfl, rfl, rfl⟩ := h
        · rw [eval_geq h2 ha hb] at hl; simp at hl; simp [RelHolds]; linarith
        · rw [eval_gt h2 ha hb] at hl; simp at hl; simp [RelHolds]; linarith
        · rw [eval_leq h2 hb ha] at hl; simp at hl; simp [RelHolds]; linarith
        · rw [eval_lt h2 hb ha] at hl; simp at hl; simp [RelHolds]; linarith
        · rw [eval_equal h2 ha hb] at hl; simp at hl; simp [RelHolds]; linarith
      · simp at h
  · simp at h

/-! ## Integers -/

/-- A node has the integer value `i` in a model. -/
def IVal (N : SmtModel) (t : Node) (i : Int) : Prop := __smtx_model_eval N t.toSmt = SmtValue.Numeral i

theorem int_of_isIntTerm {N : SmtModel} (hN : model_wf N) {t : Node} (h : isIntTerm t = true) :
    ∃ i, IVal N t i := by
  unfold isIntTerm at h
  exact LogosFacts.eval_int N _ hN (by simpa using h)

omit [LogosFacts] in
theorem eval_isub {N : SmtModel} {a b : Node} {ia ib : Int} (ha : IVal N a ia) (hb : IVal N b ib) :
    IVal N (Node.mkNode .SUB #[a, b]) (ia - ib) := by
  unfold IVal at *
  rw [toSmt_two (op := UserOp.neg) rfl, show ∀ x y, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y)
    = SmtTerm.neg (__eo_to_smt x) (__eo_to_smt y) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt a.toEo = a.toSmt from rfl, show __eo_to_smt b.toEo = b.toSmt from rfl, ha, hb]
  simp [__smtx_model_eval__, native_zplus, native_zneg, sub_eq_add_neg]

omit [LogosFacts] in
theorem eval_toReal {N : SmtModel} {t : Node} {i : Int} (h : IVal N t i) :
    RVal N (Node.mkNode .TO_REAL #[t]) (i : ℝ) := by
  unfold RVal IVal at *
  unfold Node.mkNode
  rw [toSmt_un (op := UserOp.to_real) rfl (cs := #[t]) rfl, show ∀ x, __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x)
    = SmtTerm.to_real (__eo_to_smt x) from fun _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt #[t][0].toEo = t.toSmt from rfl, h]
  simp [__smtx_model_eval_to_real, native_int_to_real]

omit [LogosFacts] in
theorem eval_intDiff {N : SmtModel} {a b : Node} {ia ib : Int} (ha : IVal N a ia) (hb : IVal N b ib)
    (strict : Bool) : RVal N (intDiff a b strict) (((ia - ib : Int) : ℝ) - (if strict then 1 else 0)) := by
  have hd := eval_toReal (eval_isub ha hb)
  unfold intDiff
  cases strict
  · simpa using hd
  · have h1 : RVal N (ratNode 1) 1 := by simpa using eval_ratNode N 1
    simpa using eval_sub hd h1

omit [LogosFacts] in
theorem eval_intLinTerm {N : SmtModel} {q : Rat} {a b : Node} {ia ib : Int} (ha : IVal N a ia) (hb : IVal N b ib)
    (strict : Bool) :
    RVal N (intLinTerm q a b strict) ((q : ℝ) * (((ia - ib : Int) : ℝ) - (if strict then 1 else 0))) :=
  eval_mult2 (eval_ratNode N q) (eval_intDiff ha hb strict) (typeof_ratNode q)

omit [LogosFacts] in
theorem eval_igeq {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : Int} (hx : IVal N ds[0] x) (hy : IVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .GEQ) ds).toSmt = SmtValue.Boolean (decide (y ≤ x)) := by
  rw [toSmt_cmp (op := UserOp.geq) rfl h, show ∀ a b, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) a) b)
    = SmtTerm.geq (__eo_to_smt a) (__eo_to_smt b) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt ds[0].toEo = ds[0].toSmt from rfl, show __eo_to_smt ds[1].toEo = ds[1].toSmt from rfl, hx, hy]
  simp [__smtx_model_eval_geq, __smtx_model_eval_leq, native_zleq]

omit [LogosFacts] in
theorem eval_igt {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : Int} (hx : IVal N ds[0] x) (hy : IVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .GT) ds).toSmt = SmtValue.Boolean (decide (y < x)) := by
  rw [toSmt_cmp (op := UserOp.gt) rfl h, show ∀ a b, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) a) b)
    = SmtTerm.gt (__eo_to_smt a) (__eo_to_smt b) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt ds[0].toEo = ds[0].toSmt from rfl, show __eo_to_smt ds[1].toEo = ds[1].toSmt from rfl, hx, hy]
  simp [__smtx_model_eval_gt, __smtx_model_eval_lt, native_zlt]

omit [LogosFacts] in
theorem eval_ileq {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : Int} (hx : IVal N ds[0] x) (hy : IVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .LEQ) ds).toSmt = SmtValue.Boolean (decide (x ≤ y)) := by
  rw [toSmt_cmp (op := UserOp.leq) rfl h, show ∀ a b, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.leq) a) b)
    = SmtTerm.leq (__eo_to_smt a) (__eo_to_smt b) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt ds[0].toEo = ds[0].toSmt from rfl, show __eo_to_smt ds[1].toEo = ds[1].toSmt from rfl, hx, hy]
  simp [__smtx_model_eval_leq, native_zleq]

omit [LogosFacts] in
theorem eval_ilt {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : Int} (hx : IVal N ds[0] x) (hy : IVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .LT) ds).toSmt = SmtValue.Boolean (decide (x < y)) := by
  rw [toSmt_cmp (op := UserOp.lt) rfl h, show ∀ a b, __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) a) b)
    = SmtTerm.lt (__eo_to_smt a) (__eo_to_smt b) from fun _ _ => rfl, __smtx_model_eval.eq_def]
  simp only
  rw [show __eo_to_smt ds[0].toEo = ds[0].toSmt from rfl, show __eo_to_smt ds[1].toEo = ds[1].toSmt from rfl, hx, hy]
  simp [__smtx_model_eval_lt, native_zlt]

omit [LogosFacts] in
theorem eval_iequal {N : SmtModel} {ds : Array Node} (h : ds.size = 2) {x y : Int} (hx : IVal N ds[0] x) (hy : IVal N ds[1] y) :
    __smtx_model_eval N (Node.app (.kind .EQUAL) ds).toSmt = SmtValue.Boolean (decide (x = y)) := by
  rw [toSmt_eq h, eval_eq', hx, hy]
  simp [__smtx_model_eval_eq, native_veq]

/-- The bound `d ⋈ 0` of a relation, over the integers. -/
def RelHoldsI : LinRel → Int → Prop
  | .ge, d => 0 ≤ d
  | .gt, d => 0 < d
  | .eq, d => d = 0

omit [LogosFacts] in
/-- A true literal of integers bounds the difference of its sides. -/
theorem linParts_isem {N : SmtModel} {l a b : Node} {r : LinRel} (h : linParts l = some (a, b, r))
    (hl : TrueIn N l.toEo) {ia ib : Int} (ha : IVal N a ia) (hb : IVal N b ib) : RelHoldsI r (ia - ib) := by
  unfold TrueIn at hl
  rw [show __eo_to_smt l.toEo = l.toSmt from rfl] at hl
  unfold linParts at h
  split at h
  · rename_i k cs
    split at h
    · rename_i hk
      have hk : k = .NOT := by simpa using hk
      subst hk
      split at h
      · rename_i h1
        rw [not_true_iff h1] at hl
        split at h
        · rename_i k' ds he
          split at h
          · rename_i h2
            rw [he] at hl
            unfold negParts at h
            split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
              obtain ⟨rfl, rfl, rfl⟩ := h
            · rw [eval_igeq h2 hb ha] at hl; simp at hl; simp [RelHoldsI]; omega
            · rw [eval_igt h2 hb ha] at hl; simp at hl; simp [RelHoldsI]; omega
            · rw [eval_ileq h2 ha hb] at hl; simp at hl; simp [RelHoldsI]; omega
            · rw [eval_ilt h2 ha hb] at hl; simp at hl; simp [RelHoldsI]; omega
          · simp at h
        · simp at h
      · simp at h
    · split at h
      · rename_i h2
        unfold cmpParts at h
        split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
          obtain ⟨rfl, rfl, rfl⟩ := h
        · rw [eval_igeq h2 ha hb] at hl; simp at hl; simp [RelHoldsI]; omega
        · rw [eval_igt h2 ha hb] at hl; simp at hl; simp [RelHoldsI]; omega
        · rw [eval_ileq h2 hb ha] at hl; simp at hl; simp [RelHoldsI]; omega
        · rw [eval_ilt h2 hb ha] at hl; simp at hl; simp [RelHoldsI]; omega
        · rw [eval_iequal h2 ha hb] at hl; simp at hl; simp [RelHoldsI]; omega
      · simp at h
  · simp at h

/-! ## Farkas combinations -/

omit [LogosFacts] in
theorem mapM_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ x ∈ l, f x = some y
  | [], r, h, y, hy => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h; subst h; simp at hy
  | x :: xs, r, h, y, hy => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, by simp, hb⟩
    · obtain ⟨z, hz, hfz⟩ := mapM_mem hbs y hy
      exact ⟨z, by simp [hz], hfz⟩

/-- An entry's term is `≥ 0`, and `> 0` if it is strict. -/
theorem entry_sem {N : SmtModel} (hN : model_wf N) {A : Array Node} (hA : ∀ a ∈ A.toList, TrueIn N a.toEo)
    {e : Node × Rat} {t : Node} {st : Bool} (h : farkasEntry A e = some (t, st)) :
    ∃ v, RVal N t v ∧ 0 ≤ v ∧ (st = true → 0 < v) := by
  unfold farkasEntry at h
  split at h
  · rename_i a b r hp
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨hm, hq⟩ := hc
      have hl := hA e.1 (Array.mem_toList_iff.2 (Array.contains_iff_mem.1 hm))
      split at h
      · -- reals
        rename_i hreal
        simp only [Bool.and_eq_true] at hreal
        obtain ⟨hra, hrb⟩ := hreal
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ra, ha⟩ := real_of_isRealTerm hN hra
        obtain ⟨rb, hb⟩ := real_of_isRealTerm hN hrb
        have hr := linParts_sem hp hl ha hb
        refine ⟨(e.2 : ℝ) * (ra - rb), eval_linTerm ha hb, ?_, ?_⟩
        · cases r with
          | eq => simp [RelHolds] at hr; simp [hr]
          | ge =>
            have : (0 : ℝ) ≤ e.2 := by exact_mod_cast (hq.resolve_left (by decide))
            exact mul_nonneg this hr
          | gt =>
            have : (0 : ℝ) ≤ e.2 := by exact_mod_cast (hq.resolve_left (by decide))
            exact mul_nonneg this (le_of_lt hr)
        · intro hs
          cases r with
          | gt =>
            have hq0 : 0 < e.2 := by
              simpa only [show (LinRel.gt == LinRel.gt) = true from by decide, Bool.true_and,
                decide_eq_true_eq] using hs
            have : (0 : ℝ) < e.2 := by exact_mod_cast hq0
            exact mul_pos this hr
          | ge => simp [show (LinRel.ge == LinRel.gt) = false from by decide] at hs
          | eq => simp [show (LinRel.eq == LinRel.gt) = false from by decide] at hs
      · split at h
        · -- integers: a strict bound strengthened
          rename_i _ hint
          simp only [Bool.and_eq_true] at hint
          obtain ⟨hia, hib⟩ := hint
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨ia, ha⟩ := int_of_isIntTerm hN hia
          obtain ⟨ib, hb⟩ := int_of_isIntTerm hN hib
          have hr := linParts_isem hp hl ha hb
          refine ⟨_, eval_intLinTerm ha hb (r == .gt), ?_, by simp⟩
          cases r with
          | eq =>
            simp [RelHoldsI] at hr
            simp [show (LinRel.eq == LinRel.gt) = false from by decide, hr]
          | ge =>
            have : (0 : ℝ) ≤ e.2 := by exact_mod_cast (hq.resolve_left (by decide))
            have hd : (0 : ℝ) ≤ ((ia - ib : Int) : ℝ) := by exact_mod_cast hr
            simpa [show (LinRel.ge == LinRel.gt) = false from by decide] using mul_nonneg this hd
          | gt =>
            have : (0 : ℝ) ≤ e.2 := by exact_mod_cast (hq.resolve_left (by decide))
            have hd : (1 : ℝ) ≤ ((ia - ib : Int) : ℝ) := by exact_mod_cast (show (1 : Int) ≤ ia - ib by simp [RelHoldsI] at hr; omega)
            have := mul_nonneg this (sub_nonneg.2 hd)
            simpa [show (LinRel.gt == LinRel.gt) = true from by decide] using this
        · simp at h
    · simp at h
  · simp at h

/-- **A Farkas combination that checks refutes its literals.** -/
theorem checkFarkas_sound {A : Array Node} {cs : Array (Node × Rat)} (h : checkFarkas A cs = true)
    (N : SmtModel) (hN : model_wf N) (hA : ∀ a ∈ A.toList, TrueIn N a.toEo) : False := by
  unfold checkFarkas at h
  split at h
  · rename_i ts hts
    simp only [Bool.and_eq_true, Bool.not_eq_true', Array.isEmpty_iff, beq_iff_eq] at h
    obtain ⟨hne, hwt, hrw⟩ := h
    -- the entries
    rw [Array.mapM_eq_mapM_toList] at hts
    obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 (by simpa using hts)
    have hent : ∀ p ∈ tl, ∃ v, RVal N p.1 v ∧ 0 ≤ v ∧ (p.2 = true → 0 < v) := by
      intro p hp
      obtain ⟨e, -, he⟩ := mapM_mem htl p hp
      exact entry_sem hN hA he
    -- the sum
    let xs : Array Node := #[ratNode 0] ++ tl.toArray.map (·.1)
    have hxs : 2 ≤ xs.size := by
      have : tl ≠ [] := by rintro rfl; simp at hne
      simp [xs]; exact List.length_pos_of_ne_nil this
    have hnil := eval_typedNil N .ADD UserOp.plus (ratNode 0) (.rat 0) (.inl ⟨rfl, rfl⟩)
      (by rw [typeof_ratNode]; rfl)
    have h0 : xs[0] = ratNode 0 := by simp [xs]
    rw [← h0] at hnil
    have hnil' : __smtx_model_eval N (__eo_to_smt (typedNil UserOp.plus xs[0].toEo)) = SmtValue.Real 0 := by
      rw [hnil]; simp [toVal]
    obtain ⟨sv, hsv, hs0, hspos⟩ := eval_plusChain hnil' xs.toList (by
      intro x hx
      simp only [xs, Array.toList_append, List.mem_append, Array.toList_map, List.mem_map] at hx
      rcases hx with hx | ⟨p, hp, rfl⟩
      · simp at hx; subst hx; exact ⟨0, by simpa using eval_ratNode N 0, le_refl _⟩
      · obtain ⟨v, hv, hv0, -⟩ := hent p (by simpa using hp)
        exact ⟨v, hv, hv0⟩)
    have hS : RVal N (Node.mkNode .ADD xs) sv := by
      unfold RVal Node.mkNode Node.toSmt
      rw [toEo_typedChain (op := UserOp.plus) rfl _ hxs]
      exact hsv
    have hz : RVal N (ratNode 0) 0 := by simpa using eval_ratNode N 0
    have hS' : RVal N (Node.app (.kind .ADD) xs) sv := hS
    -- the comparison is true
    have hF : __smtx_model_eval N (farkasAtom tl.toArray).toSmt = SmtValue.Boolean true := by
      rw [show farkasAtom tl.toArray = Node.mkNode (if tl.toArray.any (·.2) then .GT else .GEQ)
        #[Node.mkNode .ADD xs, ratNode 0] from rfl]
      unfold Node.mkNode
      split
      · rename_i hany
        have hany' : tl.any (·.2) = true := by simpa using hany
        obtain ⟨p, hp, hp2⟩ := List.any_eq_true.1 hany'
        obtain ⟨v, hv, -, hpos⟩ := hent p hp
        have hpx : p.1 ∈ xs.toList := by
          simp only [xs, Array.toList_append, Array.toList_map, List.mem_append, List.mem_map]
          exact Or.inr ⟨p, by simpa using hp, rfl⟩
        have := hspos ⟨p.1, hpx, v, hv, hpos hp2⟩
        rw [eval_gt (ds := #[Node.app (.kind .ADD) xs, ratNode 0]) rfl hS' hz]
        simpa using this
      · rw [eval_geq (ds := #[Node.app (.kind .ADD) xs, ratNode 0]) rfl hS' hz]
        simpa using hs0
    -- but it rewrites to `false`
    have hc := CondEquiv.of_equiv (Φ := fun _ => True)
      (rewrite_correct_of_logos (farkasAtom tl.toArray) (of_decide_eq_true hwt))
    rw [hrw, toEo_false] at hc
    have := (bool_of_condEquiv hc).2 N hN trivial
    rw [show __eo_to_smt (farkasAtom tl.toArray).toEo = (farkasAtom tl.toArray).toSmt from rfl, hF] at this
    simp at this
  · simp at h

omit [LogosFacts] in
/-- A true disequality of reals makes one of its strict inequalities true. -/
theorem split_sem {N : SmtModel} {l a b : Node} (h : diseqParts l = some (a, b)) (hl : TrueIn N l.toEo)
    {ra rb : ℝ} (ha : RVal N a ra) (hb : RVal N b rb) :
    TrueIn N (Node.mkNode .LT #[a, b]).toEo ∨ TrueIn N (Node.mkNode .GT #[a, b]).toEo := by
  unfold TrueIn at hl ⊢
  rw [show __eo_to_smt l.toEo = l.toSmt from rfl] at hl
  rw [show ∀ t : Node, __eo_to_smt t.toEo = t.toSmt from fun _ => rfl,
    show ∀ t : Node, __eo_to_smt t.toEo = t.toSmt from fun _ => rfl]
  unfold diseqParts at h
  split at h
  · rename_i k cs
    split at h
    · rename_i hk
      have hk : k = .NOT := by simpa using hk
      subst hk
      split at h
      · rename_i h1
        rw [not_true_iff h1] at hl
        split at h
        · rename_i k' ds he
          split at h
          · rename_i hk'
            have hk' : k' = .EQUAL := by simpa using hk'
            subst hk'
            split at h
            · rename_i h2
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rw [he, eval_equal h2 ha hb] at hl
              have hne : ra ≠ rb := by simpa using hl
              unfold Node.mkNode
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · left; rw [eval_lt (ds := #[ds[0], ds[1]]) rfl ha hb]; simpa using hlt
              · right; rw [eval_gt (ds := #[ds[0], ds[1]]) rfl ha hb]; simpa using hgt
            · simp at h
          · simp at h
        · simp at h
      · simp at h
    · simp at h
  · simp at h

end LinCertProof

end Telos.Solver
