#!/usr/bin/env python3
"""Generate verification/TelosProofs/Solver/Extend.lean from Logos's `SmtTerm`:
the constants a term mentions, and the theorem that its value does not depend
on the others (one case per constructor). Run after changing the Logos `rev`.
"""

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
s=(ROOT / '.lake/packages/Cpc/Cpc/SmtSyntax.lean').read_text()
i=s.index('inductive SmtTerm'); body=s[i:]; body=body[:re.search(r'\n\s*(deriving|end|/-|inductive)',body[20:]).start()+20]
cons=re.findall(r'^\s*\|\s*([\w«»]+)\s*:\s*(.*)$',body,re.M)
out=[]
for n,ty in cons:
    args=ty.split(' -> ')[:-1]
    terms=[k for k,a in enumerate(args) if a=='SmtTerm']
    if not terms: continue
    pat=' '.join(f'x{k}' if k in terms else '_' for k in range(len(args)))
    out.append(f'  | .{n} {pat} => '+' || '.join(f'mentions c x{k}' for k in terms))

def hs(n):
    if n==1: return ['h']
    r=[]
    for k in range(n):
        if k==0: r.append('h'+'.1'*(n-1))
        else: r.append('h'+'.1'*(n-1-k)+'.2')
    return r
CC=[]
sp={'UConst','Var','Apply','forall','exists','choice','bind'}
for n,ty in cons:
    args=ty.split(' -> ')[:-1]
    terms=[k for k,a in enumerate(args) if a=='SmtTerm']
    nm=n.strip('«»')
    if nm in sp: continue
    pat=' '.join(f'x{k}' if k in terms else '_' for k in range(len(args)))
    if not terms:
        CC.append(f'  | .{n} {pat}, M, _ => by rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def]')
        continue
    hh=hs(len(terms))
    ih=', '.join(f'eval_setConst hf x{k} M {hh[i]}' for i,k in enumerate(terms))
    CC.append(f"""  | .{n} {pat}, M, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def (M := M)]
    simp only [{ih}, nth_set hf, map_diff_set, apply_set, lookup_set M (Ne.symm hf.div),
      lookup_set M (Ne.symm hf.mod), lookup_set M (Ne.symm hf.qdiv)]""")
CASES="""  | .UConst s T, M, h => by
    simp only [mentions, decide_eq_false_iff_not] at h
    rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def]
    exact lookup_set M h T
  | .Var s T, M, _ => by
    rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def]
    exact var_set M s T
  | .Apply f x, M, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    have h1 := eval_setConst hf f M h.1
    have h2 := eval_setConst hf x M h.2
    rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def (M := M)]
    cases f <;> simp only [h1, h2, apply_set, sel_set hf]
  | .forall s T x, M, h => by
    simp only [mentions] at h
    rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def (M := M)]
    have hp : ∀ v, __smtx_model_eval (native_model_push (setConst M c U w) s T v) x =
        __smtx_model_eval (native_model_push M s T v) x := fun v => by
      rw [push_set]; exact eval_setConst hf x _ h
    exact congrArg (fun F : SmtValue → SmtValue => by
      classical
      exact if h : ∀ v : SmtValue, __smtx_typeof_value v = T → __smtx_value_canonical M.usortDom v = true →
          F v = SmtValue.Boolean true then SmtValue.Boolean true else SmtValue.Boolean false) (funext hp)
  | .exists s T x, M, h => by
    simp only [mentions] at h
    rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def (M := M)]
    have hp : ∀ v, __smtx_model_eval (native_model_push (setConst M c U w) s T v) x =
        __smtx_model_eval (native_model_push M s T v) x := fun v => by
      rw [push_set]; exact eval_setConst hf x _ h
    exact congrArg (fun F : SmtValue → SmtValue => by
      classical
      exact if h : ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical M.usortDom v = true ∧
          F v = SmtValue.Boolean true then SmtValue.Boolean true else SmtValue.Boolean false) (funext hp)
  | .choice s T x, M, h => by
    simp only [mentions] at h
    rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def (M := M)]
    have hp : ∀ v, __smtx_model_eval (native_model_push (setConst M c U w) s T v) x =
        __smtx_model_eval (native_model_push M s T v) x := fun v => by
      rw [push_set]; exact eval_setConst hf x _ h
    exact congrArg (fun F : SmtValue → SmtValue => by
      classical
      exact
        if hSat : ∃ v : SmtValue, __smtx_typeof_value v = T ∧
            __smtx_value_canonical M.usortDom v = true ∧ F v = SmtValue.Boolean true then
          Classical.choose hSat
        else if hTy : ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical M.usortDom v then
          Classical.choose hTy
        else SmtValue.NotValue) (funext hp)
  | .bind s T x y, M, h => by
    simp only [mentions, Bool.or_eq_false_iff] at h
    rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def (M := M)]
    simp only [eval_setConst hf x M h.1]
    rw [push_set]; exact eval_setConst hf y _ h.2
"""+"\n".join(CC)

(ROOT / 'verification/TelosProofs/Solver/Extend.lean').write_text('''import Telos.Core.Certified
import TelosProofs.Core.LogosFacts

/-!
# Extending a model by a constant

The value of a term that does not mention a constant is the same in a model
that differs on that constant alone (`eval_setConst`), so a model can be
extended by a definition of a new constant (`extend_def`).

Generated by `scripts/gen-extend.py`.
-/

open Eo Smtm SmtEval

set_option linter.internalConstructors false
set_option linter.unusedSimpArgs false

namespace Telos.Extend

/-- Whether a term mentions the constant named `c` (of any type). -/
def mentions (c : native_String) : SmtTerm → Bool
  | .UConst s _ => decide (s = c)
'''+'\n'.join(out)+'''
  | _ => false

/-- The model with the value `v` for the constant `c` of type `T`. -/
def setConst (M : SmtModel) (c : native_String) (T : SmtType) (v : SmtValue) : SmtModel :=
  { M with values := fun k => if k = model_key c T then v else M.values k }

/-- A name that is none of those of Logos's own functions. -/
structure Fresh (c : native_String) : Prop where
  oob : c ≠ native_oob_seq_nth_id
  div : c ≠ native_div_by_zero_id
  mod : c ≠ native_mod_by_zero_id
  qdiv : c ≠ native_qdiv_by_zero_id
  sel : ∀ n m, c ≠ native_wrong_apply_sel_id n m

variable {c : native_String} {U : SmtType} {w : SmtValue}

theorem lookup_set (M : SmtModel) {s : native_String} (h : s ≠ c) (T : SmtType) :
    native_model_lookup (setConst M c U w) s T = native_model_lookup M s T := by
  simp [native_model_lookup, setConst, model_key, h]

theorem push_set (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue) :
    native_model_push (setConst M c U w) s T v = setConst (native_model_push M s T v) c U w := by
  simp only [native_model_push, setConst, model_key, SmtModel.mk.injEq, and_true]
  funext k
  by_cases h1 : k = { isVar := true, name := s, ty := T } <;> by_cases h2 : k = { isVar := false, name := c, ty := U } <;>
    simp_all

theorem var_set (M : SmtModel) (s : native_String) (T : SmtType) :
    native_model_var_lookup (setConst M c U w) s T = native_model_var_lookup M s T := by
  simp [native_model_var_lookup, setConst, model_key]

theorem apply_set (M : SmtModel) (a b : SmtValue) :
    __smtx_model_eval_apply (setConst M c U w) a b = __smtx_model_eval_apply M a b := by
  unfold __smtx_model_eval_apply
  rfl

theorem usort_set (M : SmtModel) : (setConst M c U w).usortDom = M.usortDom := rfl

theorem nth_set (hf : Fresh c) (M : SmtModel) (a b : SmtValue) :
    __smtx_seq_nth (setConst M c U w) a b = __smtx_seq_nth M a b := by
  unfold __smtx_seq_nth __smtx_seq_nth_wrong
  simp only [lookup_set M (Ne.symm hf.oob)]

theorem sel_set (hf : Fresh c) (M : SmtModel) (s : native_String) (dd : SmtDatatypeDecl) (n m : native_Nat) (v : SmtValue) :
    __smtx_model_eval_dt_sel (setConst M c U w) s dd n m v = __smtx_model_eval_dt_sel M s dd n m v := by
  unfold __smtx_model_eval_dt_sel
  simp only [lookup_set M (Ne.symm (hf.sel _ _)), apply_set]

theorem map_diff_set (M : SmtModel) (a b : SmtValue) :
    __smtx_map_diff (setConst M c U w) a b = __smtx_map_diff M a b := by
  unfold __smtx_map_diff
  rfl

set_option maxHeartbeats 8000000 in
/-- **A term that does not mention a constant does not depend on it.** -/
theorem eval_setConst (hf : Fresh c) : ∀ (t : SmtTerm) (M : SmtModel), mentions c t = false →
    __smtx_model_eval (setConst M c U w) t = __smtx_model_eval M t
'''+CASES+'''
termination_by t => sizeOf t

/-! ## Definitions -/

variable [LogosFacts]

/-- **A model extended by a definition.** The model `N` with the value of `t` for
a new constant `c` of its type is well formed, gives `c` the value of `t`, and
gives the terms that do not mention `c` the same values. -/
theorem extend_def {N : SmtModel} (hN : model_wf N) (hf : Fresh c) {t : SmtTerm}
    (hT : __smtx_typeof t ≠ SmtType.None) (ht : mentions c t = false) :
    ∃ N', model_wf N' ∧
      __smtx_model_eval N' (.UConst c (__smtx_typeof t)) = __smtx_model_eval N' t ∧
      ∀ s, mentions c s = false → __smtx_model_eval N' s = __smtx_model_eval N s := by
  refine ⟨setConst N c (__smtx_typeof t) (__smtx_model_eval N t), ?_, ?_, fun s hs => eval_setConst hf s N hs⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hN
    have hty := LogosFacts.eval_typed N t ⟨h1, h2, h3, h4⟩ hT
    refine ⟨fun b s T hw => ?_, fun b s T hw => ?_, h3, h4⟩
    · simp only [setConst]
      split
      · rename_i e; simp only [model_key, SmtModelKey.mk.injEq] at e; rw [hty, e.2.2]
      · exact h1 b s T hw
    · simp only [setConst]
      split
      · exact LogosFacts.eval_canonical N t ⟨h1, h2, h3, h4⟩ hT
      · exact h2 b s T hw
  · rw [eval_setConst hf t N ht, __smtx_model_eval.eq_def]
    simp [native_model_lookup, setConst]

end Telos.Extend
''')
