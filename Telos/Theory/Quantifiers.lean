import Telos.Theory.Common
import Telos.Rewriter.Rewriter
import Telos.Node.OfEo

/-!
# The quantifiers rewriter

A port of cvc5's `QuantifiersRewriter` (`src/theory/quantifiers/quantifiers_rewriter.cpp`),
in stages. Ported so far:

* `exists` is `(not (forall vs (not F)))` (`postRewrite`, `exists-elim`);
* nested quantifiers of the same kind are merged (`mergePrenex`, in pre- and
  post-rewriting; `quant-merge-prenex`), when no variable is shadowed;
* a quantifier with a constant body is the body (`quant-unused-vars`);
* miniscoping (`computeMiniscoping`, cvc5's default `CONJ_AND_FV`):
  `(forall vs (and F₁ … Fₙ))` is `(and (forall vs F₁) … (forall vs Fₙ))`, with
  the conjuncts that use none of `vs` left unquantified
  (`quant-miniscope-and`, then `quant-unused-vars`), and likewise for an `ite`
  whose condition uses none of `vs` (`quant-miniscope-ite`);
* otherwise, the variables that do not occur in the body are removed
  (`quant-unused-vars`).

cvc5's steps run in order, the first that changes the quantifier winning
(`computeOperation`). Not ported yet, and so skipped: eliminating shadowed
variables, the NNF of the body (`COMPUTE_ELIM_SYMBOLS`, which cvc5 tries before
miniscoping), splitting disjunctions by free variables (`computeSplit`),
prenexing, variable elimination, datatype variable expansion and conditional
splitting.

Deviations from cvc5: cvc5 gives the quantifiers created by miniscoping fresh
bound variables (`BoundVarManager`), printed with the same names. telos, like
Logos, identifies bound variables by name and type, so they are the same
variables. Instantiation patterns are dropped (they have no CPC counterpart).
-/

open Eo

namespace Telos

namespace QuantifiersRewriter

open Node

/-- A quantifier without patterns: its kind, bound variables and body. -/
def quant? : Node → Option (Kind × Array Node × Node)
  | .app (.kind k) #[.app (.kind .BOUND_VAR_LIST) vs, body] =>
    if k == .FORALL || k == .EXISTS then some (k, vs, body) else none
  | _ => none

def mkQuant (k : Kind) (vs : Array Node) (body : Node) : Node :=
  mkNode k #[mkNode .BOUND_VAR_LIST vs, body]

/-- Whether `v` occurs in `n`. -/
def occursIn (v n : Node) : Bool := n.vars.contains v

/-- `(forall vs F)`, or `F` itself when no variable of `vs` occurs in it. -/
def mkForall (vs : Array Node) (body : Node) : Node :=
  let active := vs.filter (occursIn · body)
  if active.isEmpty then body else mkQuant .FORALL active body

def respond {n : Node} (st : RewriteStatus) : Option (Rw n) → RewriteResponse n
  | some ⟨m, h⟩ => ⟨st, m, h⟩
  | none => .done n

/-- cvc5's `mergePrenex` (without removing duplicates, which telos does not
prove yet): `(Q xs (Q ys F))` is `(Q (xs ys) F)`. -/
def mergePrenex (n : Node) : Option (Rw n) := do
  let (k, vs, body) ← quant? n
  let rec collect (fuel : Nat) (vs : Array Node) (body : Node) : Array Node × Node :=
    match fuel, quant? body with
    | fuel + 1, some (k', ws, b) => if k' == k then collect fuel (vs ++ ws) b else (vs, body)
    | _, _ => (vs, body)
  let (vs', body') := collect 1000 vs body
  if vs'.size == vs.size then none
  -- Shadowed variables would have to be renamed.
  if vs'.toList.eraseDups.length != vs'.size then none
  checkBy .quant_merge_prenex n (mkQuant k vs' body')

/-- `(forall vs F)` for `F` none of `vs` occurs in is `F` (`quant-unused-vars`). -/
def dropUnused (n : Node) : Option (Rw n) := do
  let (_, vs, body) ← quant? n
  let m := mkForall vs body
  if m == n then none
  checkBy .quant_unused_vars n m

/-- cvc5's `computeMiniscoping`. -/
def miniscope (n : Node) : Option (Rw n) := do
  let (_, vs, body) ← quant? n
  let uses (c : Node) : Bool := vs.any (occursIn · c)
  match body.getKind, body.getChildren with
  | .AND, cs =>
    -- `(and (forall vs F₁) …)`, then each conjunct without `vs` unquantified
    let r ← checkBy .quant_miniscope_and n (mkNode .AND (cs.map (mkQuant .FORALL vs)))
    (List.range cs.size).foldlM (init := r) fun r i =>
      if uses cs[i]! then some r
      else r.next? fun m => Rw.congrArg m i dropUnused
  | .ITE, #[c, t, e] =>
    if uses c then dropUnused n
    else
      let r ← checkBy .quant_miniscope_ite n (iteNode c (mkQuant .FORALL vs t) (mkQuant .FORALL vs e))
      [1, 2].foldlM (init := r) fun r i =>
        if uses #[c, t, e][i]! then some r
        else r.next? fun m => Rw.congrArg m i dropUnused
  | _, _ => dropUnused n

def rewriteForall (n : Node) : RewriteResponse n :=
  match quant? n with
  | none => .done n
  | some (_, _, body) =>
    match mergePrenex n with
    | some ⟨m, h⟩ => ⟨.REWRITE_AGAIN_FULL, m, h⟩
    | none =>
      if body.isConst && body.getKind == .CONST_BOOLEAN then
        respond .REWRITE_DONE (checkBy .quant_unused_vars n body)
      else respond .REWRITE_AGAIN_FULL (miniscope n)

/-- `(exists vs F)` is `(not (forall vs (not F)))` (`exists-elim`). -/
def rewriteExists (n : Node) : RewriteResponse n :=
  match quant? n with
  | some (_, vs, body) =>
    respond .REWRITE_AGAIN_FULL
      (checkBy .exists_elim n (notNode (mkQuant .FORALL vs (notNode body))))
  | none => .done n

def preRewrite (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .FORALL | .EXISTS => respond .REWRITE_AGAIN_FULL (mergePrenex n)
  | _ => .done n

def postRewrite (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .EXISTS => rewriteExists n
  | .FORALL => rewriteForall n
  | _ => .done n

end QuantifiersRewriter

/-- cvc5's `QuantifiersRewriter`, in part (see the module documentation). -/
def TheoryRewriter.quantifiers : TheoryRewriter where
  preRewrite := QuantifiersRewriter.preRewrite
  postRewrite := QuantifiersRewriter.postRewrite

end Telos
