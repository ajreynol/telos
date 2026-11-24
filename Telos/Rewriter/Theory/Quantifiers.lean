import Telos.Rewriter.Theory.Common
import Telos.Rewriter.Rewriter
import Telos.Core.Node.OfEo
import Telos.Rewriter.Theory.Nnf
import Telos.Core.Proof.Emit
import Telos.Rewriter.Theory.Arith

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
* `(forall vs (or …))` is split by classes of disjuncts connected by shared
  variables (`computeSplit`; `quant_var_reordering`, `aci_norm` and
  `quant-miniscope-or`);
* otherwise, the variables that do not occur in the body are removed
  (`quant-unused-vars`);
* before miniscoping, the body is put in negation normal form (cvc5's
  `COMPUTE_ELIM_SYMBOLS`, `Telos/Rewriter/Theory/Nnf.lean`);
* variable elimination (`computeVarElimination`): by equalities, Boolean
  variables and solved linear equations (`varElim`), and by bounds of one
  direction (`getVarElimIneq`, `ineqElim`);
* conditional splitting (`computeCondSplit`, `condSplit`);
* prenexing (`computePrenex`, cvc5's default `SIMPLE` mode, `prenex`): the
  quantifiers in positive positions of the body are pulled into the quantifier,
  certified by miniscoping backwards (`prenexRev`) and `quant-merge-prenex`.

cvc5's steps run in order, the first that changes the quantifier winning
(`computeOperation`). Not ported yet, and so skipped: eliminating shadowed
variables and datatype variable expansion.

Deviations from cvc5: cvc5 gives the quantifiers created by miniscoping fresh
bound variables (`BoundVarManager`), printed with the same names, and the
variables pulled by prenexing fresh ones (`BOUND_VARIABLE_n`); telos renames a
pulled variable only when it clashes. telos, like
Logos, identifies bound variables by name and type, so they are the same
variables. Instantiation patterns (which have no CPC counterpart) are kept or
dropped as cvc5's steps do (`rewriteForallPats`).
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

/-- Rewrite the body of a quantifier by `f` (`Certified.congrBody`). -/
def congrBody? : (n : Node) → ((b : Node) → Rw b) → Option (Rw n)
  | .app (.kind k) ⟨vs :: body :: pats⟩, f =>
    if hq : decide (k.isQuantifier = true ∧ body.WellTyped) = true then
      let b := f body
      if b.1 == body then none
      else
        have hq := of_decide_eq_true hq
        some ⟨.app (.kind k) ⟨vs :: b.1 :: pats⟩, .congrBody hq.1 hq.2 b.2 (.refl _)⟩
    else none
  | _, _ => none

/-! ### Patterns

A quantifier may have a pattern list (`INST_PATTERN_LIST`), which its CPC term
does not have. A step that keeps it, or drops it, as cvc5's does, is the step
on the quantifier without it, between steps that remove and put back the list:
the two quantifiers have the same CPC term, so `refl` proves them equal
(`castEo`). -/

/-- The pattern list of a quantifier. -/
def pats? : Node → Option Node
  | .app (.kind k) #[_, _, p] =>
    if (k == .FORALL || k == .EXISTS) && p.getKind == .INST_PATTERN_LIST then some p else none
  | _ => none

/-- The quantifier without its pattern list. -/
def stripPats : Node → Node
  | n@(.app op #[vs, body, _]) => if (pats? n).isSome then .app op #[vs, body] else n
  | n => n

/-- The list has a pattern, or a term excluded from patterns
(`QuantAttributes::hasPattern`). -/
def hasPattern (ipl : Node) : Bool :=
  ipl.getChildren.any fun p => p.getKind == .INST_PATTERN || p.getKind == .INST_NO_PATTERN

/-- `n` is `k` when their CPC terms are the same: a `refl` step. -/
def castEo (n k : Node) : Option (Rw n) :=
  let cs := CCmdList.cons (.step .refl (.cons n.toEo .nil) .nil) .nil
  if h : decide (ProvesEq cs n k) = true then some ⟨k, .step cs (of_decide_eq_true h) (.refl k)⟩
  else none

/-- `m` with the pattern list `ipl` put back on its quantifier, the result of
a step that keeps it: `(forall vs F)` or `(not (forall vs F))`. -/
def withPats (ipl : Node) : Node → Option Node
  | .app (.kind .FORALL) #[vs, body] => some (.app (.kind .FORALL) #[vs, body, ipl])
  | .app (.kind .NOT) #[.app (.kind .FORALL) #[vs, body]] =>
    some (.app (.kind .NOT) #[.app (.kind .FORALL) #[vs, body, ipl]])
  | _ => none

/-- The step `f` on the quantifier `n` without its pattern list; with `keep`,
the list put back on the result. -/
def viaStripped (n : Node) (keep : Bool) (f : (m : Node) → Option (Rw m)) : Option (Rw n) := do
  let ipl ← pats? n
  let c ← castEo n (stripPats n)
  let r ← c.next? f
  if !keep then return r
  r.next? fun m => match withPats ipl m with
    | some m' => castEo m m'
    | none => some (Rw.id m)

def respond {n : Node} (st : RewriteStatus) : Option (Rw n) → RewriteResponse n
  | some ⟨m, h⟩ => ⟨st, m, h⟩
  | none => .done n

/-- cvc5's `mergePrenex` (without removing duplicates, which telos does not
prove yet): `(Q xs (Q ys F))` is `(Q (xs ys) F)`. -/
def mergePrenex (n : Node) : Option (Rw n) := do
  -- (a quantifier with patterns is not merged into; an inner one's patterns
  -- become those of the merged quantifier)
  let (k, vs, body) ← quant? n
  let rec collect (fuel : Nat) (vs : Array Node) (body : Node) : Array Node × Node × Option Node :=
    match fuel, quant? body, pats? body with
    | fuel + 1, some (k', ws, b), _ => if k' == k then collect fuel (vs ++ ws) b else (vs, body, none)
    | _ + 1, none, some ipl =>
      match quant? (stripPats body) with
      | some (k', ws, b) => if k' == k then (vs ++ ws, b, some ipl) else (vs, body, none)
      | none => (vs, body, none)
    | _, _, _ => (vs, body, none)
  let (vs', body', ipl) := collect 1000 vs body
  if vs'.size == vs.size then none
  -- Shadowed variables would have to be renamed.
  if vs'.toList.eraseDups.length != vs'.size then none
  let r ← checkBy .quant_merge_prenex n (mkQuant k vs' body')
  match ipl with
  | none => return r
  | some ipl => r.next? fun m => castEo m (.app (.kind k) #[mkNode .BOUND_VAR_LIST vs', body', ipl])

/-- `(forall vs F)` for `F` none of `vs` occurs in is `F` (`quant-unused-vars`). -/
def dropUnused (n : Node) : Option (Rw n) := do
  let (_, vs, body) ← quant? n
  let m := mkForall vs body
  if m == n then none
  checkBy .quant_unused_vars n m

/-- cvc5's `computeSplit`: the disjuncts of `(or l₁ … lₙ)` that use none of
`vs`, then, for each class of disjuncts connected by shared variables of `vs`,
the class's variables (in the order of `vs`) and its disjuncts. `none` when
nothing would change: one class with all of `vs`, and no ground disjunct. -/
def computeSplit (vs : Array Node) (lits : Array Node) :
    Option (Array Node × Array (Array Node × Array Node)) :=
  -- classes: (id, variables, literals), in order of creation
  let step (st : Array Node × Array (Nat × Array Node × Array Node) × Nat) (l : Node) :=
    let (ground, classes, next) := st
    let lvs := vs.filter (occursIn · l)
    if lvs.isEmpty then (ground.push l, classes, next)
    else
      -- the classes of the literal's variables, in the order of its variables
      let ids := lvs.foldl (init := (#[] : Array Nat)) fun ids v =>
        match classes.find? (·.2.1.contains v) with
        | some (i, _, _) => if ids.contains i then ids else ids.push i
        | none => ids
      let newVs := lvs.filter fun v => !classes.any (·.2.1.contains v)
      match ids[0]? with
      | none => (ground, classes.push (next, newVs, #[l]), next + 1)
      | some z =>
        -- merge the other classes into `z`, in order
        let (zvs, zls) := ids.foldl (init := (#[], #[])) fun (zvs, zls) i =>
          match classes.find? (·.1 == i) with
          | some (_, cvs, cls) => (zvs ++ cvs, zls ++ cls)
          | none => (zvs, zls)
        let classes := classes.filter fun c => c.1 == z || !ids.contains c.1
        let classes := classes.map fun c =>
          if c.1 == z then (z, zvs ++ newVs, zls.push l) else c
        (ground, classes, next)
  let (ground, classes, _) := lits.foldl step (#[], #[], 0)
  let used := classes.foldl (init := 0) fun n c => n + c.2.1.size
  if classes.size > 1 || !ground.isEmpty || used != vs.size then
    some (ground, classes.map fun (_, cvs, cls) => (vs.filter cvs.contains, cls))
  else none

/-- The free-variable miniscoping of `(forall vs (or l₁ … lₙ))` (cvc5's
`computeSplit`, as part of `computeMiniscoping`): the unused variables dropped
(`quant-unused-vars`), the variables reordered by class
(`quant_var_reordering`), the disjuncts regrouped (`aci_norm`), and the
quantifier distributed over them (`quant-miniscope-or`). -/
def splitOr (n : Node) : Option (Rw n) := do
  let (_, vs, body) ← quant? n
  let (ground, classes) ← computeSplit vs body.getChildren
  let group (ls : Array Node) : Node := if ls.size == 1 then ls[0]! else mkNode .OR ls
  let disjuncts := ground ++ classes.map (group ·.2)
  let target := ground ++ classes.map fun (cvs, ls) => mkQuant .FORALL cvs (group ls)
  let orderedVs := classes.foldl (init := #[]) fun acc (cvs, _) => acc ++ cvs
  -- drop the unused variables, then reorder
  let r := (dropUnused n).getD (Rw.id n)
  let r ← if orderedVs == vs.filter (occursIn · body) then some r
    else r.next? fun m => checkBy .quant_var_reordering m (mkQuant .FORALL orderedVs body)
  -- regroup the disjuncts, as one disjunction per class
  let arranged := if target.size == 1 then group disjuncts else mkNode .OR disjuncts
  let r ← if arranged == body then some r
    else r.next? fun m => congrBody? m fun b => (checkBy .aci_norm b arranged).getD (Rw.id b)
  if target.size == 1 then some r
  else r.next? fun m => checkBy .quant_miniscope_or m (mkNode .OR target)

/-- `n` with the bound variable `x` replaced by `t`, except under binders of `x`. -/
partial def substitute (x t : Node) : Node → Node
  | n@(.boundVar ..) => if n == x then t else n
  | n@(.app op cs) =>
    match quant? n with
    | some (_, vs, _) => if vs.contains x then n else .app op (cs.map (substitute x t))
    | none => .app op (cs.map (substitute x t))
  | n => n

/-- Whether `s` can replace a variable in `body` without capture: none of its
bound variables is bound in `body` (cvc5's `isSafeSubsTerm`). -/
partial def bindsAny (vs : List Node) : Node → Bool
  | n@(.app _ cs) =>
    match quant? n with
    | some (_, ws, b) => ws.any vs.contains || bindsAny vs b
    | none => cs.any (bindsAny vs)
  | _ => false

/-- `t` negated, cvc5's `negate`: `(not t)`, or `u` for `t = (not u)`. -/
def negate (t : Node) : Node :=
  match t.getKind, t.getChildren with
  | .NOT, #[u] => u
  | _, _ => notNode t

/-- cvc5's `getVarElimLit`, for equalities and Boolean variables: whether `lit`
with polarity `pol` (not a negation) eliminates a variable of `vs` in `body`,
with the variable, its substitution, and for a solved arithmetic equation the
coefficient of the variable. -/
def varElimLit (vs : Array Node) (body lit : Node) (pol : Bool) :
    Option (Node × Node × Option Rat) :=
  let isVar (v : Node) : Bool := vs.contains v
  let safe (s : Node) : Bool := !bindsAny (s.vars.filter (·.getKind == .BOUND_VARIABLE)) body
  match lit.getKind, lit.getChildren with
  | .EQUAL, #[a, b] =>
    if pol || a.typeHint == some .boolean then
      -- solve for either side, preferring the smaller variable
      let solve (side other : Node) : Option (Node × Node) :=
        let (v, tpol) := match side.getKind, side.getChildren with
          | .NOT, #[v] => (v, !pol)
          | _, _ => (side, pol)
        if isVar v && !occursIn v other && v.typeHint == other.typeHint then
          some (v, if tpol then other else negate other)
        else none
      let r := match solve a b, solve b a with
        | some (v₀, s₀), some (v₁, s₁) => some (if v₁.lt v₀ then (v₁, s₁) else (v₀, s₀))
        | some r, none | none, some r => some r
        | none, none => none
      match r.bind fun (v, s) => if safe s then some (v, s, none) else none with
      | some r => some r
      | none =>
        -- cvc5's `getVarElimEqReal`: solve a linear equation for a variable
        -- with coefficient 1 or -1 that occurs in no other monomial
        if pol && (Arith.isInt a || Arith.isReal a) then
          let p := Arith.polyOf (mkNode .SUB #[a, b])
          let cands := p.filterMap fun (m, c) => match m with
            | [v] => if isVar v && (c == 1 || c == -1) &&
                p.all (fun (m', _) => m' == [v] || !m'.contains v) then some (v, c) else none
            | _ => none
          match cands.mergeSort (fun x y => x.1.lt y.1) with
          | (v, c) :: _ =>
            let rest := p.filter (·.1 != [v])
            let s := (Arith.Poly.scale rest (-1 / c)).toNode (Arith.isReal v)
            if safe s && !occursIn v s then some (v, s, some c) else none
          | [] => none
        else none
    else none
  | .BOUND_VARIABLE, _ => if isVar lit then some (lit, mkBool pol, none) else none
  | _, _ => none

/-- cvc5's `getVarElimInternal`: a literal of `n` with polarity `pol`, under
negations, conjunctions (`pol`) and disjunctions (not `pol`), that eliminates a
variable of `vs` in `body`. -/
partial def varElimIn (vs : Array Node) (body : Node) (n : Node) (pol : Bool) :
    Option (Node × Node × Option Rat) :=
  match n.getKind, n.getChildren with
  | .NOT, #[m] => varElimIn vs body m (!pol)
  | .AND, cs => if pol then cs.findSome? (varElimIn vs body · pol) else varElimLit vs body n pol
  | .OR, cs => if !pol then cs.findSome? (varElimIn vs body · pol) else varElimLit vs body n pol
  | _, _ => varElimLit vs body n pol

/-- The disjunct of the body (in NNF, so that eliminating literals are its
disjuncts) that eliminates a variable of `vs`, with the elimination. -/
def findVarElim (vs : Array Node) (body : Node) : Option (Nat × Node × Node × Option Rat) :=
  let disjuncts := if body.getKind == .OR then body.getChildren else #[body]
  (List.range disjuncts.size).findSome? fun i =>
    let d := disjuncts[i]!
    let (lit, pol) := match d.getKind, d.getChildren with
      | .NOT, #[l] => (l, true)
      | _, _ => (d, false)
    (varElimLit vs body lit pol).map fun (v, s, c) => (i, v, s, c)

/-- cvc5's `computeCondSplit`, in its default mode: an `ite` body whose condition
eliminates a variable (under either polarity) is
`(and (or (not c) t) (or c e))` (`ite-expand`), and a binary disjunction with a
conjunction that has an eliminating literal is distributed over it (that
disjunct moved first by `aci_norm`, then `bool-or-and-distrib`). -/
def condSplit (n : Node) : Option (Rw n) := do
  let (_, vs, body) ← quant? n
  match body.getKind, body.getChildren with
  | .ITE, #[c, _, _] =>
    if (varElimIn vs c c true).isSome || (varElimIn vs c c false).isSome then
      congrBody? n fun b => (byRule "ite-expand" b).getD (Rw.id b)
    else none
  | .OR, #[d₀, d₁] =>
    let splits (d : Node) : Bool := d.getKind == .AND && d.getChildren.any fun l =>
      let (a, pol) := match l.getKind, l.getChildren with
        | .NOT, #[a] => (a, true)
        | _, _ => (l, false)
      (varElimLit vs body a pol).isSome
    if splits d₀ then congrBody? n fun b => (byRule "bool-or-and-distrib" b).getD (Rw.id b)
    else if splits d₁ then
      -- move it first; the distribution follows in the next rewrite
      congrBody? n fun b => (checkBy .aci_norm b (mkNode .OR #[d₁, d₀])).getD (Rw.id b)
    else none
  | _, _ => none

/-- cvc5's `computeVarElimination`, for equalities and Boolean variables:
`(forall vs F)` with a disjunct of `F` giving `x = t` is `(forall vs' F')`, with
`x` eliminated. Certified as cvc5's proofs do: `x` moved last
(`quant_var_reordering`) and split off (`quant-merge-prenex`, reversed), the
disjunct moved first (`aci_norm`) and written `(not (= x t))` (by rewriting that
literal with `rw` and reversing the proof), then `quant-var-elim-eq`. -/
def varElim (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) := do
  let (_, vs, body) ← quant? n
  let (i, x, t, coeff) ← findVarElim vs body
  let others := vs.filter (· != x)
  let disjuncts := if body.getKind == .OR then body.getChildren else #[body]
  let d := disjuncts[i]!
  let rest := disjuncts.eraseIdx! i
  let lit := notNode (eqNode x t)
  -- the disjunct, written `(not (= x t))`
  let normLit (m : Node) : Option (Rw m) :=
    if m == lit then some (Rw.id m)
    else match coeff, m.getChildren with
      | some c, #[l] =>
        -- `(= a b)` is `(= x t)` by `arith_poly_norm_rel`: `c (x - t) = a - b`
        Rw.congrArg m 0 fun l' => match l'.getChildren with
          | #[a, b] => Arith.polyNormRel l' 1 c (mkNode .SUB #[a, b]) (mkNode .SUB #[x, t]) (eqNode x t)
          | _ => none
        |>.filter fun _ => l.getKind == .EQUAL
      | _, _ => Proof.reverse m (rw lit)
  -- the inner `(forall (x) F)` to `F` without `x`
  let elim (q : Node) : Option (Rw q) := do
    let r ← if rest.isEmpty then
        if d == lit then some (Rw.id q)
        else congrBody? q fun b => (normLit b).getD (Rw.id b)
      else do
        let arranged := mkNode .OR (#[d] ++ rest)
        let r := if arranged == body then Rw.id q
          else (congrBody? q fun b => (checkBy .aci_norm b arranged).getD (Rw.id b)).getD (Rw.id q)
        if d == lit then some r
        else r.next? fun m => congrBody? m fun b =>
          (Rw.congrArg b 0 normLit).getD (Rw.id b)
    let rest' := rest.map (substitute x t)
    let result := if rest'.isEmpty then mkFalse else if rest'.size == 1 then rest'[0]! else mkNode .OR rest'
    r.next? fun m => checkBy .quant_var_elim_eq m result
  if others.isEmpty then elim n
  else
    let r := if vs == others.push x then Rw.id n
      else (checkBy .quant_var_reordering n (mkQuant .FORALL (others.push x) body)).getD (Rw.id n)
    if r.1 == n && vs != others.push x then none
    let split := mkQuant .FORALL others (mkQuant .FORALL #[x] body)
    let r ← r.next? fun m => (checkBy .quant_merge_prenex split m).bind (Proof.reverse m)
    r.next? fun m => congrBody? m fun q => (elim q).getD (Rw.id q)

/-- `(forall (v) L)` is `false`, for a value `t` of `v` that makes `L` false,
as cvc5's proofs of `getVarElimIneq` do (`ensureProofMacroQuantVarElimIneq`),
without assumptions (`L` and `t` may use other bound variables, which Logos's
checker does not allow in an assumption). With `g` the guard `(= v t)`, `L` is
`(and (or (not g) L) (or g L))` (`bool-or-and-distrib`, `bool-and-conf2` and
`aci_norm`, reversed), the quantifier is distributed
over the conjunction (`quant-miniscope-and`), its first conjunct is `L[v := t]`
(`quant-var-elim-eq`), which `falsify` rewrites to `false`, and the conjunction
is `false` (`absorb`). -/
def refute (falsify : (m : Node) → Option (Rw m)) (v t lit : Node) (q : Node) : Option (Rw q) := do
  let (_, #[v'], body) ← quant? q | none
  if v' != v || body != lit then none
  let g := eqNode v t
  let conf := mkNode .AND #[notNode g, g]
  let d₁ := mkNode .OR #[notNode g, lit]
  let d₂ := mkNode .OR #[g, lit]
  -- `L` to `(and (or (not g) L) (or g L))`, as the reverse of the rewrite of
  -- the latter to `L` (a rewrite read back has only the variables of its
  -- left side, and `false` has none)
  let split (b : Node) : Option (Rw b) := do
    let dc := mkNode .AND #[d₁, d₂]
    let r ← Proof.reverse dc (← byRule "bool-or-and-distrib" (mkNode .OR #[conf, lit]))
    let r ← r.next? fun m => Rw.congrArg m 0 (byRule "bool-and-conf2")
    let r ← r.next? fun m => checkBy .aci_norm m lit
    Proof.reverse b r
  let r ← congrBody? q fun b => (split b).getD (Rw.id b)
  let r ← r.next? fun m =>
    checkBy .quant_miniscope_and m (mkNode .AND #[mkQuant .FORALL #[v] d₁, mkQuant .FORALL #[v] d₂])
  -- the first conjunct to `false`
  let r ← r.next? fun m => Rw.congrArg m 0 fun q₁ => do
    let r ← checkBy .quant_var_elim_eq q₁ (substitute v t lit)
    r.next? falsify
  r.next? fun m => checkBy .absorb m mkFalse

/-- A disjunct of the body that bounds a variable `v` (cvc5's `getVarElimIneq`):
`(>= a b)`, `(not (>= a b))` or a positive arithmetic `(= a b)`, where `a - b`
is `c v + rest`, with `v` in no other monomial. -/
structure IneqBound where
  /-- the position of the disjunct -/
  idx : Nat
  lit : Node
  neg : Bool
  isEq : Bool
  /-- the coefficient `c` of `v` -/
  coeff : Rat
  /-- the value of `v` at which `a - b` is zero, `-rest / c` -/
  root : Arith.Poly
  /-- `some true` when the disjunct is false for small values of `v` (cvc5's
  upper bounds), `some false` for large ones, `none` for an equation (cvc5's
  disequalities, false for all values but one) -/
  small : Option Bool
  deriving Inhabited

/-- cvc5's `getVarElimIneq`: the first variable of `vs` (in the term order) that
occurs only in disjuncts that bound it, in one direction (or are equations), with
the direction (`true` when they are false for small values of the variable) and
those disjuncts. A variable is ineligible when it occurs in a disjunct that is no
such bound, in a monomial other than itself, or (for an integer variable) with a
coefficient other than `1` or `-1`. -/
def ineqVar (vs : Array Node) (lits : Array Node) : Option (Node × Bool × List IneqBound) := Id.run do
  let ofVs (n : Node) : Array Node := (n.vars.filter vs.contains).toArray
  let mut inelig : Array Node := #[]
  let mut bounds : Array (Node × IneqBound) := #[]
  for i in [0:lits.size] do
    let l := lits[i]!
    let (atom, neg) := match l.getKind, l.getChildren with
      | .NOT, #[a] => (a, true)
      | _, _ => (l, false)
    let canSolve := match atom.getKind, atom.getChildren with
      | .GEQ, #[_, _] => true
      | .EQUAL, #[a, _] => !neg && (Arith.isInt a || Arith.isReal a)
      | _, _ => false
    match canSolve, atom.getChildren with
    | true, #[a, b] =>
      let p := Arith.polyOf (mkNode .SUB #[a, b])
      for (m, c) in p do
        match m with
        | [] => pure ()
        | [w] =>
          if inelig.contains w then pure ()
          else if vs.contains w then
            if c != 0 && (Arith.isReal w || c == 1 || c == -1) then
              let small := if atom.getKind == .EQUAL then none else some (neg != decide (c > 0))
              let root := Arith.Poly.scale (p.filter (·.1 != [w])) (-1 / c)
              bounds := bounds.push (w, ⟨i, l, neg, atom.getKind == .EQUAL, c, root, small⟩)
            else inelig := inelig.push w
          else inelig := inelig ++ ofVs w
        | m => inelig := inelig ++ m.foldl (fun acc a => acc ++ ofVs a) #[]
    | _, _ => inelig := inelig ++ ofVs l
  for v in vs.toList.mergeSort (fun a b => a.lt b) do
    if inelig.contains v then continue
    let bs := (bounds.filter (·.1 == v)).toList.map (·.2)
    if bs.isEmpty then continue
    if !bs.any (·.small == some true) then return some (v, false, bs)
    if !bs.any (·.small == some false) then return some (v, true, bs)
  return none

/-- For one bound, a value of `v` that makes it false: `a - b` is `-1` for
`(>= a b)`, `0` for `(not (>= a b))` and `1` for `(= a b)`. -/
def falsifier (real : Bool) (bd : IneqBound) : Node :=
  let k : Rat := if bd.isEq then 1 else if bd.neg then 0 else -1
  (Arith.Poly.add bd.root (Arith.Poly.const (k / bd.coeff))).toNode real

/-- The proof that the disjunction `E[v := t]` of the bounds `bds` of `v`, which
all are false for small values of `v` (`small`) or all for large ones, is
`false`, for `t` the least (or greatest) of their limits, as cvc5's
`ensureProofMacroQuantVarElimIneq` does. A bound's limit `B` is its root `r`,
less (more) `1` for a strict bound (`(>= a b)` and `(= a b)`, which are false
for `v < r`, or `v ≠ r`, when `c > 0`). `t` is `T₁ = B₁`,
`Tₖ = (ite (< Bₖ Tₖ₋₁) Bₖ Tₖ₋₁)` (or `(ite (>= Bₖ Tₖ₋₁) Bₖ Tₖ₋₁)`). Each
`(<= t Bₖ)` (or `(<= Bₖ t)`) is `arith-min-lt1`, `arith-min-lt2` (or
`arith-max-geq1`, `arith-max-geq2`) and transitivity (`arith_sum_ub` and
`arith_poly_norm_rel`); for a strict bound, `(< t r)` (or `(< r t)`) follows
by adding `(< 0 1)`. Each bound, at `t`, is written with `t` alone on one side
(`arith_poly_norm_rel`), and is `false` by that fact (`arith-elim-lt`,
`arith-elim-leq`, and `arith-eq-elim-*` and `absorb` for an equation). -/
structure IneqChain where
  /-- the value of `v` -/
  t : Node
  /-- the proof of `(= E[v := t] false)`, from `E[v := t]` -/
  falsify : (m : Node) → Option (Rw m)

def ineqChain (v : Node) (small : Bool) (bds : List IneqBound) : Option IneqChain := do
  let real := Arith.isReal v
  let num (c : Rat) : Node := Arith.constNode real c
  let strict (bd : IneqBound) : Bool := !bd.neg
  let limit (bd : IneqBound) : Node :=
    if strict bd then
      (Arith.Poly.add bd.root (Arith.Poly.const (if small then -1 else 1))).toNode real
    else bd.root.toNode real
  let Bs := bds.map limit
  let B₁ ← Bs.head?
  -- `T₁ … Tₙ`
  let Ts := (Bs.drop 1).foldl (init := [B₁]) fun Ts B =>
    let T := Ts.getLast!
    Ts ++ [iteNode (mkNode (if small then .LT else .GEQ) #[B, T]) B T]
  let t := Ts.getLast!
  let st := fun (r : CRule) (args : List Node) (prems : List Nat) =>
    Proof.push ⟨r, args.map .node, prems, .step⟩
  -- `(r X Y)`, from the fact `f` (`(r X₀ Y₀)`, with `X₀ - Y₀ = X - Y`)
  let normRel (f : Nat) (from_ to_ : Node) : Proof.EmitM Nat := do
    match from_.getChildren, to_.getChildren with
    | #[x₀, y₀], #[x, y] =>
      let pn ← st .arith_poly_norm [Arith.scaledEq real 1 1 (mkNode .SUB #[x₀, y₀]) (mkNode .SUB #[x, y])] []
      let e ← st .arith_poly_norm_rel [eqNode from_ to_] [pn]
      st .eq_resolve [] [f, e]
    | _, _ => throw "normRel"
  -- `(<= x z)` from `(<= x y)` and `(<= y z)`
  let leTrans (f₁ f₂ : Nat) (x y z : Node) : Proof.EmitM Nat := do
    let s ← st .arith_sum_ub [] [f₁, f₂]
    normRel s (mkNode .LEQ #[mkNode .ADD #[x, y], mkNode .ADD #[y, z]]) (mkNode .LEQ #[x, z])
  -- the fact `le x y`, from `(= (le' …) true)` for `le'` the rule's relation
  let ofTrue (e : Nat) (x y : Node) : Proof.EmitM Nat := do
    let f ← st .true_elim [] [e]
    if small then pure f
    else
      -- `(>= y x)` to `(<= x y)`
      let e ← st .arith_elim_leq [x, y] []
      let e ← st .symm [] [e]
      st .eq_resolve [] [f, e]
  let ff := mkFalse
  let run (et : Node) : Proof.EmitM Nat := do
    -- `le Tₖ Bₖ` and `le Tₖ Tₖ₋₁`, for `k ≥ 2`
    let n := Ts.length
    let mut toB : Array (Option Nat) := Array.replicate n none
    let mut toPrev : Array (Option Nat) := Array.replicate n none
    for k in [1:n] do
      let (r₁, r₂) := if small then (CRule.arith_min_lt1, CRule.arith_min_lt2)
        else (CRule.arith_max_geq1, CRule.arith_max_geq2)
      let B := Bs[k]!
      let T := Ts[k-1]!
      let e₁ ← st r₁ [B, T] []
      toB := toB.set! k (some (← if small then ofTrue e₁ Ts[k]! B else ofTrue e₁ B Ts[k]!))
      let e₂ ← st r₂ [B, T] []
      toPrev := toPrev.set! k (some (← if small then ofTrue e₂ Ts[k]! T else ofTrue e₂ T Ts[k]!))
    -- `le t Tₖ`, for `k < n`, from the top
    let mut toT : Array (Option Nat) := Array.replicate n none
    for j in [0:n-1] do
      let k := n - 2 - j
      let f ← match toT[k+1]!, toPrev[k+1]! with
        | none, some p => pure p
        | some f, some p =>
          if small then leTrans f p t Ts[k+1]! Ts[k]! else leTrans p f Ts[k]! Ts[k+1]! t
        | _, none => throw "chain"
      toT := toT.set! k (some f)
    -- per bound, `(= L[v := t] false)`
    let zero := num 0
    let one := num 1
    let mut eqs : List Nat := []
    for k in [0:n] do
      let bd := bds[k]!
      -- `le t Bₖ`
      let f ← match toT[k]!, toB[k]! with
        | none, some p => pure p
        | some f, none => pure f
        | some f, some p =>
          if small then leTrans f p t Ts[k]! Bs[k]! else leTrans p f Bs[k]! Ts[k]! t
        | none, none => throw "bound"
      let r := bd.root.toNode real
      -- the bound at `t` is `(k' x y)` or `(not (>= x y))`
      let (x, y) :=
        if bd.isEq then (if small then (t, r) else (r, t))
        else if bd.coeff > 0 then (t, r) else (r, t)
      let atomT := mkNode (if bd.isEq then .EQUAL else .GEQ) #[x, y]
      let litT := substitute v t bd.lit
      let cy := if x == t then bd.coeff else -bd.coeff
      let normAtom (a : Node) : Option (Rw a) := do
        let #[p, q] := a.getChildren | none
        Arith.polyNormRel a 1 cy (mkNode .SUB #[p, q]) (mkNode .SUB #[x, y]) atomT
      let rLit ← match bd.neg with
        | true => (Rw.congrArg litT 0 normAtom).elim (throw "norm") pure
        | false => (normAtom litT).elim (throw "norm") pure
      let e₁ ← Proof.closeChain litT (← Proof.emitChain rLit.2)
      -- `(= (>= x y) false)` from `(< x y)`
      let geqFalse (lt : Nat) : Proof.EmitM Nat := do
        let e ← st .arith_elim_lt [x, y] []
        let n ← st .eq_resolve [] [lt, e]
        st .false_intro [] [n]
      -- `(< x y)`, from `le t B`, `B = r ∓ 1`
      let strictLt : Proof.EmitM Nat := do
        let z ← st .evaluate [mkNode .LT #[zero, one]] []
        let z ← st .true_elim [] [z]
        let s ← st .arith_sum_ub [] [f, z]
        let (X, Y) := if small then (t, Bs[k]!) else (Bs[k]!, t)
        normRel s (mkNode .LT #[mkNode .ADD #[X, zero], mkNode .ADD #[Y, one]]) (mkNode .LT #[x, y])
      let e ← if bd.isEq then do
          let gf ← geqFalse (← strictLt)
          let le' := mkNode .LEQ #[x, y]
          let el ← st (if real then .arith_eq_elim_real else .arith_eq_elim_int) [x, y] []
          let rl ← st .refl [le'] []
          let c ← st .nary_cong [mkNode .AND #[mkNode .GEQ #[x, y], le']] [gf, rl]
          let ab ← st .absorb [eqNode (mkNode .AND #[ff, le']) ff] []
          st .trans [] [e₁, el, c, ab]
        else if bd.neg then do
          -- `(<= y x)` to `(>= x y)`, which is `true`
          let e ← st .arith_elim_leq [y, x] []
          let g ← st .eq_resolve [] [f, e]
          let tr ← st .true_intro [] [g]
          let c ← st .cong [notNode atomT] [tr]
          let ev ← st .evaluate [notNode (mkBool true)] []
          st .trans [] [e₁, c, ev]
        else do
          let gf ← geqFalse (← strictLt)
          st .trans [] [e₁, gf]
      eqs := eqs ++ [e]
    -- the disjunction
    let c ← Proof.congStep et (match et with | .app op _ => op | _ => .kind .OR) eqs
    let ev ← st .evaluate [mkNode .OR (Array.replicate n ff)] []
    st .trans [] [c, ev]
  let falsify (m : Node) : Option (Rw m) := do
    let (_, s) ← ((run m).run {}).toOption
    let r ← applyCmds ((Proof.toCmds s.steps).foldr .cons .nil) m
    if r.1 == ff then some r else none
  return ⟨t, falsify⟩

/-- cvc5's `getVarElimIneq`: `(forall vs (or L₁ … Lₙ K))`, for the disjuncts
`Lᵢ` bounding a variable `v` of `vs` (`ineqVar`), is `(forall vs' K)`.
Certified as cvc5's proofs do: `v` split off as for variable elimination, the
`Lᵢ` moved first and grouped (`aci_norm`), `(forall (v) (or E K))` to
`(or (forall (v) E) K)` (`quant-miniscope-or`), `(forall (v) E)` to `false` by
`refute`, and `(or false K)` to `K` (`aci_norm`). For one bound, the value of
`v` makes it constant (`falsifier`, and `rw` rewrites it to `false`); for
several, it is `ineqChain`. -/
def ineqElim (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) := do
  let (_, vs, body) ← quant? n
  let disjuncts := if body.getKind == .OR then body.getChildren else #[body]
  let (v, small, bds) ← ineqVar vs disjuncts
  let real := Arith.isReal v
  let elim := bds.map (·.idx)
  let lits := (bds.map (·.lit)).toArray
  let lit := if lits.size == 1 then lits[0]! else mkNode .OR lits
  let (t, falsify) ← match bds with
    | [bd] =>
      let t := falsifier real bd
      some (t, fun m => let r := rw m; if r.1 == mkFalse then some r else none)
    | _ => (ineqChain v small bds).map fun c => (c.t, c.falsify)
  -- `t` replaces `v` in the bounds, which must not capture its variables
  if occursIn v t || bindsAny (t.vars.filter (·.getKind == .BOUND_VARIABLE)) lit then none
  let keep := (List.range disjuncts.size).filter (!elim.contains ·) |>.map (disjuncts[·]!) |>.toArray
  let inner (q : Node) : Option (Rw q) :=
    if keep.isEmpty then
      let r := if lit == body then Rw.id q
        else (congrBody? q fun b => (checkBy .aci_norm b lit).getD (Rw.id b)).getD (Rw.id q)
      r.next? (refute falsify v t lit)
    else do
      let kd := if keep.size == 1 then keep[0]! else mkNode .OR keep
      let arranged := mkNode .OR #[lit, kd]
      let r := if arranged == body then Rw.id q
        else (congrBody? q fun b => (checkBy .aci_norm b arranged).getD (Rw.id b)).getD (Rw.id q)
      let r ← r.next? fun m => checkBy .quant_miniscope_or m (mkNode .OR #[mkQuant .FORALL #[v] lit, kd])
      let r ← r.next? fun m => Rw.congrArg m 0 (refute falsify v t lit)
      r.next? fun m => checkBy .aci_norm m kd
  let others := vs.filter (· != v)
  if others.isEmpty then inner n
  else
    let r := if vs == others.push v then Rw.id n
      else (checkBy .quant_var_reordering n (mkQuant .FORALL (others.push v) body)).getD (Rw.id n)
    if r.1 == n && vs != others.push v then none
    let split := mkQuant .FORALL others (mkQuant .FORALL #[v] body)
    let r ← r.next? fun m => (checkBy .quant_merge_prenex split m).bind (Proof.reverse m)
    r.next? fun m => congrBody? m fun q => (inner q).getD (Rw.id q)

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
  | .OR, _ => (splitOr n).orElse fun _ => dropUnused n
  | _, _ => dropUnused n

/-! ### Prenexing (`COMPUTE_PRENEX`, cvc5's default `SIMPLE` mode) -/

/-- Whether `n` contains a quantifier (cvc5's `hasClosure`). -/
partial def hasQuant (n : Node) : Bool :=
  (quant? n).isSome || n.getChildren.any hasQuant

/-- The bound variables occurring free in `n`, and how many quantifiers of `n`
bind each variable (as a tree). -/
partial def binderInfo (n : Node) (bound : List Node := []) :
    StateM (Std.HashSet Node × Std.HashMap Node Nat) Unit := do
  match n with
  | .boundVar .. =>
    if !bound.contains n then modify fun (f, c) => (f.insert n, c)
  | .app _ cs =>
    match quant? n with
    | some (_, vs, b) =>
      for v in vs do modify fun (f, c) => (f, c.insert v (c.getD v 0 + 1))
      binderInfo b (vs.toList ++ bound)
    | none => for c in cs do binderInfo c bound
  | _ => pure ()

structure PrenexSt where
  /-- The variables of the quantifier so far: its own, then those pulled. -/
  args : Array Node
  /-- Variables that a pulled variable must not be named as. -/
  taken : Std.HashSet Node
  /-- All the variables of the quantifier, for fresh names. -/
  all : Std.HashSet Node
  /-- Whether a quantifier was pulled from below a negation (not certified). -/
  underNot : Bool := false

/-- A pulled variable: itself if it is not taken, else a fresh variable of the
same type (`v_1`, `v_2`, …), as cvc5 gives each pulled variable a fresh one. -/
def PrenexSt.fresh (v : Node) : StateM PrenexSt Node := do
  let st ← get
  let v' := match v with
    | .boundVar name T =>
      if !st.taken.contains v then v
      else Id.run do
        let mut k := 1
        let mut w := Node.boundVar s!"{name}_{k}" T
        for _ in [0:10000] do
          if !st.all.contains w && !st.taken.contains w then break
          k := k + 1
          w := Node.boundVar s!"{name}_{k}" T
        return w
    | _ => v
  set { st with args := st.args.push v', taken := st.taken.insert v', all := st.all.insert v' }
  return v'

/-- cvc5's `computePrenex` with `pol` and not aggressive: the quantifiers in
positive positions (below `and`, `or`, the branches of `ite` and negations)
replaced by their bodies, their variables (renamed) added to the state. -/
partial def computePrenex (pol : Bool) (b : Node) : StateM PrenexSt Node := do
  if !hasQuant b then return b
  match quant? b with
  | some (.FORALL, vs, body) =>
    if !pol then return b
    let mut body := body
    for v in vs do
      let v' ← PrenexSt.fresh v
      if v' != v then body := substitute v v' body
    return body
  | some _ => return b
  | none =>
    let k := b.getKind
    let cs := b.getChildren
    let pols : Array (Option Bool) := match k with
      | .AND | .OR => cs.map fun _ => some pol
      | .NOT => #[some !pol]
      | .ITE => #[none, some pol, some pol]
      | .IMPLIES => #[some !pol, some pol]
      | _ => cs.map fun _ => none
    if b.typeHint != some .boolean || pols.size != cs.size then return b
    let before := (← get).args.size
    let mut cs' := #[]
    for i in [0:cs.size] do
      match pols[i]! with
      | some p => cs' := cs'.push (← computePrenex p cs[i]!)
      | none => cs' := cs'.push cs[i]!
    if cs' == cs then return b
    if k != .AND && k != .OR && k != .ITE && (← get).args.size != before then
      modify fun st => { st with underNot := true }
    if k == .NOT then
      if let .app (.kind .NOT) #[u] := cs'[0]! then return u
    return .app (.kind k) cs'

/-- `(forall ys b₂) = b₁`, for `b₂` the prenexed form of `b₁` whose pulled
variables are `ys`, as cvc5 elaborates `MACRO_QUANT_PRENEX`: through an `or`,
`quant-miniscope-or` gives each disjunct its variables; through an `and` or the
branches of an `ite`, `quant-miniscope-and` (`-ite`) gives each all of them, and
`quant-unused-vars` keeps its own; a pulled quantifier is itself, or for
renamed variables its `alpha_equiv` renaming. -/
partial def prenexRev (ys : Array Node) (b₁ b₂ : Node) : Option (Rw (mkQuant .FORALL ys b₂)) := do
  let n := mkQuant .FORALL ys b₂
  if n == b₁ then return Rw.id n
  let own (c : Node) : Array Node := ys.filter (occursIn · c)
  match quant? b₁ with
  | some (.FORALL, vs, body) =>
    -- a pulled quantifier, its variables renamed (the same quantifier is `Rw.id`)
    if vs.size != ys.size then none
    let r ← applyCmds (.cons (.step .alpha_equiv (.cons b₁.toEo (.cons (mkNode .BOUND_VAR_LIST vs).toEo
      (.cons (mkNode .BOUND_VAR_LIST ys).toEo .nil))) .nil) .nil) b₁
    if r.1 != n || body == b₂ && vs == ys then none
    Proof.reverse n r
  | _ =>
    match b₁.getKind, b₁.getChildren, b₂.getChildren with
    | .OR, cs, cs' =>
      if cs.size != cs'.size then none
      let gs := cs'.map fun c => let zs := own c; if zs.isEmpty then c else mkQuant .FORALL zs c
      let r ← checkBy .quant_miniscope_or n (mkNode .OR gs)
      (List.range cs.size).foldlM (init := r) fun r i => do
        let zs := own cs'[i]!
        if zs.isEmpty then (if cs[i]! == cs'[i]! then some r else none)
        else r.next? fun m => Rw.congrArg m i fun q =>
          if h : q = mkQuant .FORALL zs cs'[i]! then (prenexRev zs cs[i]! cs'[i]!).map fun s => h ▸ s
          else none
    | .AND, cs, cs' =>
      if cs.size != cs'.size then none
      let r ← checkBy .quant_miniscope_and n (mkNode .AND (cs'.map (mkQuant .FORALL ys)))
      (List.range cs.size).foldlM (init := r) fun r i => do
        let zs := own cs'[i]!
        r.next? fun m => Rw.congrArg m i fun q => do
          let tgt := if zs.isEmpty then cs'[i]! else mkQuant .FORALL zs cs'[i]!
          let r₁ : Rw q ← if q == tgt then some (Rw.id q) else checkBy .quant_unused_vars q tgt
          if zs.isEmpty then (if r₁.1 == cs[i]! then some r₁ else none)
          else r₁.next? fun q' => if h : q' = mkQuant .FORALL zs cs'[i]! then
            (prenexRev zs cs[i]! cs'[i]!).map fun s => h ▸ s else none
    | .ITE, #[a, t, e], #[a', t', e'] =>
      if a != a' then none
      let r ← checkBy .quant_miniscope_ite n (iteNode a (mkQuant .FORALL ys t') (mkQuant .FORALL ys e'))
      [(1, t, t'), (2, e, e')].foldlM (init := r) fun r (i, c, c') => do
        let zs := own c'
        r.next? fun m => Rw.congrArg m i fun q => do
          let tgt := if zs.isEmpty then c' else mkQuant .FORALL zs c'
          let r₁ : Rw q ← if q == tgt then some (Rw.id q) else checkBy .quant_unused_vars q tgt
          if zs.isEmpty then (if r₁.1 == c then some r₁ else none)
          else r₁.next? fun q' => if h : q' = mkQuant .FORALL zs c' then
            (prenexRev zs c c').map fun s => h ▸ s else none
    | _, _, _ => none

/-- `COMPUTE_PRENEX`: `(forall xs F)` is `(forall xs ys F')`, for `F'` the
prenexed `F` and `ys` its pulled variables: `F = (forall ys F')`
(`prenexRev`, reversed) below the quantifier, then `quant-merge-prenex`. -/
def prenex (n : Node) : Option (Rw n) := do
  let (_, xs, b₁) ← quant? n
  if !hasQuant b₁ then none
  let ((), (free, counts)) := (binderInfo n).run ({}, {})
  let multi := counts.toList.filterMap fun (v, k) => if k > 1 then some v else none
  let taken := (multi.foldl (·.insert ·) free).insertMany xs
  let all : Std.HashSet Node := (n.vars.foldl (·.insert ·) {})
  let (b₂, st) := (computePrenex true b₁).run { args := xs, taken, all }
  let ys := st.args.extract xs.size st.args.size
  if ys.isEmpty || st.underNot then none
  let rev ← prenexRev ys b₁ b₂
  let fwd ← Proof.reverse b₁ rev
  let r ← congrBody? n fun b => if h : b = b₁ then h ▸ fwd else Rw.id b
  r.next? fun m => checkBy .quant_merge_prenex m (mkQuant .FORALL (xs ++ ys) b₂)

/-- `rewriteForall` on a quantifier with patterns (cvc5's `doOperation`): the
steps that keep them (`COMPUTE_ELIM_SYMBOLS`, `COMPUTE_COND_SPLIT`), those that
drop them (variable elimination: `computeOperation` keeps them only if no
variable goes); no miniscoping or prenexing with a pattern
(`miniscope-quant-user`, `prenex-quant-user` off), unless the body has no
variable. -/
def rewriteForallPats (rw : (m : Node) → Rw m) (n : Node) (ipl : Node) : RewriteResponse n :=
  let n0 := stripPats n
  match quant? n0 with
  | none => .done n
  | some (_, vs, body) =>
    if body.isConst && body.getKind == .CONST_BOOLEAN then
      respond .REWRITE_DONE ((castEo n n0).bind (·.next? fun m => checkBy .quant_unused_vars m body))
    else
      let structural := !hasPattern ipl || !vs.any (occursIn · body)
      respond .REWRITE_AGAIN_FULL <| firstOf [
        fun _ => congrBody? n Nnf.nnf,
        -- (the list is kept when only unused variables go, a quantifier the
        -- result: `computeArgVec2`, `mkForAll`; a split drops it)
        fun _ => if structural then viaStripped n true miniscope else none,
        fun _ => if structural then viaStripped n false prenex else none,
        fun _ => viaStripped n false (varElim rw),
        fun _ => if hasPattern ipl then none else viaStripped n false (ineqElim rw),
        fun _ => viaStripped n true condSplit]

def rewriteForall (rw : (m : Node) → Rw m) (n : Node) : RewriteResponse n :=
  match quant? n with
  | none => match pats? n with
    | some ipl => rewriteForallPats rw n ipl
    | none => .done n
  | some (_, _, body) =>
    -- one the theory of strings made is not standard (`isStandard`)
    if n.isBoundedForall && !body.isConst then
      respond .REWRITE_AGAIN_FULL <| firstOf [fun _ => congrBody? n Nnf.nnf, fun _ => condSplit n]
    else
    match mergePrenex n with
    | some ⟨m, h⟩ => ⟨.REWRITE_AGAIN_FULL, m, h⟩
    | none =>
      if body.isConst && body.getKind == .CONST_BOOLEAN then
        respond .REWRITE_DONE (checkBy .quant_unused_vars n body)
      else
        -- cvc5's steps, in order (`computeOperation`), the first that applies
        respond .REWRITE_AGAIN_FULL <| firstOf [
          fun _ => congrBody? n Nnf.nnf,  -- COMPUTE_ELIM_SYMBOLS
          fun _ => miniscope n,           -- COMPUTE_MINISCOPING
          fun _ => prenex n,              -- COMPUTE_PRENEX
          fun _ => varElim rw n,          -- COMPUTE_VAR_ELIMINATION
          fun _ => ineqElim rw n,         -- (its inequality part)
          fun _ => condSplit n]           -- COMPUTE_COND_SPLIT

/-- `(exists vs F)` is `(not (forall vs (not F)))` (`exists-elim`). -/
def rewriteExists (n : Node) : RewriteResponse n :=
  match quant? n with
  | some (_, vs, body) =>
    respond .REWRITE_AGAIN_FULL
      (checkBy .exists_elim n (notNode (mkQuant .FORALL vs (notNode body))))
  | none =>
    -- with patterns, kept (`EXISTS_ELIM`)
    if (pats? n).isSome then
      respond .REWRITE_AGAIN_FULL (viaStripped n true fun m => match quant? m with
        | some (_, vs, body) => checkBy .exists_elim m (notNode (mkQuant .FORALL vs (notNode body)))
        | none => none)
    else .done n

def preRewrite (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .FORALL | .EXISTS => respond .REWRITE_AGAIN_FULL (mergePrenex n)
  | _ => .done n

def postRewrite (rw : (m : Node) → Rw m) (n : Node) : RewriteResponse n :=
  match n.getKind with
  | .EXISTS => rewriteExists n
  | .FORALL => rewriteForall rw n
  | _ => .done n

end QuantifiersRewriter

/-- cvc5's `QuantifiersRewriter`, in part (see the module documentation), with
`rw` the rewriter for the literals of variable elimination. -/
def TheoryRewriter.quantifiers (rw : (m : Node) → Rw m) : TheoryRewriter where
  preRewrite := QuantifiersRewriter.preRewrite
  postRewrite := QuantifiersRewriter.postRewrite rw

end Telos
