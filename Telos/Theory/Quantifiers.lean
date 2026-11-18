import Telos.Theory.Common
import Telos.Rewriter.Rewriter
import Telos.Node.OfEo
import Telos.Theory.Nnf
import Telos.Proof.Emit
import Telos.Theory.Arith

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
  `COMPUTE_ELIM_SYMBOLS`, `Telos/Theory/Nnf.lean`).

cvc5's steps run in order, the first that changes the quantifier winning
(`computeOperation`). Not ported yet, and so skipped: eliminating shadowed
variables,
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
(`quant-var-elim-eq`), which `rw` rewrites to `false`, and the conjunction is
`false` (`absorb`). -/
def refute (rw : (m : Node) → Rw m) (v t lit : Node) (q : Node) : Option (Rw q) := do
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
    let r := r.trans (rw r.1)
    if r.1 == mkFalse then some r else none
  r.next? fun m => checkBy .absorb m mkFalse

/-- A value for `v` that makes the bound `lit` (a disjunct: `(>= a b)`, its
negation, or a positive arithmetic equation) false, if `v` has coefficient 1 or
-1 in it and occurs in no other monomial. -/
def falsifier (v lit : Node) : Option Node := do
  let (atom, neg) := match lit.getKind, lit.getChildren with
    | .NOT, #[a] => (a, true)
    | _, _ => (lit, false)
  let #[a, b] := atom.getChildren | none
  if !(Arith.isInt a || Arith.isReal a) then none
  let p := Arith.polyOf (mkNode .SUB #[a, b])
  let c ← p.findSome? fun (m, c) => if m == [v] then some c else none
  if !(c == 1 || c == -1) || p.any (fun (m, _) => m != [v] && m.contains v) then none
  let rest := p.filter (·.1 != [v])
  -- `p = c v + rest` is zero at `v = root`
  let root := Arith.Poly.scale rest (-1 / c)
  let real := Arith.isReal v
  let shifted (k : Rat) : Node := (Arith.Poly.add root (Arith.Poly.const k)).toNode real
  match atom.getKind, neg with
  -- `p >= 0` false: `p = -1`
  | .GEQ, false => some (shifted (-1 / c))
  -- `p >= 0` true: `p = 0`
  | .GEQ, true => some (shifted 0)
  -- `p = 0` false: `p = 1`
  | .EQUAL, false => some (shifted (1 / c))
  | _, _ => none

/-- cvc5's `getVarElimIneq`, when the eliminated variable `v` occurs in one
literal `L` of the body: `(forall vs (or L K))` is `(forall vs' K)`. `L` and
the value of `v` that falsifies it may use the other variables of `vs`. Certified as cvc5's proofs do: `v` split off as for variable
elimination, `L` moved first (`aci_norm`), `(forall (v) (or L K))` to
`(or (forall (v) L) K)` (`quant-miniscope-or`), `(forall (v) L)` to `false` by
`refute`, and `(or false K)` to `K` (`aci_norm`). -/
def ineqElim (rw : (m : Node) → Rw m) (n : Node) : Option (Rw n) := do
  let (_, vs, body) ← quant? n
  let disjuncts := if body.getKind == .OR then body.getChildren else #[body]
  let cands := vs.toList.mergeSort (fun a b => a.lt b) |>.filterMap fun v =>
    let uses := (List.range disjuncts.size).filter fun i => occursIn v disjuncts[i]!
    match uses with
    | [i] =>
      (falsifier v disjuncts[i]!).bind fun t =>
        -- `t` replaces `v` in the literal, which binds nothing
        let safe := !bindsAny (t.vars.filter (·.getKind == .BOUND_VARIABLE)) disjuncts[i]!
        if occursIn v t || !safe then none else some (v, i, t)
    | _ => none
  let (v, i, t) ← cands.head?
  let lit := disjuncts[i]!
  let keep := disjuncts.eraseIdx! i
  let inner (q : Node) : Option (Rw q) :=
    if keep.isEmpty then refute rw v t lit q
    else do
      let kd := if keep.size == 1 then keep[0]! else mkNode .OR keep
      let arranged := mkNode .OR #[lit, kd]
      let r := if arranged == body then Rw.id q
        else (congrBody? q fun b => (checkBy .aci_norm b arranged).getD (Rw.id b)).getD (Rw.id q)
      let r ← r.next? fun m => checkBy .quant_miniscope_or m (mkNode .OR #[mkQuant .FORALL #[v] lit, kd])
      let r ← r.next? fun m => Rw.congrArg m 0 (refute rw v t lit)
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

def rewriteForall (rw : (m : Node) → Rw m) (n : Node) : RewriteResponse n :=
  match quant? n with
  | none => .done n
  | some (_, _, body) =>
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
          fun _ => varElim rw n,          -- COMPUTE_VAR_ELIMINATION
          fun _ => ineqElim rw n,         -- (its inequality part)
          fun _ => condSplit n]           -- COMPUTE_COND_SPLIT

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
