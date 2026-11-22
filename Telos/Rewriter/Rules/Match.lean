import Telos.Rewriter.Rules.Pattern

/-!
# Matching rule patterns

`RuleSpec.allMatches` finds every way the left-hand side of a rule matches a node,
and `RuleSpec.apply` turns a match into a certified rewrite: it builds the CPC
command list (an `evaluate` step per premise, then the rule) and runs it through
Logos's checker (`applyCmds`). This file is untrusted (see `Pattern.lean`).
-/

open Eo

namespace Telos

namespace Rw

/-- Continue a rewrite with a step on its result. If the step does not apply,
stop where we are. -/
def next {n : Node} (r : Rw n) (f : (m : Node) → Option (Rw m)) : Rw n :=
  match f r.1 with
  | some ⟨k, h⟩ => ⟨k, r.2.trans h⟩
  | none => r

/-- Like `next`, but fail if the step does not apply. -/
def next? {n : Node} (r : Rw n) (f : (m : Node) → Option (Rw m)) : Option (Rw n) :=
  (f r.1).map fun ⟨k, h⟩ => ⟨k, r.2.trans h⟩

/-- Rewrite child `i` of `n` by `f`, when `n` is an application whose operator is
congruent in its children, and all its children are well typed. -/
def congrArg (n : Node) (i : Nat) (f : (c : Node) → Option (Rw c)) : Option (Rw n) :=
  match n with
  | .app op cs =>
    if hi : i < cs.size then
      if hop : op.eoShape.isChildCongruent = true then
        if hwt : op.childrenTypedOfParent = true ∨ Profile.time "types"
            (fun _ => "congrArg: children well typed") (fun _ => decide (∀ c ∈ cs.toList, c.WellTyped)) = true then
          (f cs[i]).map fun ⟨c', hc⟩ =>
            ⟨.app op (cs.set i c'), .congrArg i c' hi hop (hwt.imp (fun h => h) of_decide_eq_true) hc (.refl _)⟩
        else none
      else none
    else none
  | _ => none

end Rw

/-- What a pattern variable is bound to. -/
inductive Binding where
  | node (n : Node)
  /-- A run of children of an n-ary application of kind `k`. `seed` is the first
  child of that application, from which a typed nil (`+`, `*`) is computed when
  the run is empty. -/
  | list (k : Kind) (elems : List Node) (seed : Option Node := none)
  deriving BEq, Inhabited

/-- A partial assignment of pattern variables. -/
abbrev Subst := Array (Option Binding)

/-- Whether two bindings are the same run of children or node. The seed of a
list only gives the type of its nil, so it is not compared: the first binding
is kept, and a nil of the wrong type would be rejected by the checker. -/
def Binding.same : Binding → Binding → Bool
  | .list k es _, .list k' es' _ => k == k' && es == es'
  | b, b' => b == b'

/-- Bind variable `i` to `b`, or check that it is already bound to `b`. -/
def Subst.bind (σ : Subst) (i : Nat) (b : Binding) : List Subst :=
  match σ[i]? with
  | some none => [σ.set! i (some b)]
  | some (some b') => if b'.same b then [σ] else []
  | none => []

mutual

/-- All extensions of `σ` under which `p` matches `n`. -/
partial def matchPat (σ : Subst) : Pat → Node → List Subst
  | .var i, n => σ.bind i (.node n)
  | .listVar _, _ => []
  | .const c, n => if n == .const c then [σ] else []
  | .app k ps, .app (.kind k') cs => if k == k' then matchList k cs[0]? σ ps cs.toList else []
  | .app _ _, _ => []
  | .indexed k ips ps, .app (.indexed k' is) cs =>
    if k == k' then
      (matchList k none σ ips (is.toList.map fun i => .const (.integer i))).flatMap fun σ' =>
        matchList k cs[0]? σ' ps cs.toList
    else []
  | .indexed .., _ => []
  | .bvLit vp wp, .const (.bitVector w v) =>
    (matchPat σ wp (.const (.integer w))).flatMap fun σ' => matchPat σ' vp (.const (.integer v))
  | .bvLit .., _ => []

/-- All extensions of `σ` under which the patterns `ps` match the children `cs`
of an application of kind `k`. A list variable takes any run of children. -/
partial def matchList (k : Kind) (seed : Option Node) (σ : Subst) :
    List Pat → List Node → List Subst
  | [], [] => [σ]
  | .listVar i :: ps, cs =>
      (List.range (cs.length + 1)).flatMap fun j =>
        (σ.bind i (.list k (cs.take j) seed)).flatMap fun σ' => matchList k seed σ' ps (cs.drop j)
  | p :: ps, c :: cs => (matchPat σ p c).flatMap fun σ' => matchList k seed σ' ps cs
  | _ :: _, [] | [], _ :: _ => []

end

/-- The Logos term a binding stands for. A run of children of an n-ary operator
is the `:list` term Eunoia binds: the right-nested tail ending in the nil. -/
def Binding.toEo : Binding → Option Term
  | .node n => some n.toEo
  | .list k elems seed =>
    match k.eoShape with
    | .rightAssocNil op nil =>
      let xs := elems.map Node.toEo
      let first := xs.head? <|> (seed.map Node.toEo)
      some (eoRightAssocNil op (nil.eval op (first.getD Term.Stuck)) xs)
    | _ => none

mutual

/-- The node a pattern stands for under a complete assignment. With `sym`, a
bit-vector literal pattern `(@bv v w)` stands for `((_ int_to_bv w) v)`, as the
signature defines `@bv`; otherwise for the literal. -/
partial def Pat.instantiate (σ : Subst) (p : Pat) (sym : Bool := false) : Option Node :=
  match p with
  | .var i => match σ[i]? with
    | some (some (.node n)) => some n
    | _ => none
  | .listVar _ => none
  | .const c => some (.const c)
  | .app k ps => do return .app (.kind k) (← Pat.instantiateList σ ps sym).toArray
  | .indexed k ips ps => do
    let is ← ips.mapM fun p => do
      match ← p.instantiate σ sym with
      | .const (.integer i) => some i
      | _ => none
    return .app (.indexed k is.toArray) (← Pat.instantiateList σ ps sym).toArray
  | .bvLit vp wp => do
    match ← vp.instantiate σ sym, ← wp.instantiate σ sym with
    | .const (.integer v), .const (.integer w) =>
      if sym then some (.app (.indexed .INT_TO_BITVECTOR #[w]) #[.const (.integer v)])
      else some (.const (.bitVector w v))
    -- A value that is a term, as in premises like `(@bv (- (@bvsize x) 1) w)`:
    -- `((_ int_to_bv w) e)`, which `evaluate` reduces.
    | e, .const (.integer w) => some (.app (.indexed .INT_TO_BITVECTOR #[w]) #[e])
    | _, _ => none

/-- The children a list of patterns stands for; list variables are spliced in. -/
partial def Pat.instantiateList (σ : Subst) (ps : List Pat) (sym : Bool := false) :
    Option (List Node) :=
  match ps with
  | [] => some []
  | .listVar i :: ps => do
    match σ[i]? with
    | some (some (.list _ elems _)) => return elems ++ (← Pat.instantiateList σ ps sym)
    | _ => none
  | p :: ps => do return (← p.instantiate σ sym) :: (← Pat.instantiateList σ ps sym)

end

/-- The value of `a`, as the `evaluate` step proving the premise computes it
(Logos's evaluator, run directly: this only decides whether the rule is tried;
the certificate still has the `evaluate` step). -/
def evalNode (a : Node) : Option Node :=
  Profile.time "strategy: premise evaluation" (fun _ => "") fun _ =>
    match __run_evaluate a.toEo with
    | .Stuck => none
    | v => Node.ofEo [] v

/-- A prover for premises that evaluation does not discharge: for a predicate
`p` and a Boolean constant `v`, the CPC commands proving `(= p v)` (their last
fact). It is used for premises `(= p true)` and `(= p false)`, and for premises
`(= a b)` between two terms, as `(= (= a b) true)` followed by `true_elim`. -/
abbrev PremiseProver := Node → Node → Option (List CCmd)

/-- The Boolean constant of a premise `(= p true)` or `(= p false)`. -/
def Premise.boolValue? (p : Premise) : Option Node :=
  if p.other.isSome || p.symm then none else
  match p.value with
  | .const (.boolean b) => some (.const (.boolean b))
  | _ => none

/-- The prover's proof of the premise, when evaluation does not give `true`. -/
def proverSteps (prove : Option PremiseProver) (σ : Subst) (p : Premise) (a : Node) :
    Option (List CCmd) :=
  match prove with
  | none => none
  | some f =>
    match p.boolValue? with
    | some v => if evalNode a == some v then none else f a v
    | none => match p.other with
      | some o => do
        let b ← o.instantiate σ (sym := true)
        if (evalNode a).isSome && evalNode a == evalNode b then none
        else return (← f (Node.mkNode .EQUAL #[a, b]) (.const (.boolean true))) ++
          [CCmd.step .true_elim .nil (.cons 0 .nil)]
      | none => none

/-- Extend `σ` by one premise: the value of its left-hand side must match its
right-hand side, or it is proven by `prove`. -/
def bindPremise (prove : Option PremiseProver) (σ : Subst) (p : Premise) : List Subst :=
  let a? := p.expr.instantiate σ (sym := true)
  let proven := a?.bind (proverSteps prove σ p) |>.isSome
  if proven then [σ] else
  match a? >>= evalNode with
  | some val =>
    match p.other with
    | some o =>
      match o.instantiate σ (sym := true) >>= evalNode with
      | some val' => if val == val' then [σ] else []
      | none => []
    | none => matchPat σ p.value val
  | none => []

/-- Extend `σ` by the premises, in order, except that a premise whose left-hand
side has variables that a later premise binds is taken after it (as in
`bv-ult-add-one`, whose `(= c (@bv 1 w))` comes before `(= w (@bvsize x))`):
the first premise whose left-hand side is instantiated is taken first. -/
partial def bindPremises (prove : Option PremiseProver) (σ : Subst) (ps : List Premise) :
    List Subst :=
  match ps with
  | [] => [σ]
  | p₀ :: rest =>
    match ps.findIdx? fun p => (p.expr.instantiate σ (sym := true)).isSome with
    | some i =>
      let p := ps[i]?.getD p₀
      (bindPremise prove σ p).flatMap fun σ' => bindPremises prove σ' (ps.eraseIdx i)
    | none => (bindPremise prove σ p₀).flatMap fun σ' => bindPremises prove σ' rest

/-- Whether a pattern has a bit-vector literal pattern `(@bv v w)`. -/
partial def Pat.hasBvLit : Pat → Bool
  | .bvLit .. => true
  | .app _ ps | .indexed _ _ ps => ps.any Pat.hasBvLit
  | _ => false

/-- Rewrite `n` to `target`, which is `n` with some bit-vector literals written
`((_ int_to_bv w) v)`: each by `evaluate` and `symm`, under congruence. -/
partial def toSymbolic (n target : Node) : Option (Rw n) :=
  if n == target then some (Rw.id n) else
  match target with
  | .app (.indexed .INT_TO_BITVECTOR _) #[_] =>
    if n.isConst then
      applyCmds (.cons (.step .evaluate (.cons target.toEo .nil) .nil)
        (.cons (.step .symm .nil (.cons 0 .nil)) .nil)) n
    else none
  | .app op' ds =>
    let cs := n.getChildren
    if n.getOperator? == some op' && cs.size == ds.size then
      (List.range cs.size).foldlM (init := Rw.id n) fun r i =>
        r.next? fun m => Rw.congrArg m i fun c => toSymbolic c ds[i]!
    else none
  | _ => none

/-- Whether a node has an `int_to_bv` application. -/
partial def hasIntToBv : Node → Bool
  | .app (.indexed .INT_TO_BITVECTOR _) _ => true
  | .app _ cs => cs.any hasIntToBv
  | _ => false

/-- The `int_to_bv` applications of `n` evaluated to literals, under
congruence: each maximal variable-free subterm that has one and evaluates to a
constant, such as `(bvnot ((_ int_to_bv 4) 0))`. Logos writes the `(@bv v w)` of
a rule's right-hand side this way; cvc5's rules produce the constant. -/
partial def foldIntToBv (n : Node) : Rw n :=
  let cs := n.getChildren
  let evaluated := if n.vars.isEmpty then
      (applyCmds (.cons (.step .evaluate (.cons n.toEo .nil) .nil) .nil) n).filter (·.1.isConst)
    else none
  if let some r := evaluated then r
  else
    (List.range cs.size).foldl (init := Rw.id n) fun r i =>
      r.next fun m => Rw.congrArg m i fun c =>
        if hasIntToBv c then
          let rc := foldIntToBv c
          if rc.1 == c then none else some rc
        else none

namespace RuleSpec

/-- Every match of the rule's left-hand side against `n`, with its premises. -/
def allMatches (r : RuleSpec) (n : Node) (prove : Option PremiseProver := none) : List Subst :=
  (matchPat (Array.replicate r.numVars none) r.lhs n).flatMap (bindPremises prove · r.premises)

/-- `[k-1, …, 1, 0]`: the positions of `k` premises proven by the last `k` steps,
the first premise being the oldest. -/
def premiseIndices (k : Nat) : CIndexList :=
  (List.range k).foldl (fun acc i => .cons (Int.ofNat i) acc) .nil

/-- The steps proving one premise: an `evaluate` step, then `symm` for a
premise written `(= value expr)`. -/
def premiseSteps (p : Premise) (a : Term) (b : Option Term) : List CCmd :=
  match b with
  | some b =>
    -- `(= a v)`, `(= b v)`, `(= v b)`, then `(= a b)`.
    [CCmd.step .evaluate (.cons a .nil) .nil, CCmd.step .evaluate (.cons b .nil) .nil,
      CCmd.step .symm .nil (.cons 0 .nil), CCmd.step .trans .nil (.cons 2 (.cons 0 .nil))]
  | none =>
    [CCmd.step .evaluate (.cons a .nil) .nil] ++
      (if p.symm then [CCmd.step .symm .nil (.cons 0 .nil)] else [])

/-- The CPC command list for applying the rule under the assignment `σ`. -/
def cmds (r : RuleSpec) (σ : Subst) (prove : Option PremiseProver := none) : Option CCmdList := do
  let vargs ← r.args.mapM fun i => do (← σ[i]?.join).toEo
  let targs ← r.typeArgs.mapM fun (p, i) => do return (p, __eo_typeof (← (← σ[i]?.join).toEo))
  let args := targs.foldl (fun acc (p, t) => acc.take p ++ [t] ++ acc.drop p) vargs
  -- Premises are written as the rule writes them: `(@bv v w)` as `((_ int_to_bv w) v)`.
  let prems ← r.premises.mapM fun p => do
    let b : Option Term ← match p.other with
      | some o => (o.instantiate σ (sym := true)).map fun n => some n.toEo
      | none => some none
    let a ← p.expr.instantiate σ (sym := true)
    match proverSteps prove σ p a with
    | some steps => return steps
    | none => return premiseSteps p a.toEo b
  let steps := prems.flatten
  -- The position of the last step of each premise, and its offset from the rule.
  let ends := (prems.scanl (fun n s => n + s.length) 0).tail
  let indices := ends.foldr (fun e acc => .cons (Int.ofNat (steps.length - e)) acc) .nil
  let ruleStep := CCmd.step r.rule (toArgList args) indices
  return (steps ++ [ruleStep]).foldr .cons .nil

/-- The step under the assignment `σ` by a template rule (`TRule`), taken
statically (`StaticProc.template`), without running Logos's checker: for rules
without premises or type arguments. -/
def staticStep (r : RuleSpec) (n : Node) (σ : Subst) : Option (Rw n) := do
  if !r.premises.isEmpty || !r.typeArgs.isEmpty || r.lhs.hasBvLit then none
  let tr ← TRule.ofRule r.rule
  let args ← r.args.mapM fun i => match (σ[i]? : Option (Option Binding)) with
    | some (some (Binding.node c)) => some c
    | _ => none
  let m ← tr.rhs args
  if h : Profile.time "static: side conditions" (fun _ => r.name)
      (fun _ => decide (tr.Ok args n m)) = true then
    some ⟨m, .static (.template tr args false) (show tr.Ok args n m from of_decide_eq_true h) (.refl m)⟩
  else none

/-- `apply`, before folding `int_to_bv` applications. -/
def applyRaw (r : RuleSpec) (n : Node) (prove : Option PremiseProver := none) : Option (Rw n) :=
  Profile.time "strategy: RARE matching" (fun _ => r.name) (fun _ => r.allMatches n prove) |>.findSome? fun σ =>
    (r.staticStep n σ).orElse fun _ => r.cmds σ prove >>= fun cs =>
      if r.lhs.hasBvLit then
        -- The rule's left-hand side has `(@bv v w)`, which is `((_ int_to_bv w) v)`:
        -- write the matched literals that way first.
        r.lhs.instantiate σ (sym := true) >>= fun n' =>
          toSymbolic n n' >>= fun rw => rw.next? (applyCmds cs)
      else applyCmds cs n

/-- Apply the rule to `n`: the first match whose command list Logos's checker
accepts. -/
def apply (r : RuleSpec) (n : Node) (prove : Option PremiseProver := none) : Option (Rw n) :=
  (r.applyRaw n prove).map fun rw => rw.next fun m => if hasIntToBv m then some (foldIntToBv m) else none

end RuleSpec

end Telos
