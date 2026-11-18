import Std.Data.HashMap
import Telos.Core.Certified

/-!
# Rewriter

Modelled on cvc5's `Rewriter` (`src/theory/rewriter.cpp`) and `TheoryRewriter`
(`src/theory/theory_rewriter.h`). Each theory supplies `preRewrite` and
`postRewrite`, which return a `RewriteResponse`. The driver, `rewriteWith`, does
what cvc5's `Rewriter::rewriteTo` does:

1. pre-rewrite the node with the rewriter of its theory (`theoryOf`), until it is
   `REWRITE_DONE` and stays in the same theory;
2. rewrite its children;
3. post-rewrite it, again with the rewriter of its theory. On `REWRITE_AGAIN` it
   post-rewrites again; on `REWRITE_AGAIN_FULL`, or when the result belongs to
   another theory, it rewrites the result from step 1.

Differences from cvc5:

* The driver takes **fuel** and returns its input when the fuel runs out. That is
  sound, since the identity is an equivalence, and it avoids `partial def`, which
  proofs cannot see through. Fuel bounds the recursion depth, not the work.
* Recursion instead of cvc5's explicit stack. The rewrite cache (`Cache`) lasts
  for one call of `rewriteWith`, where cvc5's lasts for the whole run.
* Children are rewritten only when each is well typed: for the kinds of
  `Op.childrenTypedOfParent` this is proved (`ChildTyping.children_wellTyped`),
  and for the others it is checked at run time. Under a quantifier only the body
  is rewritten.
* A `RewriteResponse n` carries a certificate that its node is CPC-provably equal
  to `n` (`Certified`). Theory rewriters therefore cannot return an unjustified
  result, and need no proof of their own. The driver chains these certificates
  (`Rw`), so its result is certified too, and can be printed as a CPC proof.

Correctness is `Telos.rewrite_correct` in `verification/TelosProofs/Rewriter/Rewriter.lean`.
-/

namespace Telos

/-- cvc5's `RewriteStatus`. -/
inductive RewriteStatus where
  /-- The node is in normal form for this theory. -/
  | REWRITE_DONE
  /-- Rewrite the result again at the top level. -/
  | REWRITE_AGAIN
  /-- Rewrite the result again, including its children. -/
  | REWRITE_AGAIN_FULL
  deriving DecidableEq, Repr, Inhabited

/-- cvc5's `RewriteResponse`, for a rewrite of `n`. It also carries a
certificate that `n` rewrites to `node` by CPC-checked steps. -/
structure RewriteResponse (n : Node) where
  status : RewriteStatus
  node : Node
  cert : Certified n node

/-- `n` is in normal form. -/
def RewriteResponse.done (n : Node) : RewriteResponse n :=
  ⟨.REWRITE_DONE, n, .refl n⟩

/-- cvc5's `TheoryRewriter` interface. -/
structure TheoryRewriter where
  preRewrite : (n : Node) → RewriteResponse n
  postRewrite : (n : Node) → RewriteResponse n

namespace TheoryRewriter

/-- A theory rewriter that leaves every node unchanged. -/
def trivial : TheoryRewriter where
  preRewrite := .done
  postRewrite := .done

end TheoryRewriter

/-- cvc5's `Theory::theoryOf` in its default, type-based mode: a variable belongs
to the theory of its type, an equality to the theory of the type of its
arguments, and anything else to the theory of its kind. -/
def theoryOf : Node → TheoryId
  | .var _ T | .boundVar _ T => T.theoryId
  -- A skolem is a variable in cvc5.
  | n@(.skolem ..) => ((n.typeHint).map TypeNode.theoryId).getD .THEORY_BUILTIN
  | n@(.app (.kind .EQUAL) cs) =>
      match Profile.time "types" (fun _ => "theoryOf: type of equality") fun _ => cs[0]?.bind Node.typeHint with
      | some T => T.theoryId
      | none => n.getKind.theoryId
  | n => n.getKind.theoryId

/-- The response as a certified rewrite. -/
def RewriteResponse.toRw {n : Node} (r : RewriteResponse n) : Rw n := ⟨r.node, r.cert⟩

/-- Pre-rewrite at the top, until the node is done and stays in its theory. -/
def preRewriteLoop (R : TheoryId → TheoryRewriter) : Nat → (n : Node) → Rw n
  | 0, n => .id n
  | fuel + 1, n =>
    let r := (R (theoryOf n)).preRewrite n
    match r.status with
    | .REWRITE_DONE =>
      if theoryOf r.node == theoryOf n then r.toRw
      else r.toRw.trans (preRewriteLoop R fuel r.node)
    | _ => r.toRw.trans (preRewriteLoop R fuel r.node)

/-- The rewrite cache: the rewrite of each node rewritten so far, as cvc5's
rewriter caches the result of `rewriteTo`. -/
abbrev Cache := Std.HashMap Node ((n : Node) × Rw n)

/-- The rewriter's monad: a computation with the rewrite cache. -/
abbrev RwM := StateM Cache

/-- The cached rewrite of `n`, if any. -/
def Cache.find (c : Cache) (n : Node) : Option (Rw n) :=
  match c.get? n with
  | some ⟨n', r⟩ => if h : n' = n then some (h ▸ r) else none
  | none => none

/-- The rewrites of `cs` by `f`, in order. -/
def mapChildren (f : (c : Node) → RwM (Rw c)) :
    (cs : List Node) → RwM {rs : List ((c : Node) × Rw c) // rs.map (·.1) = cs}
  | [] => return ⟨[], rfl⟩
  | c :: cs => do
    let r ← f c
    let ⟨rs, h⟩ ← mapChildren f cs
    return ⟨⟨c, r⟩ :: rs, by simp [h]⟩

/-- Rewrite the children of a node with `f`. -/
def rewriteChildren (f : (c : Node) → RwM (Rw c)) (n : Node) : RwM (Rw n) :=
  match n with
  | .app op cs =>
    if hop : op.eoShape.isChildCongruent then
      let typed := op.childrenTypedOfParent = true ∨ Profile.time "types"
        (fun _ => "driver: children well typed") (fun _ => decide (∀ c ∈ cs.toList, c.WellTyped)) = true
      if hwt : typed then do
        let ⟨rs, hrs⟩ ← mapChildren f cs.toList
        let hwt' : op.childrenTypedOfParent = true ∨ ∀ c ∈ cs.toList, c.WellTyped :=
          hwt.imp (fun h => h) of_decide_eq_true
        return Rw.congrList op cs rs hrs hop hwt'
      else return .id _
    else
      match op, cs with
      | .kind k, ⟨vs :: body :: pats⟩ =>
        if hq : Profile.time "types" (fun _ => "driver: quantifier body well typed")
            (fun _ => decide (k.isQuantifier = true ∧ body.WellTyped)) = true then do
          let b ← f body
          have hq := of_decide_eq_true hq
          return ⟨.app (.kind k) ⟨vs :: b.1 :: pats⟩, .congrBody hq.1 hq.2 b.2 (.refl _)⟩
        else return .id _
      | _, _ => return .id _
  | _ => return .id _

/-- Post-rewrite at the top. `full` rewrites a node from the start, for
`REWRITE_AGAIN_FULL` and for results that belong to another theory. -/
def postRewriteLoop (R : TheoryId → TheoryRewriter) (full : (n : Node) → RwM (Rw n)) :
    Nat → (n : Node) → RwM (Rw n)
  | 0, n => return .id n
  | fuel + 1, n => do
    let tid := theoryOf n
    let r := (R tid).postRewrite n
    match r.status with
    | .REWRITE_DONE =>
      if theoryOf r.node == tid then return r.toRw else return r.toRw.trans (← full r.node)
    | .REWRITE_AGAIN =>
      if theoryOf r.node == tid then return r.toRw.trans (← postRewriteLoop R full fuel r.node)
      else return r.toRw.trans (← full r.node)
    | .REWRITE_AGAIN_FULL => return r.toRw.trans (← full r.node)

/-- cvc5's `Rewriter::rewriteTo`, with the given theory rewriters and fuel, and
the rewrite cache. -/
def rewriteWithM (R : TheoryId → TheoryRewriter) : Nat → (n : Node) → RwM (Rw n)
  | 0, n => return .id n
  | fuel + 1, n => do
    if let some r := (← get).find n then return r
    let full := fun m => rewriteWithM R fuel m
    let pre := preRewriteLoop R fuel n
    let mid ← rewriteChildren full pre.1
    let post ← postRewriteLoop R full fuel mid.1
    let r := pre.trans (mid.trans post)
    modify (·.insert n ⟨n, r⟩)
    return r

/-- cvc5's `Rewriter::rewriteTo`, with the given theory rewriters and fuel. The
result is certified, so it is correct by construction (`Certified.equiv`). -/
def rewriteWith (R : TheoryId → TheoryRewriter) (fuel : Nat) (n : Node) : Rw n :=
  (rewriteWithM R fuel n).run' {}

end Telos
