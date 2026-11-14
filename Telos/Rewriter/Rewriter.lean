import Telos.Rewriter.Certified

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
* Recursion instead of cvc5's explicit stack, and no rewrite cache yet.
* Children are rewritten only when each is well typed, a runtime check that
  stands in, for now, for a proof that the children of a well-typed node are well
  typed. Under a quantifier only the body is rewritten.
* A `RewriteResponse n` carries a certificate that its node is CPC-provably equal
  to `n` (`Certified`). Theory rewriters therefore cannot return an unjustified
  result, and need no proof of their own. The driver chains these certificates
  (`Rw`), so its result is certified too, and can be printed as a CPC proof.

Correctness is `Telos.rewrite_correct` in `verification/TelosProofs/Rewriter.lean`.
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

/-- Rewrite the children of a node with `f`. -/
def rewriteChildren (f : (c : Node) → Rw c) (n : Node) : Rw n :=
  match n with
  | .app op cs =>
    if hop : op.eoShape.isChildCongruent then
      if hc : op.childrenTypedOfParent = true then Rw.congr op cs f hop (Or.inl hc)
      else if hwt : Profile.time "types" (fun _ => "driver: children well typed")
          (fun _ => decide (∀ c ∈ cs.toList, c.WellTyped)) = true then
        Rw.congr op cs f hop (Or.inr (of_decide_eq_true hwt))
      else .id _
    else
      match op, cs with
      | .kind k, ⟨vs :: body :: pats⟩ =>
        if hq : Profile.time "types" (fun _ => "driver: quantifier body well typed")
            (fun _ => decide (k.isQuantifier = true ∧ body.WellTyped)) = true then
          let b := f body
          have hq := of_decide_eq_true hq
          ⟨.app (.kind k) ⟨vs :: b.1 :: pats⟩, .congrBody hq.1 hq.2 b.2 (.refl _)⟩
        else .id _
      | _, _ => .id _
  | _ => .id _

/-- Post-rewrite at the top. `full` rewrites a node from the start, for
`REWRITE_AGAIN_FULL` and for results that belong to another theory. -/
def postRewriteLoop (R : TheoryId → TheoryRewriter) (full : (n : Node) → Rw n) :
    Nat → (n : Node) → Rw n
  | 0, n => .id n
  | fuel + 1, n =>
    let tid := theoryOf n
    let r := (R tid).postRewrite n
    match r.status with
    | .REWRITE_DONE =>
      if theoryOf r.node == tid then r.toRw else r.toRw.trans (full r.node)
    | .REWRITE_AGAIN =>
      if theoryOf r.node == tid then r.toRw.trans (postRewriteLoop R full fuel r.node)
      else r.toRw.trans (full r.node)
    | .REWRITE_AGAIN_FULL => r.toRw.trans (full r.node)

/-- cvc5's `Rewriter::rewriteTo`, with the given theory rewriters and fuel. The
result is certified, so it is correct by construction (`Certified.equiv`). -/
def rewriteWith (R : TheoryId → TheoryRewriter) : Nat → (n : Node) → Rw n
  | 0, n => .id n
  | fuel + 1, n =>
    let full := fun m => rewriteWith R fuel m
    let pre := preRewriteLoop R fuel n
    let mid := rewriteChildren full pre.1
    pre.trans (mid.trans (postRewriteLoop R full fuel mid.1))

end Telos
