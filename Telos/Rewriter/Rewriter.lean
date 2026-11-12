import Telos.Node.ToEo
import Telos.Node.DecEq

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

/-- cvc5's `RewriteResponse`. -/
structure RewriteResponse where
  status : RewriteStatus
  node : Node
  deriving Inhabited

/-- cvc5's `TheoryRewriter` interface. -/
structure TheoryRewriter where
  preRewrite : Node → RewriteResponse
  postRewrite : Node → RewriteResponse

namespace TheoryRewriter

/-- A theory rewriter that leaves every node unchanged. -/
def trivial : TheoryRewriter where
  preRewrite n := ⟨.REWRITE_DONE, n⟩
  postRewrite n := ⟨.REWRITE_DONE, n⟩

end TheoryRewriter

/-- cvc5's `Theory::theoryOf` in its default, type-based mode: a variable belongs
to the theory of its type, an equality to the theory of the type of its
arguments, and anything else to the theory of its kind. -/
def theoryOf : Node → TheoryId
  | .var _ T | .boundVar _ T => T.theoryId
  | n@(.app (.kind .EQUAL) cs) =>
      match cs[0]?.bind Node.getType with
      | some T => T.theoryId
      | none => n.getKind.theoryId
  | n => n.getKind.theoryId

/-- The rewriter of each theory. None is implemented yet. -/
def theoryRewriter : TheoryId → TheoryRewriter
  | _ => .trivial

/-- Pre-rewrite at the top, until the node is done and stays in its theory. -/
def preRewriteLoop (R : TheoryId → TheoryRewriter) : Nat → Node → Node
  | 0, n => n
  | fuel + 1, n =>
    let r := (R (theoryOf n)).preRewrite n
    match r.status with
    | .REWRITE_DONE =>
      if theoryOf r.node == theoryOf n then r.node else preRewriteLoop R fuel r.node
    | _ => preRewriteLoop R fuel r.node

/-- Rewrite the children of a node with `f`. -/
def rewriteChildren (f : Node → Node) (n : Node) : Node :=
  match n with
  | .app op cs =>
    if op.eoShape.isChildCongruent then
      if cs.all (fun c => decide c.WellTyped) then .app op (cs.map f) else n
    else
      match op, cs with
      | .kind k, ⟨vs :: body :: pats⟩ =>
        if k.isQuantifier && decide body.WellTyped then
          .app (.kind k) ⟨vs :: f body :: pats⟩
        else n
      | _, _ => n
  | _ => n

/-- Post-rewrite at the top. `full` rewrites a node from the start, for
`REWRITE_AGAIN_FULL` and for results that belong to another theory. -/
def postRewriteLoop (R : TheoryId → TheoryRewriter) (full : Node → Node) : Nat → Node → Node
  | 0, n => n
  | fuel + 1, n =>
    let tid := theoryOf n
    let r := (R tid).postRewrite n
    match r.status with
    | .REWRITE_DONE => if theoryOf r.node == tid then r.node else full r.node
    | .REWRITE_AGAIN =>
      if theoryOf r.node == tid then postRewriteLoop R full fuel r.node else full r.node
    | .REWRITE_AGAIN_FULL => full r.node

/-- cvc5's `Rewriter::rewriteTo`, with the given theory rewriters and fuel. -/
def rewriteWith (R : TheoryId → TheoryRewriter) : Nat → Node → Node
  | 0, n => n
  | fuel + 1, n =>
    let full := fun m => rewriteWith R fuel m
    postRewriteLoop R full fuel (rewriteChildren full (preRewriteLoop R fuel n))

/-- The fuel `rewrite` uses. It bounds the recursion depth of the driver. -/
def defaultFuel : Nat := 10000

/-- cvc5's `Rewriter::rewrite`: rewrite a node to its normal form. -/
def rewrite (t : Node) : Node := rewriteWith theoryRewriter defaultFuel t

end Telos
