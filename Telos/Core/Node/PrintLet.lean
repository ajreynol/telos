import Std.Data.HashMap
import Telos.Core.Node.Print
import Telos.Core.Node.Key

/-!
# Printing with `let`

cvc5's default printing (`--dag-thresh=1`, `src/printer/let_binding.cpp`): a
subterm with children that is referenced at least twice is bound by a `let`,
named `_let_1`, `_let_2`, … in post-order (a binding's value refers only to the
earlier ones), one binding per `let`, around the whole term. Binders are not
entered: the body of a quantifier is printed in a scope of its own, numbered
from `_let_1` again, as cvc5 does. So a term is printed in time linear in its
size as a DAG, not as a tree.
-/

namespace Telos

namespace Node

/-- Whether `n` binds variables: its first child is a variable list. -/
def isBinder : Node → Bool
  | .app _ cs => match cs[0]? with
    | some (Node.app (.kind .BOUND_VAR_LIST) _) => true
    | _ => false
  | _ => false

/-- The subterms the let printer counts and binds below `n`: none for binders
(printed in their own scope) and tuples (printed flat), the children
otherwise. -/
def letChildren : Node → Array Node
  | n@(.app op cs) => if n.isBinder || op.getKind == .TUPLE then #[] else cs
  | _ => #[]

/-- The subterms of `n` to bind, in post-order (as cvc5's `LetBinding`): those
with children referenced at least twice. Iterative, so deep terms do not
overflow the stack. -/
def letBound (n : Node) : Array Node := Id.run do
  let mut count : Std.HashMap Key Nat := {}
  let mut post : Array Node := #[]
  -- `(node, true)` marks the end of the node's visit
  let mut stack : Array (Node × Bool) := #[(n, false)]
  while 0 < stack.size do
    let (cur, done) := stack.back!
    stack := stack.pop
    if done then
      post := post.push cur
      continue
    match count.get? ⟨cur⟩ with
    | some c => count := count.insert ⟨cur⟩ (c + 1)
    | none =>
      count := count.insert ⟨cur⟩ 1
      stack := stack.push (cur, true)
      -- in order, so visited last to first, as cvc5 does
      for c in cur.letChildren do
        stack := stack.push (c, false)
  return post.filter fun c =>
    !c.getChildren.isEmpty && (count.getD ⟨c⟩ 0) ≥ 2

mutual

/-- `n` in SMT-LIB syntax with its shared subterms bound by `let`. -/
partial def toSmtLibLet (N : DtNames) (n : Node) : String := Id.run do
  let bound := letBound n
  let mut names : Std.HashMap Key String := {}
  let mut binds : Array (String × String) := #[]
  for h : i in [0:bound.size] do
    let c := bound[i]
    let v := letTop N names c
    let x := s!"_let_{i + 1}"
    names := names.insert ⟨c⟩ x
    binds := binds.push (x, v)
  let body := letSub N names n
  let opens := binds.foldl (fun s (x, v) => s ++ s!"(let (({x} {v})) ") ""
  return opens ++ body ++ "".pushn ')' binds.size

/-- A subterm: its name, if it is bound, or else printed. -/
partial def letSub (N : DtNames) (names : Std.HashMap Key String) (c : Node) : String :=
  match names.get? ⟨c⟩ with
  | some x => x
  | none => letTop N names c

/-- The top of a node, its subterms by `letSub`, and the bodies of binders in
their own scope. -/
partial def letTop (N : DtNames) (names : Std.HashMap Key String) (c : Node) : String :=
  if c.isBinder then
    c.toSmtLibTop N fun d =>
      if d.getKind == .BOUND_VAR_LIST then d.toSmtLibWith N else toSmtLibLet N d
  else c.toSmtLibTop N (letSub N names)

end

end Node

end Telos
