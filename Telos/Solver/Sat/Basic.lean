/-!
# SAT solver basics

The types of MiniSat (`src/prop/minisat/core/SolverTypes.h`, `mtl/`), as cvc5
uses them: variables, literals, three-valued values, and MiniSat's own sort and
heap, whose orders the search follows.

The SAT layer (`Telos/Solver/Sat/`) knows nothing of telos's terms: it is the
part of the engine that a verified CDCL(T) solver will replace
(`docs/theory-engine-plan.md`, Stage 6).
-/

namespace Telos.Sat

/-- A variable: its index. -/
abbrev Var := Nat

/-- A literal, as MiniSat encodes it: `2 * var + sign`, the sign `1` for the
negation. -/
structure Lit where
  ofNat ::
  x : Nat
  deriving BEq, Hashable, Inhabited, Repr, DecidableEq

namespace Lit

/-- `lit_Undef`. -/
def undef : Lit := ⟨1 <<< 62⟩

def mk (v : Var) (sign : Bool := false) : Lit := ⟨2 * v + (if sign then 1 else 0)⟩

def var (p : Lit) : Var := p.x / 2

def sign (p : Lit) : Bool := p.x % 2 == 1

/-- `~p`. -/
def neg (p : Lit) : Lit := ⟨p.x ^^^ 1⟩

instance : LT Lit := ⟨fun a b => a.x < b.x⟩
instance (a b : Lit) : Decidable (a < b) := inferInstanceAs (Decidable (a.x < b.x))

end Lit

/-- `lbool`: true, false or undefined. -/
inductive LBool where
  | tt
  | ff
  | undef
  deriving BEq, Inhabited, Repr, DecidableEq

namespace LBool

def ofBool (b : Bool) : LBool := if b then .tt else .ff

/-- `v ^ sign`. -/
def xor (v : LBool) (sign : Bool) : LBool :=
  match v, sign with
  | .tt, true => .ff
  | .ff, true => .tt
  | v, _ => v

end LBool

/-- `selectionSort`, as MiniSat's (`mtl/Sort.h`). -/
def selectionSort {α : Type} [Inhabited α] (lt : α → α → Bool) (a : Array α) (lo n : Nat) :
    Array α := Id.run do
  let mut a := a
  for i in [0:n - 1] do
    let mut best := i
    for j in [i + 1:n] do
      if lt a[lo + j]! a[lo + best]! then best := j
    let tmp := a[lo + i]!
    a := (a.set! (lo + i) a[lo + best]!).set! (lo + best) tmp
  return a

/-- MiniSat's `sort` (`mtl/Sort.h`): selection sort up to 15 elements, else a
quicksort on the middle element. The order of equal elements is MiniSat's. -/
partial def sortRange {α : Type} [Inhabited α] (lt : α → α → Bool) (a : Array α) (lo n : Nat) :
    Array α :=
  if n ≤ 15 then selectionSort lt a lo n
  else Id.run do
    let pivot := a[lo + n / 2]!
    let mut a := a
    let mut i : Int := -1
    let mut j : Int := n
    repeat
      i := i + 1
      while lt a[lo + i.toNat]! pivot do i := i + 1
      j := j - 1
      while lt pivot a[lo + j.toNat]! do j := j - 1
      if i ≥ j then break
      let tmp := a[lo + i.toNat]!
      a := (a.set! (lo + i.toNat) a[lo + j.toNat]!).set! (lo + j.toNat) tmp
    let a' := sortRange lt a lo i.toNat
    return sortRange lt a' (lo + i.toNat) (n - i.toNat)

def sort {α : Type} [Inhabited α] (lt : α → α → Bool) (a : Array α) : Array α :=
  sortRange lt a 0 a.size

/-- MiniSat's binary heap of variables (`mtl/Heap.h`), a minimum-heap for `lt`. -/
structure Heap where
  heap : Array Nat := #[]
  /-- The position of each variable in `heap`, `-1` if it is not there. -/
  indices : Array Int := #[]
  deriving Inhabited

namespace Heap

def left (i : Nat) : Nat := 2 * i + 1
def right (i : Nat) : Nat := 2 * (i + 1)
def parent (i : Nat) : Nat := (i - 1) / 2

def size (h : Heap) : Nat := h.heap.size
def empty (h : Heap) : Bool := h.heap.isEmpty

def inHeap (h : Heap) (n : Nat) : Bool := n < h.indices.size && h.indices[n]! ≥ 0

partial def percolateUp (lt : Nat → Nat → Bool) (h : Heap) (i : Nat) : Heap := Id.run do
  let x := h.heap[i]!
  let mut heap := h.heap
  let mut indices := h.indices
  let mut i := i
  let mut p := parent i
  while i != 0 && lt x heap[p]! do
    heap := heap.set! i heap[p]!
    indices := indices.set! heap[p]! i
    i := p
    p := parent p
  heap := heap.set! i x
  indices := indices.set! x i
  return { heap, indices }

partial def percolateDown (lt : Nat → Nat → Bool) (h : Heap) (i : Nat) : Heap := Id.run do
  let x := h.heap[i]!
  let mut heap := h.heap
  let mut indices := h.indices
  let mut i := i
  while left i < heap.size do
    let child := if right i < heap.size && lt heap[right i]! heap[left i]! then right i else left i
    if !lt heap[child]! x then break
    heap := heap.set! i heap[child]!
    indices := indices.set! heap[i]! i
    i := child
  heap := heap.set! i x
  indices := indices.set! x i
  return { heap, indices }

def decrease (lt : Nat → Nat → Bool) (h : Heap) (n : Nat) : Heap :=
  percolateUp lt h h.indices[n]!.toNat

def insert (lt : Nat → Nat → Bool) (h : Heap) (n : Nat) : Heap :=
  let indices := if h.indices.size < n + 1 then
      h.indices ++ Array.replicate (n + 1 - h.indices.size) (-1) else h.indices
  let indices := indices.set! n h.heap.size
  let heap := h.heap.push n
  percolateUp lt { heap, indices } (heap.size - 1)

def removeMin (lt : Nat → Nat → Bool) (h : Heap) : Nat × Heap :=
  let x := h.heap[0]!
  let last := h.heap.back!
  let heap := h.heap.set! 0 last
  let indices := (h.indices.set! last 0).set! x (-1)
  let heap := heap.pop
  let h' : Heap := { heap, indices }
  (x, if heap.size > 1 then percolateDown lt h' 0 else h')

def build (lt : Nat → Nat → Bool) (h : Heap) (ns : Array Nat) : Heap := Id.run do
  let mut indices := h.indices
  for v in h.heap do indices := indices.set! v (-1)
  let mut heap : Array Nat := #[]
  for i in [0:ns.size] do
    indices := indices.set! ns[i]! i
    heap := heap.push ns[i]!
  let mut h : Heap := { heap, indices }
  let mut i : Int := heap.size / 2 - 1
  while i ≥ 0 do
    h := percolateDown lt h i.toNat
    i := i - 1
  return h

end Heap

end Telos.Sat
