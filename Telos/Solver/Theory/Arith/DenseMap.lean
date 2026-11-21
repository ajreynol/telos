/-!
# Dense maps

cvc5's `DenseMap`, `DenseSet` and `DenseMultiset` (`src/util/dense_map.h`):
maps from small natural numbers (arith variables, row indices) with a list of
the keys. The arithmetic solver iterates over the keys in the list's order,
which `remove` changes (it swaps the key with the last one), so the port
keeps that order exactly.
-/

namespace Telos.Solver.Arith

/-- A map from small naturals to `α`, with its keys in a list. -/
structure DenseMap (α : Type) [Inhabited α] where
  /-- The keys (`d_list`). -/
  list : Array Nat := #[]
  /-- The position of each key in `list`, if it is one (`d_posVector`). -/
  pos : Array (Option Nat) := #[]
  /-- The values (`d_image`). -/
  image : Array α := #[]
  deriving Inhabited

namespace DenseMap

variable {α : Type} [Inhabited α]

def size (m : DenseMap α) : Nat := m.list.size
def isEmpty (m : DenseMap α) : Bool := m.list.isEmpty

def isKey (m : DenseMap α) (x : Nat) : Bool :=
  match m.pos[x]? with
  | some (some _) => true
  | _ => false

/-- The value of `x` (the default value if `x` is not a key, as cvc5's image
holds `T()` there). -/
def get (m : DenseMap α) (x : Nat) : α := m.image[x]?.getD default

def get? (m : DenseMap α) (x : Nat) : Option α := if m.isKey x then some (m.get x) else none

/-- `increaseSize`: room for the key `x`. -/
private def grow (m : DenseMap α) (x : Nat) : DenseMap α :=
  if x < m.pos.size then m
  else { m with pos := m.pos ++ Array.replicate (x + 1 - m.pos.size) none,
                image := m.image ++ Array.replicate (x + 1 - m.image.size) default }

/-- `set`: a new key goes at the end of the list. -/
def set (m : DenseMap α) (x : Nat) (v : α) : DenseMap α :=
  let m := m.grow x
  let m := if m.isKey x then m
    else { m with pos := m.pos.set! x (some m.list.size), list := m.list.push x }
  { m with image := m.image.set! x v }

/-- Update the value of the key `x`. -/
def modify (m : DenseMap α) (x : Nat) (f : α → α) : DenseMap α :=
  { m with image := m.image.modify x f }

def back (m : DenseMap α) : Nat := m.list.back!

/-- `pop_back`: remove the last key. -/
def popBack (m : DenseMap α) : DenseMap α :=
  let k := m.back
  { m with pos := m.pos.set! k none, image := m.image.set! k default, list := m.list.pop }

/-- `swapToBack`. -/
private def swapToBack (m : DenseMap α) (x : Nat) : DenseMap α :=
  match m.pos[x]? with
  | some (some p) =>
    let atBack := m.back
    let last := m.list.size - 1
    let list := (m.list.set! p atBack).set! last x
    let pos := (m.pos.set! atBack (some p)).set! x (some last)
    { m with list, pos }
  | _ => m

/-- `remove`: the key `x` swaps places with the last key, and is removed. -/
def remove (m : DenseMap α) (x : Nat) : DenseMap α :=
  if m.isKey x then (m.swapToBack x).popBack else m

/-- `purge`: remove every key, from the last. -/
def purge (m : DenseMap α) : DenseMap α := Id.run do
  let mut m := m
  while !m.isEmpty do m := m.popBack
  return m

/-- The keys, in order. -/
def keys (m : DenseMap α) : Array Nat := m.list

end DenseMap

/-- `DenseSet`. -/
abbrev DenseSet := DenseMap Bool

namespace DenseSet
def isMember (s : DenseSet) (x : Nat) : Bool := s.isKey x
def add (s : DenseSet) (x : Nat) : DenseSet := s.set x true
end DenseSet

/-- `DenseMultiset`. -/
abbrev DenseMultiset := DenseMap Nat

namespace DenseMultiset
def count (s : DenseMultiset) (x : Nat) : Nat := if s.isKey x then s.get x else 0
def add (s : DenseMultiset) (x : Nat) (c : Nat := 1) : DenseMultiset := s.set x (s.count x + c)
def removeAll (s : DenseMultiset) (x : Nat) : DenseMultiset := s.remove x
def removeOne (s : DenseMultiset) (x : Nat) : DenseMultiset :=
  match s.count x with
  | 0 => s
  | 1 => s.removeAll x
  | c => s.set x (c - 1)
end DenseMultiset

end Telos.Solver.Arith
