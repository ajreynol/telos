import Telos.Solver.Sat.Basic
open Telos.Sat
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648
-- random inserts, decreases and removals against a reference
def check (seed : Nat) : Bool := Id.run do
  let mut s := seed
  let mut act : Array Nat := Array.replicate 40 0
  let mut h : Heap := {}
  let mut inh : Array Bool := Array.replicate 40 false
  for _ in [0:400] do
    s := lcg s
    let v := s % 40
    s := lcg s
    let op := s % 3
    let lt := fun (x y : Nat) => decide (act[x]! > act[y]!)
    if op == 0 then
      if !h.inHeap v then
        h := h.insert lt v
        inh := inh.set! v true
    else if op == 1 then
      act := act.set! v (act[v]! + s % 7)
      let lt := fun (x y : Nat) => decide (act[x]! > act[y]!)
      if h.inHeap v then h := h.decrease lt v
    else if !h.empty then
      let (x, h') := h.removeMin lt
      h := h'
      -- x must have the maximal activity among those in the heap
      for y in [0:40] do
        if inh[y]! && y != x && act[y]! > act[x]! then return false
      inh := inh.set! x false
  return true
#guard (List.range 50).all check
