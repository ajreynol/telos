import Telos.Solver.Sat.Basic
open Telos.Sat
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648
def check (n seed : Nat) : Bool := Id.run do
  let mut s := seed
  let mut a : Array Nat := #[]
  for _ in [0:n] do
    s := lcg s
    a := a.push (s % 50)
  let b := sort (· < ·) a
  return b.toList == a.toList.mergeSort (· ≤ ·)
#guard (List.range 200).all fun i => check (i % 60) (i * 7 + 3)
