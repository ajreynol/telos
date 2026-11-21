import Telos.Solver.Theory.Arith.Matrix
open Telos.Solver.Arith

def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- The value of each basic variable from its row, for values `val` of the
others (a row is `Σ aᵢ·xᵢ - x = 0`). -/
def basicValue (m : Tableau) (val : Nat → Rat) (x : Nat) : Rat :=
  (m.basicRowEntries x).foldl (fun acc id =>
    let e := m.entry id
    if e.col == x then acc else acc + e.coeff * val e.col) 0

/-- The rows and the columns hold the same entries, with consistent sizes. -/
def consistent (m : Tableau) : Bool :=
  (List.range m.numRows).all (fun r =>
    let es := m.rowEntries r
    es.size == m.rowLength r && es.all fun id =>
      let e := m.entry id
      e.row == r && e.coeff != 0 && (m.colEntries e.col).contains id) &&
  (List.range m.numColumns).all fun c =>
    let es := m.colEntries c
    es.size == m.colLength c && es.all fun id => (m.entry id).col == c

/-- Rows for basic variables `n..n+k-1` over `0..n-1`, random pivots; after
each, every original equation holds for random values of the nonbasic
variables, and the basic variable of each row has coefficient `-1`. -/
def check (seed : Nat) : Bool := Id.run do
  let n := 6
  let k := 4
  let mut s := seed
  let mut m : Tableau := ({} : Tableau).increaseSizeTo (n + k)
  let mut orig : Array (Nat × Array (Rat × Nat)) := #[]
  for b in [n:n+k] do
    let mut row := #[]
    for v in [0:n] do
      s := lcg s
      if s % 3 != 0 then
        s := lcg s
        row := row.push (((s % 7 : Nat) : Rat) - 3 + (if s % 7 == 3 then 1 else 0), v)
    orig := orig.push (b, row)
    m := m.addRow b (row.map (·.1)) (row.map (·.2))
  for _ in [0:12] do
    if !consistent m then return false
    -- the basic variables have coefficient -1 in their rows
    for b in m.basics do
      if m.basicFindCoeff b b != -1 then return false
    -- the original equations hold
    let mut vals : Array Rat := #[]
    for _ in [0:n+k] do
      s := lcg s
      vals := vals.push ((s % 11 : Nat) : Rat)
    let nb := fun v => if m.isBasic v then 0 else vals[v]!
    let val := fun v => if m.isBasic v then basicValue m nb v else vals[v]!
    for (b, row) in orig do
      if val b != row.foldl (fun acc (c, v) => acc + c * val v) 0 then return false
    -- a random pivot
    s := lcg s
    let bs := m.basics
    let b := bs[s % bs.size]!
    let cands := (m.basicRowEntries b).filterMap fun id =>
      let e := m.entry id; if e.col == b then none else some e.col
    if cands.isEmpty then continue
    s := lcg s
    m := (m.pivot CoeffCallback.none () b cands[s % cands.size]!).1
  return true

#guard (List.range 40).all check
