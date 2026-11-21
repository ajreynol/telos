import Telos.Solver.Theory.Arith.DenseMap

/-!
# The sparse matrix and the tableau

cvc5's `Matrix<Rational>` (`src/theory/arith/linear/matrix.h`) and `Tableau`
(`tableau.{h,cpp}`). The entries are in one array, each in two doubly linked
lists, its row's and its column's. A new entry goes at the head of both lists,
and a freed entry is reused first in, first out, so the order in which rows and
columns are traversed, which decides the simplex's choices, is cvc5's.

A row of the tableau, with basic variable `x`, is `Σ aᵢ·xᵢ - x = 0` (`addRow`
adds `x` with coefficient `-1`).

The coefficient-change callback (`CoefficientChangeCallback`, which the linear
equality module uses to track the signs of rows' entries) is a structure of
functions on the caller's state `σ`.
-/

namespace Telos.Solver.Arith

/-- No entry (`ENTRYID_SENTINEL`). -/
def noEntry : Nat := 0xFFFFFFFF

/-- `MatrixEntry<Rational>`. A blank entry has `row = noEntry`. -/
structure Entry where
  row : Nat := noEntry
  col : Nat := noEntry
  nextRow : Nat := noEntry
  nextCol : Nat := noEntry
  prevRow : Nat := noEntry
  prevCol : Nat := noEntry
  coeff : Rat := 0
  deriving Inhabited, Repr

def Entry.blank (e : Entry) : Bool := e.row == noEntry

/-- `MatrixVector`: the head of a list, and its length. -/
structure Vec where
  head : Nat := noEntry
  size : Nat := 0
  deriving Inhabited, Repr

/-- `CoefficientChangeCallback`, on the caller's state. -/
structure CoeffCallback (σ : Type) where
  /-- The coefficient of `col` in row `row` changed sign. -/
  update : σ → (row col : Nat) → (oldSgn newSgn : Int) → σ
  /-- Row `row` was multiplied by a number of this sign. -/
  multiplyRow : σ → (row : Nat) → (sgn : Int) → σ
  /-- Whether the row's signs are tracked (`canUseRow`). -/
  canUseRow : σ → (row : Nat) → Bool

/-- `NoEffectCCCB`. -/
def CoeffCallback.none : CoeffCallback Unit :=
  ⟨fun s _ _ _ _ => s, fun s _ _ => s, fun _ _ => false⟩

def ratSgn (q : Rat) : Int := if q < 0 then -1 else if q == 0 then 0 else 1

/-- `Matrix<Rational>`, with the `Tableau`'s maps between basic variables and
rows. -/
structure Tableau where
  rows : Array Vec := #[]
  cols : Array Vec := #[]
  entries : Array Entry := #[]
  /-- The freed entries, reused first in, first out (`std::queue`): `freed`
  from `freedHead` on. -/
  freed : Array Nat := #[]
  freedHead : Nat := 0
  /-- `d_mergeBuffer`: for each column, its entry in the buffered row, and
  whether it was used. -/
  mergeBuffer : DenseMap (Nat × Bool) := {}
  rowInMergeBuffer : Nat := noEntry
  entriesInUse : Nat := 0
  /-- The released row indices (`d_pool`, a stack). -/
  pool : Array Nat := #[]
  basic2Row : DenseMap Nat := {}
  row2Basic : DenseMap Nat := {}
  deriving Inhabited

namespace Tableau

def entry (m : Tableau) (id : Nat) : Entry := m.entries[id]!

/-- `MatrixEntryVector::newEntry`. -/
private def newEntryId (m : Tableau) : Tableau × Nat :=
  if m.freedHead < m.freed.size then
    let id := m.freed[m.freedHead]!
    -- compact the queue once it is all used
    let m := if m.freedHead + 1 == m.freed.size then { m with freed := #[], freedHead := 0 }
      else { m with freedHead := m.freedHead + 1 }
    (m, id)
  else ({ m with entries := m.entries.push {} }, m.entries.size)

/-- Insert entry `id` at the head of row `r` (`MatrixVector<_, true>::insert`). -/
private def rowInsert (m : Tableau) (r id : Nat) : Tableau :=
  let v := m.rows[r]!
  let entries := m.entries.modify id fun e => { e with nextRow := v.head }
  let entries := if v.head != noEntry then entries.modify v.head fun e => { e with prevRow := id } else entries
  { m with entries, rows := m.rows.set! r { head := id, size := v.size + 1 } }

private def colInsert (m : Tableau) (c id : Nat) : Tableau :=
  let v := m.cols[c]!
  let entries := m.entries.modify id fun e => { e with nextCol := v.head }
  let entries := if v.head != noEntry then entries.modify v.head fun e => { e with prevCol := id } else entries
  { m with entries, cols := m.cols.set! c { head := id, size := v.size + 1 } }

private def rowRemove (m : Tableau) (r id : Nat) : Tableau :=
  let v := m.rows[r]!
  let e := m.entry id
  let head := if v.head == id then e.nextRow else v.head
  let entries := if e.prevRow != noEntry then m.entries.modify e.prevRow fun x => { x with nextRow := e.nextRow } else m.entries
  let entries := if e.nextRow != noEntry then entries.modify e.nextRow fun x => { x with prevRow := e.prevRow } else entries
  { m with entries, rows := m.rows.set! r { head, size := v.size - 1 } }

private def colRemove (m : Tableau) (c id : Nat) : Tableau :=
  let v := m.cols[c]!
  let e := m.entry id
  let head := if v.head == id then e.nextCol else v.head
  let entries := if e.prevCol != noEntry then m.entries.modify e.prevCol fun x => { x with nextCol := e.nextCol } else m.entries
  let entries := if e.nextCol != noEntry then entries.modify e.nextCol fun x => { x with prevCol := e.prevCol } else entries
  { m with entries, cols := m.cols.set! c { head, size := v.size - 1 } }

/-- `addEntry`: a new entry at the head of its row and of its column. -/
def addEntry (m : Tableau) (row col : Nat) (coeff : Rat) : Tableau :=
  let (m, id) := m.newEntryId
  let m := { m with entries := m.entries.set! id { row, col, coeff }, entriesInUse := m.entriesInUse + 1 }
  let m := m.rowInsert row id
  m.colInsert col id

/-- `removeEntry`: unlinked, marked blank (its links are kept, as cvc5's, so
that an iterator on it can go on), and freed. -/
def removeEntry (m : Tableau) (id : Nat) : Tableau :=
  let e := m.entry id
  let m := { m with entriesInUse := m.entriesInUse - 1 }
  let m := m.rowRemove e.row id
  let m := m.colRemove e.col id
  { m with entries := m.entries.modify id (fun x => { x with row := noEntry, col := noEntry }),
           freed := m.freed.push id }

/-- The entries of a row, from its head (`RowIterator`). -/
def rowEntries (m : Tableau) (r : Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut cur := m.rows[r]!.head
  while cur != noEntry do
    out := out.push cur
    cur := (m.entry cur).nextRow
  return out

/-- The entries of a column, from its head (`ColIterator`). -/
def colEntries (m : Tableau) (c : Nat) : Array Nat := Id.run do
  let mut out := #[]
  let mut cur := m.cols[c]!.head
  while cur != noEntry do
    out := out.push cur
    cur := (m.entry cur).nextCol
  return out

def numRows (m : Tableau) : Nat := m.rows.size
def numColumns (m : Tableau) : Nat := m.cols.size
def rowLength (m : Tableau) (r : Nat) : Nat := m.rows[r]!.size
def colLength (m : Tableau) (c : Nat) : Nat := m.cols[c]!.size

/-- `increaseSize`: a new column. -/
def increaseSize (m : Tableau) : Tableau := { m with cols := m.cols.push {} }

def increaseSizeTo (m : Tableau) (s : Nat) : Tableau :=
  if m.cols.size ≥ s then m else { m with cols := m.cols ++ Array.replicate (s - m.cols.size) {} }

/-- `requestRowIndex`. -/
private def requestRowIndex (m : Tableau) : Tableau × Nat :=
  if m.pool.isEmpty then ({ m with rows := m.rows.push {} }, m.rows.size)
  else ({ m with pool := m.pool.pop }, m.pool.back!)

/-- `loadRowIntoBuffer`. -/
def loadRowIntoBuffer (m : Tableau) (r : Nat) : Tableau :=
  let mb := (m.rowEntries r).foldl (fun mb id => mb.set (m.entry id).col (id, false)) m.mergeBuffer
  { m with mergeBuffer := mb, rowInMergeBuffer := r }

def clearBuffer (m : Tableau) : Tableau :=
  { m with rowInMergeBuffer := noEntry, mergeBuffer := m.mergeBuffer.purge }

/-- `rowPlusBufferTimesConstant`: `to += mult · buffered row`, with the
callback when one is given (cvc5 has two versions; without a callback, an
entry is removed whenever its coefficient becomes zero, with one, when its
sign changes to zero, which is the same). -/
def rowPlusBufferTimesConstant {σ : Type} (cb : Option (CoeffCallback σ)) (m : Tableau) (s : σ)
    (to : Nat) (mult : Rat) : Tableau × σ := Id.run do
  let mut m := m
  let mut s := s
  for id in m.rowEntries to do
    let e := m.entry id
    if m.mergeBuffer.isKey e.col then
      let (bid, _) := m.mergeBuffer.get e.col
      m := { m with mergeBuffer := m.mergeBuffer.modify e.col fun (b, _) => (b, true) }
      let old := ratSgn e.coeff
      let c := e.coeff + mult * (m.entry bid).coeff
      m := { m with entries := m.entries.modify id fun x => { x with coeff := c } }
      let new := ratSgn c
      if let some cb := cb then
        if old != new then s := cb.update s to e.col old new
      if new == 0 then m := m.removeEntry id
  for id in m.rowEntries m.rowInMergeBuffer do
    let e := m.entry id
    if (m.mergeBuffer.get e.col).2 then
      m := { m with mergeBuffer := m.mergeBuffer.modify e.col fun (b, _) => (b, false) }
    else
      let c := mult * e.coeff
      m := m.addEntry to e.col c
      if let some cb := cb then s := cb.update s to e.col 0 (ratSgn c)
  return (m, s)

/-- `findOnRow`. -/
def findOnRow (m : Tableau) (r col : Nat) : Nat :=
  ((m.rowEntries r).find? fun id => (m.entry id).col == col).getD noEntry

/-- `findOnCol`. -/
def findOnCol (m : Tableau) (r col : Nat) : Nat :=
  ((m.colEntries col).find? fun id => (m.entry id).row == r).getD noEntry

/-- `findEntryID`: along the shorter of the row and the column. -/
def findEntryId (m : Tableau) (r col : Nat) : Nat :=
  if m.colLength col < m.rowLength r then m.findOnCol r col else m.findOnRow r col

/-- The coefficient of `col` in row `r` (`findEntry`; zero if none). -/
def coeffAt (m : Tableau) (r col : Nat) : Rat :=
  let id := m.findEntryId r col
  if id == noEntry then 0 else (m.entry id).coeff

/-- `manipulateRowEntry`: add `c` to the coefficient of `col` in row `r`. -/
def manipulateRowEntry {σ : Type} (cb : CoeffCallback σ) (m : Tableau) (s : σ) (r col : Nat) (c : Rat) :
    Tableau × σ :=
  let id := m.findEntryId r col
  let (m, id, old, new) :=
    if id == noEntry then
      let m := m.addEntry r col c
      -- the new entry is at the head of the row
      (m, m.rows[r]!.head, (0 : Int), ratSgn c)
    else
      let e := m.entry id
      let t := e.coeff + c
      ({ m with entries := m.entries.modify id fun x => { x with coeff := t } }, id, ratSgn e.coeff, ratSgn t)
  let s := if old != new then cb.update s r col old new else s
  let m := if new == 0 then m.removeEntry id else m
  (m, s)

/-- `removeRow`. -/
def removeRow (m : Tableau) (r : Nat) : Tableau :=
  let m := (m.rowEntries r).foldl (fun m id => m.removeEntry id) m
  { m with pool := m.pool.push r }

/-! ## The tableau -/

def isBasic (m : Tableau) (v : Nat) : Bool := m.basic2Row.isKey v
def basicToRowIndex (m : Tableau) (x : Nat) : Nat := m.basic2Row.get x
def rowIndexToBasic (m : Tableau) (r : Nat) : Nat := m.row2Basic.get r
/-- The basic variables, in `d_basic2RowIndex`'s order (`beginBasic`). -/
def basics (m : Tableau) : Array Nat := m.basic2Row.keys
def basicRowEntries (m : Tableau) (x : Nat) : Array Nat := m.rowEntries (m.basicToRowIndex x)
def basicRowLength (m : Tableau) (x : Nat) : Nat := m.rowLength (m.basicToRowIndex x)
def basicFindCoeff (m : Tableau) (basic col : Nat) : Rat := m.coeffAt (m.basicToRowIndex basic) col

/-- `Tableau::addRow`: the row `Σ coeffs[i]·vars[i] - basic = 0`, with the rows
of the basic variables among `vars` substituted in. -/
def addRow (m : Tableau) (basic : Nat) (coeffs : Array Rat) (vars : Array Nat) : Tableau := Id.run do
  let (m, r) := m.requestRowIndex
  let mut m := (coeffs.zip vars).foldl (fun m (c, v) => m.addEntry r v c) m
  m := m.addEntry r basic (-1)
  m := { m with basic2Row := m.basic2Row.set basic r, row2Basic := m.row2Basic.set r basic }
  for (c, v) in coeffs.zip vars do
    if m.isBasic v then
      let ri := m.basicToRowIndex v
      m := m.loadRowIntoBuffer ri
      m := (m.rowPlusBufferTimesConstant (some CoeffCallback.none) () r c).1
      m := m.clearBuffer
  return m

/-- `rowPivot`: the row of `basicOld` is scaled by `-1/a`, for `a` the
coefficient of `basicNew`, which becomes its basic variable. -/
private def rowPivot {σ : Type} (cb : CoeffCallback σ) (m : Tableau) (s : σ) (basicOld basicNew : Nat) :
    Tableau × σ :=
  let r := m.basicToRowIndex basicOld
  let a := (m.entry (m.findOnRow r basicNew)).coeff
  let negInv := -(1 / a)
  let m := (m.rowEntries r).foldl (fun m id =>
    { m with entries := m.entries.modify id fun e => { e with coeff := e.coeff * negInv } }) m
  let m := { m with basic2Row := (m.basic2Row.remove basicOld).set basicNew r,
                    row2Basic := m.row2Basic.set r basicNew }
  (m, cb.multiplyRow s r (-(ratSgn a)))

/-- `Tableau::pivot`: `basicNew` replaces `basicOld`, and is eliminated from the
other rows, in the order of its column. -/
def pivot {σ : Type} (cb : CoeffCallback σ) (m : Tableau) (s : σ) (basicOld basicNew : Nat) :
    Tableau × σ := Id.run do
  let r := m.basicToRowIndex basicOld
  let (m₁, s₁) := m.rowPivot cb s basicOld basicNew
  let mut m := m₁.loadRowIntoBuffer r
  let mut s := s₁
  -- the column's entries, as the iterator meets them: each next entry is read
  -- before the current one's row changes
  let mut cur := m.cols[basicNew]!.head
  while cur != noEntry do
    let e := m.entry cur
    cur := e.nextCol
    if e.row == r then continue
    let (m', s') := m.rowPlusBufferTimesConstant (if cb.canUseRow s e.row then some cb else none) s e.row e.coeff
    m := m'; s := s'
  return (m.clearBuffer, s)

/-- `removeBasicRow`. -/
def removeBasicRow (m : Tableau) (basic : Nat) : Tableau :=
  let r := m.basicToRowIndex basic
  let m := m.removeRow r
  { m with basic2Row := m.basic2Row.remove basic, row2Basic := m.row2Basic.remove r }

/-- `substitutePlusTimesConstant`: `to += mult · (row of from)`, with an entry
for `from` added first, to be cancelled. -/
def substitutePlusTimesConstant {σ : Type} (cb : CoeffCallback σ) (m : Tableau) (s : σ) (to from_ : Nat)
    (mult : Rat) : Tableau × σ :=
  if mult == 0 then (m, s) else
  let ti := m.basicToRowIndex to
  let m := m.addEntry ti from_ mult
  let fi := m.basicToRowIndex from_
  let s := cb.update s ti from_ 0 (ratSgn mult)
  let m := m.loadRowIntoBuffer fi
  let (m, s) := m.rowPlusBufferTimesConstant (some cb) s ti mult
  (m.clearBuffer, s)

/-- `directlyAddToCoefficient`. -/
def directlyAddToCoefficient {σ : Type} (cb : CoeffCallback σ) (m : Tableau) (s : σ) (rowVar col : Nat)
    (mult : Rat) : Tableau × σ :=
  m.manipulateRowEntry cb s (m.basicToRowIndex rowVar) col mult

end Tableau

end Telos.Solver.Arith
