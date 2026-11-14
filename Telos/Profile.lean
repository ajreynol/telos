import Std.Data.HashMap

/-!
# Profiling probes

`Profile.time cat key f` is `f ()`. When profiling is enabled (`Profile.enable`,
from `--profile` in `telos` and `telos-fuzz`), it also adds the time spent in
`f ()` to the entry `(cat, key ())`. `Profile.report` prints the table to
standard error. When profiling is off, a probe reads one flag and calls `f ()`;
`key` is not evaluated.

The times are of the probed code only. The `total` entries (`Profile.measure`,
one per query) also contain the probes' own overhead, about 0.2µs per probe,
which the report estimates by calibration and prints in its header. Nested
probes are counted in both entries (a type query inside the arithmetic normal
form, say), so categories can add up to more than the total. Compare wall
times without `--profile`.

## Trust

`time` is `implemented_by` an `unsafe` implementation that reads a global flag
and the clock with `unsafeBaseIO`. Its result is `f ()` on every path, which is
what the reference definition says. It is listed in `TRUSTED.md`.
-/

namespace Telos.Profile

structure Entry where
  calls : Nat := 0
  nanos : Nat := 0

initialize enabledRef : IO.Ref Bool ← IO.mkRef false
/-- One ref per entry. Values stored in a ref made by `initialize` are shared
between threads, so the runtime copies them instead of updating them in place;
a table of entries in a single ref was copied on every probe (about 4µs). With
a ref per entry, a probe only looks its entry up and replaces two numbers. -/
initialize tableRef : IO.Ref (Std.HashMap (String × String) (IO.Ref Entry)) ← IO.mkRef {}

def enable : IO Unit := enabledRef.set true

def enabled : IO Bool := enabledRef.get

def record (cat key : String) (nanos : Nat) : BaseIO Unit := do
  match (← tableRef.get)[(cat, key)]? with
  | some r => r.modify fun e => { calls := e.calls + 1, nanos := e.nanos + nanos }
  | none =>
    let r ← IO.mkRef { calls := 1, nanos }
    tableRef.modify (·.insert (cat, key) r)

/-- The entries recorded so far. -/
def entries : IO (Array ((String × String) × Entry)) := do
  (← tableRef.get).toArray.mapM fun (k, r) => return (k, ← r.get)

/-- Evaluate `f ()` here, not where its result is used. -/
@[noinline] def force {α : Type} (f : Unit → α) : BaseIO α := pure (f ())

unsafe def timeImpl {α : Type} (cat : String) (key : Unit → String) (f : Unit → α) : α :=
  unsafeBaseIO do
    if !(← enabledRef.get) then return f ()
    let t0 ← IO.monoNanosNow
    let r ← force f
    let t1 ← IO.monoNanosNow
    record cat (key ()) (t1 - t0)
    return r

/-- `f ()`, timed under `(cat, key ())` when profiling is enabled. -/
@[implemented_by timeImpl]
def time {α : Type} (_cat : String) (_key : Unit → String) (f : Unit → α) : α := f ()

/-- `f ()`, timed under `(cat, key)` when profiling is enabled. For `IO` code,
such as the loop over queries; needs no trust. -/
def measure {α : Type} (cat key : String) (f : Unit → α) : IO α := do
  if !(← enabled) then return f ()
  let t0 ← IO.monoNanosNow
  let r ← force f
  let t1 ← IO.monoNanosNow
  record cat key (t1 - t0)
  return r

private def ms (nanos : Nat) : String :=
  let tenths := (nanos + 50000) / 100000
  s!"{tenths / 10}.{tenths % 10}ms"

private def pct (part whole : Nat) : String :=
  if whole == 0 then "-" else
    let tenths := (part * 1000 + whole / 2) / whole
    s!"{tenths / 10}.{tenths % 10}%"

private def pad (n : Nat) (s : String) : String :=
  s ++ String.ofList (List.replicate (n - s.length) ' ')

private def lpad (n : Nat) (s : String) : String :=
  String.ofList (List.replicate (n - s.length) ' ') ++ s

private def row (name : String) (e : Entry) (total : Nat) : String :=
  let perCall := if e.calls == 0 then "-" else s!"{e.nanos / e.calls / 1000}.{(e.nanos / e.calls / 100) % 10}µs"
  s!"{pad 42 name}{lpad 9 (toString e.calls)}{lpad 12 (ms e.nanos)}{lpad 8 (pct e.nanos total)}{lpad 11 perCall}"

@[noinline] private def calibrationWork (i : Nat) : Nat := i + 1

/-- The cost of one enabled probe around trivial work, in nanoseconds, measured
on a scratch entry that is then removed. -/
def probeOverhead (n : Nat := 100000) : IO Nat := do
  let t0 ← IO.monoNanosNow
  let mut acc := 0
  for i in [0:n] do
    acc := acc + time "calibration" (fun _ => "probe") fun _ => calibrationWork i
  let t1 ← IO.monoNanosNow
  for i in [0:n] do
    acc := acc + (← force fun _ => calibrationWork i)
  let t2 ← IO.monoNanosNow
  tableRef.modify (·.erase ("calibration", "probe"))
  -- Keep `acc` alive.
  if acc == 0 then IO.eprintln ""
  return ((t1 - t0) - (t2 - t1)) / n

/-- Print the table to standard error: each category with its total, then its
`top` most expensive keys. Shares are of the `total` category. -/
def report (top : Nat := 10) : IO Unit := do
  let overhead ← probeOverhead
  let entries ← entries
  let probes := (entries.filter (·.1.1 != "total")).foldl (fun acc (_, e) => acc + e.calls) 0
  let total := (entries.filter (·.1.1 == "total")).foldl (fun acc (_, e) => acc + e.nanos) 0
  let cats := (entries.map (·.1.1)).toList.eraseDups.toArray.qsort (· < ·)
  let catTotal (c : String) : Entry :=
    (entries.filter (·.1.1 == c)).foldl
      (fun acc (_, e) => { calls := acc.calls + e.calls, nanos := acc.nanos + e.nanos }) {}
  let cats := cats.qsort fun a b => (catTotal a).nanos > (catTotal b).nanos
  IO.eprintln s!"{probes} probes at about {overhead}ns each: about {ms (probes * overhead)} of the total is probe overhead"
  IO.eprintln s!"{pad 42 "telos profile"}{lpad 9 "calls"}{lpad 12 "time"}{lpad 8 "share"}{lpad 11 "per call"}"
  for c in cats do
    IO.eprintln (row c (catTotal c) total)
    let keys := (entries.filter (·.1.1 == c)).qsort fun a b => a.2.nanos > b.2.nanos
    for (k, e) in keys.toList.take top do
      IO.eprintln (row s!"  {k.2}" e total)
    if keys.size > top then IO.eprintln s!"  ... {keys.size - top} more"

end Telos.Profile
