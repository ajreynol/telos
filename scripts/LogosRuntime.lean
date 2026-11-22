import Lean
import Lean.Compiler.LCNF.PhaseExt

/-!
Backend for logos-runtime.py. Read Lean's saved base LCNF (after proof erasure
and early simplification/specialization), so elaborated names, implicit instances, partial
applications and private/generated helpers are visible. No theorem bodies,
types or constructor allocations are counted. This tool is not solver code.
-/

open Lean Compiler.LCNF

private def relevant (m : Name) : Bool :=
  m == `Telos || m == `Main || (`Telos).isPrefixOf m ||
  m == `Cpc || (`Cpc).isPrefixOf m || m == `Logos || (`Logos).isPrefixOf m

private def owner (env : Environment) (owners : Std.HashMap Name Name) (n : Name) : Name :=
  match owners[n]? with
  | some m => m
  | none => match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!
    | none => .anonymous

private partial def calls (code : Code .pure) : Array (Name × Nat) := Id.run do
  match code with
  | .let d k =>
    let rest := calls k
    match d.value with
    | .const n _ args _ => return #[(n, args.size)] ++ rest
    | _ => return rest
  | .fun d k _ | .jp d k => return calls d.value ++ calls k
  | .cases c =>
    let mut result := #[]
    for alt in c.alts do
      match alt with
      | .alt _ _ body _ | .default body => result := result ++ calls body
    return result
  | .jmp .. | .return .. | .unreach .. => return #[]

private partial def sourceLine (env : Environment) (m n : Name) : Nat :=
  if n.isAnonymous then 0
  else
    let sameModule := (env.getModuleIdxFor? n).any fun i => env.header.moduleNames[i.toNat]! == m
    match declRangeExt.find? env n with
    | some r => if sameModule then r.selectionRange.pos.line else sourceLine env m n.getPrefix
    | none => sourceLine env m n.getPrefix

private def callerLine (env : Environment) (m n : Name) : Nat :=
  -- A specialization's name starts with its original library helper. Locate
  -- the specializing caller instead, never a line in an unrelated source file.
  let base := ((n.toString.splitOn "._at_.").getLast!).toName
  let line := sourceLine env m base
  if line == 0 then sourceLine env m n else line

-- Loading compiler extensions requires Lean's initializer hook. This unsafe
-- entry point is confined to this audit tool; it does not enter Telos's TCB.
unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports := args.toArray.map fun m => ({ module := m.toName } : Import)
  let env ← importModules imports {} (loadExts := true)
  let mut owners : Std.HashMap Name Name := {}
  let mut decls : Array (Name × Decl .pure) := #[]
  for i in [:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    for d in baseExt.getModuleEntries env i do
      owners := owners.insert d.name m
      if relevant m then decls := decls.push (m, d)
  let stdout ← IO.getStdout
  for (m, d) in decls do
    let .code body := d.value | continue
    for (callee, argc) in calls body do
      let target := owner env owners callee
      if !relevant target then continue
      if let some (.ctorInfo _) := env.find? callee then continue
      let arity := (getDeclCore? env baseExt callee).map (·.params.size)
      let form := if argc == 0 then "value/function reference"
        else if arity.any (argc < ·) then "partial application" else "application"
      let row := Json.mkObj [
        ("module", toJson m.toString), ("caller", toJson d.name.toString),
        ("line", toJson (callerLine env m d.name)),
        ("target_module", toJson target.toString), ("callee", toJson callee.toString),
        ("form", toJson form)]
      stdout.putStrLn row.compress
