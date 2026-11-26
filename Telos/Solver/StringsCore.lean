import Telos.Solver.DtLemma
import Telos.Core.Node.OfEo
import Telos.Preprocess.Theory.StringsStaticRewrite
import Telos.Solver.Theory.StringsRegexOps
import Telos.Solver.Theory.StringsReduce

/-!
# Proofs of the core inferences of the theory of strings

A port of the part of cvc5's `InferProofCons` (`src/theory/strings/
infer_proof_cons.cpp`) for the core solver's inferences: `prove id P conc`
gives a CPC proof of `(=> (and P) conc)` (of `(=> p conc)` for one premise),
for the inference `id` with the premises `P` and the conclusion `conc` (`false`
for a conflict). The proof is checked when it is made: Logos runs it from the
empty state (`EqProof.valid`).

All of the core inferences have the form: a main equality `t = s` between
string terms, equalities that make `t` and `s` agree on a prefix (or a suffix,
`rev`), and possibly a length constraint. As cvc5 does, the proof:
- substitutes the other equalities in the main equality, and rewrites it
  (`convertCoreSubs`, `MACRO_SR_PRED_ELIM`), here by congruence and the
  verified rewriter (`EqProof`);
- strips the common prefix of its sides (`concat_eq`);
- splits the constants at the heads of the sides, as the rule needs
  (`spliceConstants`), by the rewriter (which merges them back);
- applies the rule of the inference (`concat_csplit`, `concat_cprop`,
  `concat_split`, `concat_lprop`, `concat_unify`), its length premise derived
  from the length constraint;
- relates its conclusion to `conc`: the purification skolems of the rule and
  of the solver are of terms with the same rewrite (`skolem_intro`, and the
  rewriter), and the rest by congruence and the rewriter.

The steps take each conclusion from Logos (`Node.ofEo` of the last fact
proven). The choices (which premise is the main equality, its orientation, the
direction) are tried in turn; the first proof that checks is kept.
-/

open Eo

namespace Telos.Solver.StringsCore

open Proof

/-- The facts known in a CPC proof under construction: each formula with the
position of its step, and the variables and skolems they have (to read the
conclusions of rules back as nodes). -/
structure Known where
  A : Array Node := #[]
  pos : Array Nat := #[]
  env : List Node := []
  /-- Substitutions replace the larger terms first (a premise about a term that
  another premise rewrites inside). -/
  largest : Bool := false
  /-- The main equality of an inference is not substituted by premises that
  define a variable, which also rewrite it inside the terms of skolems. -/
  keepVars : Bool := false
  /-- With `largest`, the size of an equality is that of the side it replaces
  (rather than of its larger side). -/
  byReplaced : Bool := false
  deriving Inhabited

abbrev M := StateT Known EmitM

/-- Record a fact `F` proven at step `p`: its index among the known facts. -/
def known (F : Node) (p : Nat) : M Nat :=
  modifyGet fun k => (k.A.size, { k with A := k.A.push F, pos := k.pos.push p, env := k.env ++ F.vars })

def posOf (i : Nat) : M Nat := do
  let some p := (← get).pos[i]? | throw "a fact out of range"
  return p

/-- The conclusion of a rule from the premises `prems`, read back from Logos,
which runs the rule alone (its premises assumed), not the proof so far. -/
def conclusionOf (r : CRule) (args : List PArg) (prems : List Node) : M Node := do
  let act : EmitM Unit := do
    let ps ← prems.mapM fun F => push ⟨.refl, [.node F], [], .assume⟩
    let _ ← push ⟨r, args, ps, .step⟩
  match act.run {} with
  | .error e => throw e
  | .ok ((), st) =>
    let cmds := (toCmds st.steps).foldr CCmdList.cons CCmdList.nil
    let t := __eo_state_proven_nth (runFromEmpty cmds) 0
    let some n := Node.ofEo (← get).env t | throw "a conclusion that does not read back"
    return n

/-- Apply a CPC rule to known facts: its conclusion becomes known. -/
def rule (r : CRule) (args : List PArg) (prems : List Nat) : M (Node × Nat) := do
  let ps ← prems.mapM posOf
  let A := (← get).A
  let F ← conclusionOf r args (prems.map fun i => A[i]!)
  let p ← push ⟨r, args, ps, .step⟩
  return (F, ← known F p)

/-- A proof from the known facts: its conclusion `(a, b)` becomes the known
fact `(= a b)`. -/
def eqFact (q : EqProof) : M (Node × Node × Nat) := do
  let k ← get
  let some (a, b) := EqProof.check k.A q | throw "a step that does not check"
  let p ← emitEq k.A k.pos q
  return (a, b, ← known (Node.eqNode a b) p)

/-- The literal of a proof from the known facts: `F` for `(F, true)`, `(not x)`
for `(x, false)`, `(= a b)` otherwise. -/
def litFact (q : EqProof) : M (Node × Nat) := do
  let (a, b, i) ← eqFact q
  if b == Node.mkTrue then
    let p ← push ⟨.true_elim, [], [← posOf i], .step⟩
    return (a, ← known a p)
  if b == Node.mkFalse then
    let p ← push ⟨.false_elim, [], [← posOf i], .step⟩
    let n := Node.notNode a
    return (n, ← known n p)
  return (Node.eqNode a b, i)

/-- What the known fact `i` gives as an assumption, as a proof of `(F, true)` or
`(x, false)` for its atom `x`. -/
def atomProof (F : Node) (i : Nat) : EqProof :=
  match F with
  | .app (.kind .EQUAL) #[_, _] => .eqTrue (.assume i)
  | _ => .assume i

/-! ## Terms -/

def emptyStr : Node := .const (.string [])

def concatList (t : Node) : Array Node :=
  match t with
  | .app (.kind .STRING_CONCAT) cs => cs
  | _ => #[t]

def mkConcat (cs : Array Node) (like : Node := emptyStr) : Node :=
  if h : cs.size = 1 then cs[0] else if cs.isEmpty then Strings.emptyOf like else Node.mkNode .STRING_CONCAT cs

def word? (t : Node) : Option (List Nat) :=
  match t with
  | .const (.string w) => some w
  | .const (.emptySeq _) => some []
  | _ => none

def mkWord (w : List Nat) : Node := .const (.string w)

/-- The head of a concatenation, in the direction. -/
def head? (t : Node) (rev : Bool) : Option Node :=
  let cs := concatList t
  if rev then cs.back? else cs[0]?

/-- `t` with its head (in the direction) replaced by the components `hs`. -/
def replaceHead (t : Node) (hs : Array Node) (rev : Bool) : Node :=
  let cs := concatList t
  if cs.isEmpty then t else
  mkConcat (if rev then cs.pop ++ hs else hs ++ cs.extract 1 cs.size)

/-- `(t, t')` for the rewrite `t'` of `t`, if it differs. -/
def rwProof (t : Node) : Node × Option EqProof :=
  let r := Telos.rewrite t
  if r == t then (t, none) else (r, some (.rw t))

def compose : Option EqProof → Option EqProof → Option EqProof
  | none, q => q
  | p, none => p
  | some p, some q => some (.trans p q)

/-- A proof of `(a, b)` for nodes with the same rewrite: by the rewriter. -/
def sameRw (a b : Node) : Option (Option EqProof) :=
  if a == b then some none
  else if Telos.rewrite a == Telos.rewrite b then some (some (.trans (.rw a) (.symm (.rw b))))
  else none

/-- `(k, t)` for the purification skolem `k` of `t`. -/
def purifyEq (k : Node) : Option (Node × EqProof) :=
  match k with
  | .skolem .PURIFY #[t] => some (t, .valid (Node.eqNode k t) [DT.argStep .skolem_intro k])
  | _ => none

/-- A proof of `(a, b)`, by the structure of the nodes: purification skolems
of terms with the same rewrite are equal, applications by congruence, and the
rest by the rewriter. -/
partial def bridge (a b : Node) : Option (Option EqProof) :=
  if a == b then some none else
  match a, b with
  | .skolem .PURIFY #[_], .skolem .PURIFY #[_] => do
    let (t, pa) ← purifyEq a
    let (t', pb) ← purifyEq b
    let m ← bridge t t'
    some (compose (some pa) (compose m (some (.symm pb))))
  | .app op cs, .app op' ds =>
    if op == op' && cs.size == ds.size then
      match (cs.zip ds).mapM fun (c, d) => bridge c d with
      | some args => some (some (.congAt a args))
      | none => sameRw a b
    else sameRw a b
  | _, _ => sameRw a b

/-- `t` with its purification skolems replaced by those of the rewrites of their
terms, in turn (those of constants by the constants), and a proof of `(t, t')`,
if it differs. -/
partial def normSkolems (t : Node) : Node × Option EqProof :=
  match t with
  | .skolem .PURIFY #[u] =>
    let (v, qv) := normSkolems u
    let (w, qw) := rwProof v
    if w == u && !w.isConst then (t, none) else
    match purifyEq t with
    | none => (t, none)
    | some (_, pk) =>
      let q := compose (some pk) (compose qv qw)
      if w.isConst then (w, q) else
      let k := Node.mkPurifySkolem w
      match purifyEq k with
      | none => (t, none)
      | some (_, pk') => (k, compose q (some (.symm pk')))
  | .app op cs =>
    if !op.eoShape.substCongruent then (t, none) else
    let rs := cs.map normSkolems
    if rs.all (·.2.isNone) then (t, none)
    else (.app op (rs.map (·.1)), some (.congAt t (rs.map (·.2))))
  | _ => (t, none)

/-- A proof of `(a, b)`, for nodes that differ in their purification skolems,
up to the rewrites of their terms. -/
partial def bridgeSkolems (a b : Node) : Option EqProof :=
  let direct : Option EqProof := do
    let (a', qa) := normSkolems a
    let (b', qb) := normSkolems b
    let m ← sameRw a' b'
    compose qa (compose m (qb.map .symm))
  match a, b with
  | .app op cs, .app op' ds =>
    if op == op' && cs.size == ds.size && op.eoShape.substCongruent then
      let args := (cs.zip ds).map fun (c, d) => if c == d then some none else (bridgeSkolems c d).map some
      match args.mapM id with
      | some args => some (.congAt a args)
      | none => direct
    else direct
  | _, _ => direct

/-- `t` with each subterm `x` replaced by `y`, for the known equality `(= x y)`
at index `i` (oriented by `flip`), and its proof. -/
partial def substOne (x y : Node) (p : EqProof) (t : Node) : Option EqProof :=
  if t == x then some p else
  match t with
  | .app _ cs =>
    let args := cs.map (substOne x y p)
    if args.all (·.isNone) then none else some (.congAt t args)
  | _ => none

/-- Whether `x` occurs in `t` (each shared subterm visited once). -/
def occurs (x t : Node) : Bool := Id.run do
  let mut seen : Std.HashSet Key := {}
  let mut work := #[t]
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    if c == x then return true
    if seen.contains ⟨c⟩ then continue
    seen := seen.insert ⟨c⟩
    work := work ++ c.getChildren
  return false

/-- Whether `t`, as a tree, has at most `n` nodes (counting stops at `n`). -/
def treeSizeAtMost (n : Nat) (t : Node) : Bool := Id.run do
  let mut work := #[t]
  let mut k := 0
  while !work.isEmpty do
    let c := work.back!
    work := work.pop
    k := k + 1
    if k > n then return false
    work := work ++ c.getChildren
  return true

/-- The largest term (as a tree) that the substitutions go on with. -/
def substLimit : Nat := 3000

/-- The size of `t` as a tree, up to `n`. -/
def sizeUpTo (n : Nat) (t : Node) : Nat := Id.run do
  let mut work := #[t]
  let mut k := 0
  while !work.isEmpty && k < n do
    let c := work.back!
    work := work.pop ++ match c with
      | .app _ cs => cs
      | _ => #[]
    k := k + 1
  return k

/-- The order in which the equalities `R` are used as a substitution. -/
def substOrder (R : Array Nat) : M (Array Nat) := do
  let k ← get
  if !k.largest then return R
  let size (i : Nat) : Nat := match k.A[i]? with
    | some (.app (.kind .EQUAL) #[x, y]) =>
      if x.isConst then sizeUpTo 100 y else if y.isConst || k.byReplaced then sizeUpTo 100 x else
        max (sizeUpTo 100 x) (sizeUpTo 100 y)
    | _ => 0
  return R.qsort fun i j => size i > size j || (size i == size j && i < j)

/-- `(t, t')` for `t'` the rewrite of `t` with the substitution of the known
equalities `R` applied in turn (`SBA_SEQUENTIAL`). -/
def substRw (R : Array Nat) (t : Node) : M (Node × Option EqProof) := do
  let R ← substOrder R
  let A := (← get).A
  let mut cur := t
  let mut acc : Option EqProof := none
  -- in turn, until nothing changes (an equality may bring a term that an
  -- earlier one replaces; one that brings its own left hand side is used once)
  let mut used : Array Nat := #[]
  for _ in [0:R.size + 1] do
    let mut changed := false
    for i in R do
      if used.contains i then continue
      let some (.app (.kind .EQUAL) #[x, y]) := A[i]? | continue
      -- (a constant replaces the other side)
      let (x, y, p) : Node × Node × EqProof :=
        if x.isConst && !y.isConst then (y, x, .symm (.assume i)) else (x, y, .assume i)
      if let some q := substOne x y p cur then
        let some (_, c') := EqProof.check A q | continue
        cur := c'
        acc := compose acc (some q)
        changed := true
        if occurs x y then used := used.push i
        -- (a substitution that grows)
        if !treeSizeAtMost substLimit cur then
          changed := false
          break
    if !changed then break
  let (r, q) := rwProof cur
  return (r, compose acc q)

/-! ## The length premises -/

/-- A proof of the literal `L` (`(L, true)`, or `(x, false)` for `L` the
negation of `x`) from a known literal whose atom has the same rewrite, after
the substitution of the known equalities `R`. -/
def deriveLit (R : Array Nat) (L : Node) : M (Option EqProof) := do
  let (atom, pol) := match L with
    | .app (.kind .NOT) #[a] => (a, false)
    | a => (a, true)
  let (ra, qa) ← substRw R atom
  let A := (← get).A
  for i in [0:A.size] do
    let K := A[i]!
    let (katom, kpol) := match K with
      | .app (.kind .NOT) #[a] => (a, false)
      | a => (a, true)
    if kpol != pol then continue
    let (rk, qk) ← substRw R katom
    if rk != ra then continue
    -- `(atom, katom)`, then the known literal
    let q := compose qa (qk.map .symm)
    let lit := atomProof K i
    return some (match q with
      | some q => .trans q lit
      | none => lit)
  return none

/-- The known fact `L`, from the known literals (`deriveLit`), or by the rewriter
alone. -/
def lengthFact (R : Array Nat) (L : Node) : M Nat := do
  let q ← match ← deriveLit R L with
    | some q => pure q
    | none =>
      -- (a literal the rewriter decides, such as the equality of the lengths
      -- of two constants)
      let (atom, pol) := match L with
        | .app (.kind .NOT) #[a] => (a, false)
        | a => (a, true)
      if Telos.rewrite atom != Node.mkBool pol then throw "a length premise that does not follow"
      pure (EqProof.rw atom)
  let (F, i) ← litFact q
  if F != L then throw "a length premise of another form"
  return i

/-- The facts `(not (= (str.len s) 0))` of the known disequalities `(not (= s ""))`
(`string_length_non_empty`). -/
def nonEmptyLengths : M Unit := do
  let A := (← get).A
  for i in [0:A.size] do
    match A[i]! with
    | .app (.kind .NOT) #[.app (.kind .EQUAL) #[s, t]] =>
      if Strings.isEmptyWord t && Strings.isStringLike s then
        let _ ← rule .string_length_non_empty [] [i]
      else if Strings.isEmptyWord s && Strings.isStringLike t then
        -- `(not (= t ""))` first: the two equalities have the same rewrite
        let e := Node.eqNode s t
        let e' := Node.eqNode t s
        if Telos.rewrite e == Telos.rewrite e' then
          let (_, j) ← litFact (.trans (.rw e') (.trans (.symm (.rw e)) (.assume i)))
          let _ ← rule .string_length_non_empty [] [j]
    | _ => pure ()

/-! ## Splitting constants -/

/-- The known fact `(= t s')`, for `s'` the side `s` of the known equality
`i` with its head constant split after `n` characters (from the end, `rev`):
by the rewriter, which merges them back. -/
def splice (i : Nat) (n : Nat) (rev : Bool) : M (Node × Nat) := do
  let A := (← get).A
  let some (.app (.kind .EQUAL) #[t, s]) := A[i]? | throw "a splice of a non-equality"
  let some h := head? s rev | throw "a splice without a head"
  let some w := word? h | throw "a splice of a non-constant"
  if n == 0 || n ≥ w.length then return (A[i]!, i)
  let (w₁, w₂) := if rev then (w.take (w.length - n), w.drop (w.length - n)) else (w.take n, w.drop n)
  let s' := replaceHead s #[mkWord w₁, mkWord w₂] rev
  let some q := sameRw s s' | throw "a splice the rewriter does not undo"
  let q := match q with
    | some q => EqProof.trans (.assume i) q
    | none => .assume i
  let (_, _, j) ← eqFact q
  return (Node.eqNode t s', j)

/-! ## The inferences -/

/-- The rule of an inference, and whether it is a conflict of constants. -/
inductive Kind where
  /-- `STRINGS_CTN_POS`, `STRINGS_CTN_NEG_EQUAL`, `STRINGS_CTN_DECOMPOSE`: the
  eager reduction of a `str.contains` of the premises. -/
  | ctn
  /-- `STRINGS_EXTF_EQ_REW`: the last premise, with the substitution of the
  others, by cvc5's extended rewriting of equalities. -/
  | eqRew
  /-- `STRINGS_ARITH_BOUND_CONFLICT`: a length equal to a constant beyond its
  bound. -/
  | bound
  /-- `string_decompose`, from a premise `(>= (str.len x) n)`. -/
  | decompose
  | csplit | cprop | split | lprop | unify | const | eq
  /-- Substitution and rewriting: the main equality rewrites to `false` (a
  conflict), or the conclusion to `true`. -/
  | sr
  deriving BEq, Inhabited

def kindOf (id : String) : Option Kind :=
  match id with
  | "STRINGS_CTN_POS" | "STRINGS_CTN_NEG_EQUAL" | "STRINGS_CTN_DECOMPOSE" => some .ctn
  | "STRINGS_EXTF_EQ_REW" => some .eqRew
  | "STRINGS_ARITH_BOUND_CONFLICT" => some .bound
  | "STRINGS_DEQ_DISL_STRINGS_SPLIT" | "STRINGS_DEQ_DISL_FIRST_CHAR_STRING_SPLIT" => some .decompose
  | "STRINGS_SSPLIT_CST" => some .csplit
  | "STRINGS_SSPLIT_CST_PROP" => some .cprop
  | "STRINGS_SSPLIT_VAR" => some .split
  | "STRINGS_SSPLIT_VAR_PROP" => some .lprop
  | "STRINGS_N_UNIFY" | "STRINGS_F_UNIFY" => some .unify
  | "STRINGS_N_CONST" | "STRINGS_F_CONST" | "STRINGS_N_EQ_CONF" => some .const
  | "STRINGS_N_ENDPOINT_EMP" | "STRINGS_N_ENDPOINT_EQ" | "STRINGS_F_ENDPOINT_EMP"
  | "STRINGS_F_ENDPOINT_EQ" | "STRINGS_N_NCTN" | "STRINGS_F_NCTN" => some .eq
  | _ => some .sr

def len (t : Node) : Node := Node.mkNode .STRING_LENGTH #[t]
def zero : Node := .const (.integer 0)

/-- The known fact `conc` from the known fact `C` (index `j`): by
`bridge`, or for `false`, by the rewriter on `C`. -/
def conclude (C : Node) (j : Nat) (conc : Node) (R : Array Nat := #[]) : M Nat := do
  let pc := atomProof C j
  if conc == Node.mkFalse then
    -- `C` rewrites to `false`
    let (atom, pol) := match C with
      | .app (.kind .NOT) #[a] => (a, false)
      | a => (a, true)
    -- (`(atom, ¬pol)`: by the rewriter, or for an equality of strings by
    -- cvc5's extended equality rewriting, `rewriteStrEqualityExt`, whose
    -- CPC proof is checked)
    let byRw : Option EqProof :=
      if Telos.rewrite atom == Node.mkBool (!pol) then some (.rw atom)
      else if pol && atom.getKind == .EQUAL then do
        let r ← Preprocess.strEqualityExt atom
        if r.1 != Node.mkFalse then none
        let cs ← Proof.cmdsOf r
        some (.valid (Node.eqNode atom Node.mkFalse) cs)
      else none
    let some v := byRw | throw "a conclusion that is not false"
    -- `(true, false)`, as `(false, true)`
    let contra : EqProof := if pol then .trans (.symm pc) v else .trans (.symm v) pc
    let (_, i) ← litFact (.symm contra)
    return i
  let some q := bridge C conc | do
    -- by the substitution of the premises `R` in both, then rewriting (cvc5's
    -- `applyPredTransform`): `(conc, D)` and `(C, D)`
    -- (or of one of them: the others may change the terms of the skolems)
    for R' in (if R.size > 1 then #[R] ++ R.map (#[·]) else #[R]) do
      if R'.isEmpty then continue
      let (dc, qc) ← substRw R' conc
      let (dC, qC) ← substRw R' C
      if dc == dC then
        let q : Option EqProof := compose qc (qC.map .symm)
        let (F, i) ← litFact (match q with | some q => .trans q pc | none => pc)
        if F != conc then throw "a conclusion of another form"
        return i
    -- by extended equality rewriting (cvc5's `RW_REWRITE_EQ_EXT`), which Logos
    -- checks: `(= C C')`, with `C'` the conclusion up to rewriting
    let .app (.kind .EQUAL) #[_, _] := C | throw "a conclusion that does not bridge"
    let some r := Preprocess.strEqualityExt C | throw "a conclusion that does not bridge"
    let C' := r.1
    if C' != conc && Telos.rewrite C' != Telos.rewrite conc then throw "a conclusion that does not bridge"
    let some cs := Proof.cmdsOf r | throw "a conclusion that does not bridge"
    let pEq : EqProof := .valid (Node.eqNode C C') cs
    -- `(conc, C')`, then `(C', C)`, then `C`
    let toC' : EqProof := if C' == conc then .symm pEq
      else .trans (.rw conc) (.trans (.symm (.rw C')) (.symm pEq))
    let (F, i) ← litFact (.trans toC' pc)
    if F != conc then throw "a conclusion of another form"
    return i
  let q := match q with
    | some q => EqProof.trans (.symm q) pc
    | none => pc
  let (F, i) ← litFact q
  if F != conc then throw "a conclusion of another form"
  return i

/-- `t` with its purification skolems replaced by the terms they purify, in
turn (cvc5's `SkolemManager::getOriginalForm`), and a proof of `(t, t')`,
each skolem's equality by `skolem_intro`; `none` if `t` has none. -/
partial def purifyOriginalM (t : Node) : StateM (Std.HashMap Key (Option (EqProof × Node))) (Option (EqProof × Node)) := do
  if let some r := (← get).get? ⟨t⟩ then return r
  let r ← match t with
    | .skolem .PURIFY #[u] =>
      let pk : EqProof := .valid (Node.eqNode t u) [.step .skolem_intro (.cons t.toEo .nil) .nil]
      match ← purifyOriginalM u with
      | some (q, u') => pure (some (.trans pk q, u'))
      | none => pure (some (pk, u))
    | .app op cs =>
      if !op.eoShape.substCongruent then pure none else do
      let rs ← cs.mapM purifyOriginalM
      if rs.all Option.isNone then pure none
      else pure (some (.congAt t (rs.map (·.map (·.1))), .app op ((cs.zip rs).map fun (c, r) => (r.map (·.2)).getD c)))
    | _ => pure none
  modify (·.insert ⟨t⟩ r)
  return r

def purifyOriginal (t : Node) : Option (EqProof × Node) := ((purifyOriginalM t).run {}).1

/-- `substRw`, with each equality of `R` used once, in the direction whose side
occurs in the term (the premises' orientation is the equality engine's, not
the one the proof needs). -/
def substRwEither (R : Array Nat) (t : Node) : M (Node × Option EqProof) := do
  let R ← substOrder R
  let A := (← get).A
  let mut cur := t
  let mut acc : Option EqProof := none
  let mut used : Array Nat := #[]
  for _ in [0:R.size + 1] do
    let mut changed := false
    for i in R do
      if used.contains i then continue
      let some (.app (.kind .EQUAL) #[x, y]) := A[i]? | continue
      let (x, y, p) : Node × Node × EqProof :=
        -- (a term is replaced by one it has)
        if occurs x y && occurs y cur && !y.isConst then (y, x, .symm (.assume i))
        else if occurs x cur && !x.isConst then (x, y, .assume i)
        else (y, x, .symm (.assume i))
      if x.isConst then continue
      if let some q := substOne x y p cur then
        let some (_, c') := EqProof.check A q | continue
        cur := c'
        acc := compose acc (some q)
        used := used.push i
        changed := true
    if !changed then break
  let (r, q) := rwProof cur
  return (r, compose acc q)

/-- The largest expanded conclusion (as a tree) that `byOriginalForms` tries:
original forms can be exponentially larger than their skolems, when the terms
of purification skolems contain others. -/
def originalFormLimit : Nat := 400

/-- The conclusion `conc`, from the premises `R` once their purification
skolems and its own are replaced by their terms (as cvc5's proofs by
substitution and rewriting see them), substituted and rewritten. -/
def byOriginalForms (R : Array Nat) (conc : Node) : M Nat := do
  let catom := match conc with
    | .app (.kind .NOT) #[a] => a
    | a => a
  if (purifyOriginal catom).isNone then throw "a conclusion that does not rewrite"
  let A := (← get).A
  -- the premises' equalities, in original form, as known facts
  let mut R' : Array Nat := #[]
  for i in R do
    let some (.app (.kind .EQUAL) #[a, b]) := A[i]? | continue
    match purifyOriginal a, purifyOriginal b with
    | none, none => R' := R'.push i
    | pa, pb =>
      let qa := pa.map (·.1)
      let qb := pb.map (·.1)
      let q : EqProof := match qa, qb with
        | some qa, some qb => .trans (.symm qa) (.trans (.assume i) qb)
        | some qa, none => .trans (.symm qa) (.assume i)
        | none, some qb => .trans (.assume i) qb
        | none, none => .assume i
      let (_, _, j) ← eqFact q
      R' := R'.push j
  let (atom, pol) := match conc with
    | .app (.kind .NOT) #[a] => (a, false)
    | a => (a, true)
  -- only a conclusion about purification skolems needs their original forms
  let some (pq, atom') := purifyOriginal atom | throw "a conclusion that does not rewrite"
  let pc := some pq
  if !treeSizeAtMost originalFormLimit atom' then throw "a conclusion that does not rewrite"
  let (r, q) ← substRw R' atom'
  if r != Node.mkBool pol then throw "a conclusion that does not rewrite"
  let some q := compose pc q | throw "a conclusion that does not rewrite"
  let (F, i) ← litFact q
  if F != conc then throw "a conclusion of another form"
  return i

/-- The known equality `E` (at `e`) between terms whose heads are constants of
different lengths that agree on the shorter, without it: the longer is split
(`splice`), then `concat_eq`, in turn (`fuel` times). -/
partial def stripConstants (E : Node) (e : Nat) (rev : Bool) (fuel : Nat) : M (Node × Nat) := do
  if fuel == 0 then return (E, e)
  let .app (.kind .EQUAL) #[t, s] := E | return (E, e)
  let some wt := (head? t rev).bind word? | return (E, e)
  let some ws := (head? s rev).bind word? | return (E, e)
  let l := min wt.length ws.length
  if l == 0 || wt.length == ws.length then return (E, e)
  let pre (w : List Nat) := if rev then w.drop (w.length - l) else w.take l
  if pre wt != pre ws then return (E, e)
  let (_, e₁) ← splice e l rev
  let (_, _, e₂) ← eqFact (.symm (.assume e₁))
  let (_, e₃) ← splice e₂ l rev
  let (E', e') ← rule .concat_eq [.node (Node.mkBool rev)] [e₃]
  stripConstants E' e' rev (fuel - 1)

/-- The steps of the inference from the known premises: the main equality
`m` (oriented by `flip`), in the direction `rev`. The index of `conc`. -/
def coreSteps (k : Kind) (n : Nat) (m : Nat) (flip rev : Bool) (conc : Node) : M Nat := do
  let A := (← get).A
  if k == .ctn then
    let isContains (l : Node) : Bool := match l with
      | .app (.kind .STRING_CONTAINS) _ => true
      | .app (.kind .NOT) #[.app (.kind .STRING_CONTAINS) _] => conc != Node.mkFalse
      | _ => false
    let some i := (List.range n).find? (fun i => isContains A[i]!)
      | throw "no str.contains"
    let (atom, pol) := match A[i]! with
      | .app (.kind .NOT) #[a] => (a, false)
      | a => (a, true)
    let (_, r) ← rule .string_eager_reduction [.node atom] []
    let (_, c) ← rule (if pol then .ite_elim1 else .ite_elim2) [] [r]
    let (C, j) ← if pol then rule .resolution [.node (Node.mkBool false), .node atom] [c, i]
      else rule .resolution [.node (Node.mkBool true), .node atom] [c, i]
    if conc == Node.mkFalse then
      -- (`STRINGS_CTN_DECOMPOSE`) a negative `str.contains` that, with this
      -- equality and the premises', rewrites to `true`
      let R := ((List.range n).filter fun i => match A[i]! with
        | .app (.kind .EQUAL) _ => true
        | _ => false).toArray.push j
      for m in [0:n] do
        let .app (.kind .NOT) #[a] := A[m]! | continue
        let (t, qt) ← substRw R a
        if t != Node.mkTrue then continue
        let some qt := qt | continue
        let (_, i) ← litFact (.symm (.trans (.symm qt) (atomProof A[m]! m)))
        return i
      throw "no str.contains that rewrites to true"
    if C == conc then return j
    let some q := bridgeSkolems C conc | throw "a reduction of another form"
    let (F, i) ← litFact (.trans (.symm q) (atomProof C j))
    if F != conc then throw "a conclusion of another form"
    return i
  if k == .bound then
    for m in (List.range n).reverse do
      let .app (.kind .EQUAL) #[a, b] := A[m]! | continue
      let (x, c, p) : Node × Node × EqProof :=
        if b.isConst then (a, b, .assume m) else (b, a, .symm (.assume m))
      let .const (.integer v) := c | continue
      -- the length, of the term its skolem purifies, rewritten: `(x, r)`
      let (x', q₁) := match x with
        | .app (.kind .STRING_LENGTH) #[y] => match purifyEq y with
          | some (u, pk) => (Node.mkNode .STRING_LENGTH #[u], some (.congAt x #[some pk]))
          | none => (x, none)
        | _ => (x, none)
      let (r, q₂) := rwProof x'
      let toC : EqProof := match compose q₁ q₂ with
        | some q => .trans (.symm q) p
        | none => p
      -- at least one more, or at most one less, by `arith_string_pred_entail`
      for lower in [true, false] do
        let d := if lower then Node.mkNode .SUB #[r, .const (.integer (v + 1))]
          else Node.mkNode .SUB #[.const (.integer (v - 1)), r]
        let P := Node.mkNode .GEQ #[d, zero]
        let eP := Node.eqNode P Node.mkTrue
        let pP : EqProof := .valid eP [DT.argStep .arith_string_pred_entail eP]
        if (EqProof.check A pP).isNone then continue
        let some qd := substOne r c toC P | continue
        let some (_, P') := EqProof.check A qd | continue
        if Telos.rewrite P' != Node.mkFalse then continue
        let (_, i) ← litFact (.symm (.trans (.symm pP) (.trans qd (.rw P'))))
        return i
    throw "no length beyond its bound"
  if k == .eqRew then
    for m in (List.range n).reverse do
      let R := ((List.range n).filter fun i => i != m && match A[i]! with
        | .app (.kind .EQUAL) _ => true
        | _ => false).toArray
      -- (a predicate, or a negated one, whose atom rewrites to the other value)
      match A[m]! with
      | .app (.kind .EQUAL) _ => pure ()
      | l =>
        if conc != Node.mkFalse then continue
        let (atom, pol) := match l with
          | .app (.kind .NOT) #[a] => (a, false)
          | a => (a, true)
        let (r, q) ← do
          let (r, q) ← substRw R atom
          if r.isConst then pure (r, q) else substRwEither R atom
        -- (or to an equality whose extended rewrite is that value)
        let (r, q) := match r with
          | .app (.kind .EQUAL) _ => match Preprocess.strEqualityExt r with
            | some e => match Proof.cmdsOf e with
              | some cs =>
                let (v, qv) := rwProof e.1
                (v, compose (compose q (some (.valid (Node.eqNode r e.1) cs))) qv)
              | none => (r, q)
            | none => (r, q)
          | _ => (r, q)
        if r != Node.mkBool (!pol) then continue
        let some q := q | continue
        let contra : EqProof := .trans (.symm (atomProof l m)) q
        let (_, i) ← litFact (if pol then .symm contra else contra)
        return i
      let (t, qt) ← substRw R A[m]!
      let pt : EqProof := match qt with
        | some q => .trans (.symm q) (.eqTrue (.assume m))
        | none => .eqTrue (.assume m)
      -- `(t, true)`, then the extended rewrite of `t`, and its rewrite
      let (c, p) ← match Preprocess.strEqualityExt t with
        | none => pure (t, pt)
        | some r => do
          let some cs := Proof.cmdsOf r | continue
          let q : EqProof := .valid (Node.eqNode t r.1) cs
          let (c, q') := rwProof r.1
          let q := match q' with
            | some q' => EqProof.trans q q'
            | none => q
          pure (c, EqProof.trans (.symm q) pt)
      if c == Node.mkFalse then
        -- (`(false, true)`)
        if conc != Node.mkFalse then continue
        let (_, i) ← litFact p
        return i
      let parts := match c with
        | .app (.kind .AND) cs => cs
        | c => #[c]
      let some k := parts.findIdx? (fun l => l == conc || Telos.rewrite l == Telos.rewrite conc) | continue
      let p : EqProof := if parts.size > 1 then .andElim k p else p
      let (F, i) ← litFact p
      if F == conc then return i
      return ← conclude F i conc
    throw "no premise whose extended rewrite is the conclusion"
  if k == .decompose then
    let l ← match (A[0]? : Option Node) with
      | some (Node.app (.kind .GEQ) #[_, l]) => pure l
      | _ => throw "no length premise"
    let P := Node.mkNode .GEQ #[l, zero]
    -- (the rewriter, or `arith_string_pred_entail`)
    let nonneg : EqProof := if Telos.rewrite P == Node.mkTrue then .rw P
      else .valid (Node.eqNode P Node.mkTrue) [DT.argStep .arith_string_pred_entail (Node.eqNode P Node.mkTrue)]
    let some _ := EqProof.check A nonneg | throw "a length that is not known to be nonnegative"
    let (_, i) ← litFact nonneg
    let (C, j) ← rule .string_decompose [.node (Node.mkBool false)] [i, 0]
    if C == conc then return j
    let some q := bridgeSkolems C conc | throw "a decomposition of another form"
    let (F, i) ← litFact (.trans (.symm q) (atomProof C j))
    if F != conc then throw "a conclusion of another form"
    return i
  if k == .sr && conc != Node.mkFalse then
    -- the conclusion, with the substitution of the premises, rewrites to `true`
    let R := ((List.range n).filter fun i => match A[i]! with
      | .app (.kind .EQUAL) #[_, _] => true
      | _ => false).toArray
    nonEmptyLengths
    let some q ← deriveLit R conc | do
      let (atom, pol) := match conc with
        | .app (.kind .NOT) #[a] => (a, false)
        | a => (a, true)
      let (r, q) ← do
        let (r, q) ← substRw R atom
        if r == Node.mkBool pol then pure (r, q) else substRwEither R atom
      if r != Node.mkBool pol then return ← byOriginalForms R conc
      let some q := q | return ← byOriginalForms R conc
      let (F, i) ← litFact q
      if F != conc then throw "a conclusion of another form"
      return i
    let (F, i) ← litFact q
    if F != conc then throw "a conclusion of another form"
    return i
  let some (.app (.kind .EQUAL) #[a, b]) := A[m]? | throw "a main equality that is not one"
  let keepVars := (← get).keepVars
  let R := ((List.range n).filter fun i => i != m && match A[i]! with
    | .app (.kind .EQUAL) #[x, _] => Strings.isStringLike x && !(keepVars && x.getKind == .VARIABLE)
    | _ => false).toArray
  nonEmptyLengths
  -- the main equality, with the substitution and rewritten
  let (t, qa) ← substRw R (if flip then b else a)
  let (s, qb) ← substRw R (if flip then a else b)
  let main : EqProof := if flip then .symm (.assume m) else .assume m
  let q := compose (qa.map .symm) (compose (some main) qb)
  let (_, _, e₀) ← eqFact (q.getD main)
  if t == s then throw "a main equality that is trivial"
  if k == .sr then return ← conclude (Node.eqNode t s) e₀ conc R
  -- the common prefix stripped
  let (E, e) ← rule .concat_eq [.node (Node.mkBool rev)] [e₀]
  if k == .eq then
    return ← tryCatch (conclude E e conc R) fun err => do
      -- the heads of the same length unified (`concat_unify`), replaced, and
      -- the common end stripped again, as cvc5's proof does (once: each
      -- attempt costs a length derivation and a substitution)
      let mut cur := (E, e)
      for _ in [0:1] do
        let .app (.kind .EQUAL) #[t₁, s₁] := cur.1 | throw err
        let some ht := head? t₁ rev | throw err
        let some hs := head? s₁ rev | throw err
        if ht == hs then throw err
        -- (a constant or a unit against a term, whose length the premises fix,
        -- or two terms whose lengths a premise equates)
        let lenEq := (← get).A.any fun l => l == Node.eqNode (len ht) (len hs) || l == Node.eqNode (len hs) (len ht)
        if (word? ht).isNone && (word? hs).isNone && ht.getKind != .SEQ_UNIT && hs.getKind != .SEQ_UNIT && !lenEq then
          throw err
        let li ← lengthFact R (Node.eqNode (len ht) (len hs))
        let (_, u) ← rule .concat_unify [.node (Node.mkBool rev)] [cur.2, li]
        let some qt := substOne ht hs (.assume u) t₁ | throw err
        let (_, _, e') ← eqFact (.trans (.symm qt) (.assume cur.2))
        cur ← rule .concat_eq [.node (Node.mkBool rev)] [e']
        if let .ok i ← tryCatch (Except.ok <$> conclude cur.1 cur.2 conc R) (fun e => pure (.error e)) then
          return i
      throw err
  -- (constants of different lengths at the heads agree on the shorter)
  let (E, e) ← if k == .const then pure (E, e) else stripConstants E e rev 8
  let .app (.kind .EQUAL) #[t₁, s₁] := E | throw "concat_eq without an equality"
  let some ht := head? t₁ rev | throw "no head"
  let some hs := head? s₁ rev | throw "no head"
  match k with
  | .const =>
    -- constants of the same length at the heads, which differ
    let some wt := word? ht | throw "no constant head"
    let some ws := word? hs | throw "no constant head"
    let l := min wt.length ws.length
    -- `(= t s')`, then `(= s' t)`, then `(= s' t')`
    let (_, e₁) ← splice e l rev
    let (_, _, e₂) ← eqFact (.symm (.assume e₁))
    let (E, e₃) ← splice e₂ l rev
    let .app (.kind .EQUAL) #[x, y] := E | throw "no equality"
    let some hx := head? x rev | throw "no head"
    let some hy := head? y rev | throw "no head"
    let li ← lengthFact R (Node.eqNode (len hx) (len hy))
    let (C, c) ← rule .concat_unify [.node (Node.mkBool rev)] [e₃, li]
    conclude C c conc R
  | .csplit | .cprop =>
    -- the non-constant at the head of `t`, the constant at the head of `s`
    let (e, ht, hs) ← if (word? ht).isSome && (word? hs).isNone then do
        let (_, _, e') ← eqFact (.symm (.assume e))
        pure (e', hs, ht)
      else pure (e, ht, hs)
    let e ← if k == .csplit then pure (← splice e 1 rev).2 else pure e
    let _ := hs
    let li ← lengthFact R (Node.notNode (Node.eqNode (len ht) zero))
    let r := if k == .csplit then CRule.concat_csplit else .concat_cprop
    let (C, c) ← rule r [.node (Node.mkBool rev)] [e, li]
    conclude C c conc R
  | .split =>
    let li ← lengthFact R (Node.notNode (Node.eqNode (len ht) (len hs)))
    let (C, c) ← rule .concat_split [.node (Node.mkBool rev)] [e, li]
    conclude C c conc R
  | .lprop =>
    let li ← lengthFact R (Node.mkNode .GT #[len ht, len hs])
    let (C, c) ← rule .concat_lprop [.node (Node.mkBool rev)] [e, li]
    conclude C c conc R
  | .unify =>
    let li ← lengthFact R (Node.eqNode (len ht) (len hs))
    let (C, c) ← rule .concat_unify [.node (Node.mkBool rev)] [e, li]
    conclude C c conc R
  | .eq | .sr | .ctn | .decompose | .eqRew | .bound => throw "unreachable"

/-- The premises as a formula: their conjunction, or the one premise. -/
def premiseFormula (P : Array Node) : Node :=
  if h : P.size = 1 then P[0] else Node.mkNode .AND P

/-- The intersection inferences (`STRINGS_RE_INTER_INCLUDE`, `_CONF`, `_INFER`),
as cvc5's `InferProofCons`: each membership of the premises as a positive one
(a negative one is a membership in the complement, by their rewrites), over
the first one's string (by the premises' equalities), their intersection by
`re_inter`: the CPC proof of `(=> (premiseFormula P) C)` for `C` the membership
in the intersection, with `C`. Its rewrite to the conclusion (`false`) is left to
the rewriter (`proveFrom`), whose steps Logos does not run. -/
def proveReInter (P : Array Node) : Option (Node × Node × List CCmd) := do
  if P.isEmpty then none
  let h := premiseFormula P
  let act : M Node := do
    let p ← push ⟨.refl, [.node h], [], .assume⟩
    let mut facts : Array Nat := #[]
    if P.size == 1 then facts := #[← known h p]
    else
      for i in [0:P.size] do
        let q ← push ⟨.and_elim, [.term (Term.Numeral i)], [p], .step⟩
        facts := facts.push (← known P[i]! q)
    -- the premises' equalities, as proofs between their sides
    let eqs : Array (Node × Node × Nat) := (P.zip facts).filterMap fun (l, i) => match l with
      | .app (.kind .EQUAL) #[a, b] => some (a, b, i)
      | _ => none
    let some x := P.findSome? fun l => match l with
        | .app (.kind .STRING_IN_REGEXP) #[a, _] => some a
        | .app (.kind .NOT) #[.app (.kind .STRING_IN_REGEXP) #[a, _]] => some a
        | _ => none
      | throw "no membership"
    let toX (a : Node) : Option EqProof :=
      if a == x then none
      else eqs.findSome? fun (l, r, i) =>
        if l == a && r == x then some (EqProof.assume i)
        else if r == a && l == x then some (.symm (.assume i)) else none
    let mut mems : Array (Node × Nat) := #[]
    for (l, i) in P.zip facts do
      let (a, r, pa) ← match l with
        | .app (.kind .STRING_IN_REGEXP) #[a, r] => pure (a, r, atomProof l i)
        | .app (.kind .NOT) #[.app (.kind .STRING_IN_REGEXP) #[a, r]] =>
          -- `(str.in_re a (re.comp r))`, which has the rewrite of `(not atom)`
          let tgt := Node.mkNode .STRING_IN_REGEXP #[a, Node.mkNode .REGEXP_COMPLEMENT #[r]]
          if Telos.rewrite tgt != Telos.rewrite l then throw "a complement that does not rewrite"
          let notTrue : EqProof := .trans (.congAt l #[some (atomProof l i)]) (.rw (Node.notNode Node.mkFalse))
          let (_, j) ← litFact (.trans (.rw tgt) (.trans (.symm (.rw l)) notTrue))
          pure (a, Node.mkNode .REGEXP_COMPLEMENT #[r], atomProof tgt j)
        | _ => continue
      let m := Node.mkNode .STRING_IN_REGEXP #[a, r]
      -- over `x`
      let (_, j) ← match toX a with
        | none => litFact pa
        | some q => litFact (.trans (.symm (.congAt m #[some q, none])) pa)
      mems := mems.push (Node.mkNode .STRING_IN_REGEXP #[x, r], j)
    let some (first, j₀) := mems[0]? | throw "no membership"
    let mut cur := (first, j₀)
    for k in [1:mems.size] do
      let (_, jk) := mems[k]!
      let (C, c) ← rule .re_inter [] [cur.2, jk]
      cur := (C, c)
    if Telos.rewrite cur.1 != Node.mkFalse then throw "an intersection that is not empty"
    let _ ← push ⟨.scope, [], [← posOf cur.2], .pop⟩
    return cur.1
  match (act.run {}).run {} with
  | .ok ((C, _), st) =>
    let cs := toCmds st.steps
    let F := Node.mkNode .IMPLIES #[h, C]
    if (EqProof.check #[] (.valid F cs)).isSome then some (C, F, cs) else none
  | .error _ => none

/-- A conflict of an equality `(= t c)` between a concatenation `t` and a
constant `c` that `t`'s constant components do not fit in, in order
(`STRINGS_F_NCTN`, `STRINGS_N_NCTN`), as cvc5's proof: each component in its
own constant's regular expression (`str-in-re-eval`) or in `(re.* re.allchar)`
(`re-in-sigma-star`), so `t` in their concatenation (`re_concat`), so `c` (by
the equality), which evaluates to `false`. -/
def proveNctn (P : Array Node) : Option (Node × List CCmd) := do
  let #[h] := P | none
  let .app (.kind .EQUAL) #[a, b] := h | none
  let (t, c, flip) := if a.isConst then (b, a, true) else (a, b, false)
  if !c.isConst || t.getKind != .STRING_CONCAT then none
  let act : M Unit := do
    let p ← push ⟨.refl, [.node h], [], .assume⟩
    let e ← known h p
    let mut mems : List Nat := []
    for x in t.getChildren do
      let (_, i) ← if x.isConst then
          rule .str_in_re_eval [.node (Node.eqNode (Node.mkNode .STRING_IN_REGEXP
            #[x, Node.mkNode .STRING_TO_REGEXP #[x]]) Node.mkTrue)] []
        else rule .re_in_sigma_star [.node x] []
      let (_, j) ← rule .true_elim [] [i]
      mems := mems ++ [j]
    let (Mt, m) ← rule .re_concat [] mems
    let .app (.kind .STRING_IN_REGEXP) #[_, R] := Mt | throw "a concatenation of another form"
    let Mc := Node.mkNode .STRING_IN_REGEXP #[c, R]
    -- `(c, t)`, then the membership of `t`
    let ct : EqProof := if flip then .assume e else .symm (.assume e)
    let (_, j) ← litFact (.trans (.congAt Mc #[some ct, none]) (atomProof Mt m))
    let f ← conclude Mc j Node.mkFalse
    let _ ← push ⟨.scope, [], [← posOf f], .pop⟩
  match (act.run {}).run {} with
  | .ok (((), _), st) =>
    let cs := toCmds st.steps
    let F := Node.mkNode .IMPLIES #[h, Node.mkFalse]
    if (EqProof.check #[] (.valid F cs)).isSome then some (F, cs) else none
  | .error _ => none

/-- The inference is one of intersections (`proveReInter`). -/
def isReInter (id : String) : Bool :=
  id == "STRINGS_RE_INTER_INCLUDE" || id == "STRINGS_RE_INTER_CONF" || id == "STRINGS_RE_INTER_INFER"

/-- The inference may have a proof (`prove`). -/
def provable (id : String) (P : Array Node) : Bool :=
  !P.isEmpty && (id == "STRINGS_UNIT_INJ" || (kindOf id).isSome)

/-- **A CPC proof of `(=> (premiseFormula P) conc)`** for the core inference
`id`, which Logos checks. -/
def prove (id : String) (P : Array Node) (conc : Node) : Option (Node × List CCmd) := do
  -- the injectivity of `seq.unit`
  if id == "STRINGS_UNIT_INJ" then
    let #[h] := P | none
    let act : EmitM Unit := do
      let p ← push ⟨.refl, [.node h], [], .assume⟩
      let c ← push ⟨.string_seq_unit_inj, [], [p], .step⟩
      let _ ← push ⟨.scope, [], [c], .pop⟩
    match act.run {} with
    | .ok ((), st) =>
      let F := Node.mkNode .IMPLIES #[h, conc]
      let cs := toCmds st.steps
      return ← if (EqProof.check #[] (.valid F cs)).isSome then some (F, cs) else none
    | .error _ => none
  if (id == "STRINGS_F_NCTN" || id == "STRINGS_N_NCTN") && conc == Node.mkFalse then
    if let some r := proveNctn P then return r
  let k ← kindOf id
  if P.isEmpty then none
  let h := premiseFormula P
  let F := Node.mkNode .IMPLIES #[h, conc]
  -- a prefix conflict: each membership in a concatenation gives the equality
  -- of its unfolding (`re_unfold_pos`, then its first conjunct), as cvc5's
  -- proof does; they are known facts after the premises
  let isPrefix := id == "STRINGS_PREFIX_CONFLICT" || id == "STRINGS_PREFIX_CONFLICT_MIN"
  let unfolds : Array (Nat × Bool) := if !isPrefix then #[] else
    (List.range P.size).toArray.filterMap fun i => match P[i]! with
      | m@(.app (.kind .STRING_IN_REGEXP) #[_, .app (.kind .REGEXP_CONCAT) _]) =>
        match Strings.reduceRegExpPos m with
        | some (.app (.kind .AND) _) => some (i, true)
        | some (.app (.kind .EQUAL) _) => some (i, false)
        | _ => none
      | _ => none
  let derived : Array Nat := Id.run do
    let mut out := #[]
    let mut next := P.size
    for (_, isAnd) in unfolds do
      if isAnd then
        out := out.push (next + 1)
        next := next + 2
      else
        out := out.push next
        next := next + 1
    return out
  let total := P.size + unfolds.foldl (fun a (_, isAnd) => a + (if isAnd then 2 else 1)) 0
  let mains := ((List.range P.size).filter fun i => match P[i]! with
    | .app (.kind .EQUAL) #[x, _] => Strings.isStringLike x
    | _ => false) ++ derived.toList
  let tries := mains.flatMap fun m => [false, true].flatMap fun rev => [false, true].map fun flip => (k, m, rev, flip)
  -- (substitution and rewriting: for a conflict, each main equality; else once)
  let srTries := if conc == Node.mkFalse then mains.map fun m => (Kind.sr, m, false, false) else [(Kind.sr, 0, false, false)]
  let tries := if k == .sr then srTries
    else if k == .bound then (k, 0, false, false) :: srTries
    else if k == .ctn || k == .decompose || k == .eqRew then [(k, 0, false, false)] else tries ++ srTries
  -- (the second order only for small inferences: an attempt can be costly)
  let orders : List Known := if P.size ≤ 8 then [{}, { largest := true }, { largest := true, byReplaced := true }]
    else [{}]
  let orders := if k == .eq then orders ++ [{ keepVars := true }] else orders
  orders.findSome? fun cfg => tries.findSome? fun (k, m, rev, flip) =>
    let act : M Unit := do
      let p ← push ⟨.refl, [.node h], [], .assume⟩
      if P.size == 1 then let _ ← known h p
      else
        for i in [0:P.size] do
          let q ← push ⟨.and_elim, [.term (Term.Numeral i)], [p], .step⟩
          let _ ← known P[i]! q
      for (i, isAnd) in unfolds do
        let (_, j) ← rule .re_unfold_pos [] [i]
        if isAnd then let _ ← rule .and_elim [.term (Term.Numeral 0)] [j]
      let c ← coreSteps k total m flip rev conc
      let _ ← push ⟨.scope, [], [← posOf c], .pop⟩
    match (act.run cfg).run {} with
    | .ok (((), _), st) =>
      let cs := toCmds st.steps
      if (EqProof.check #[] (.valid F cs)).isSome then some (F, cs) else none
    | .error _ => none

/-! ## Using the proofs -/

/-- A proof of `((and l₁ … lₙ), true)` (of `(l₁, true)` for one) from proofs of
each `(lᵢ, true)`: congruence, then the rewrite of `(and true … true)`. -/
def andIntro (P : Array Node) (ps : Array EqProof) : Option EqProof := do
  if P.size != ps.size || P.isEmpty then none
  if h : ps.size = 1 then return ps[0]
  let F := premiseFormula P
  let t := Node.mkNode .AND (P.map fun _ => Node.mkTrue)
  some (.trans (.congAt F (ps.map some)) (.rw t))

/-- A proof of `(C, true)` from one of `(F, true)`, for `F = (=> H C)`, and one
of `(H, true)`: congruence gives `((=> true C), true)`, which has the rewrite
of `C`. -/
def modusPonens (F : Node) (pF pH : EqProof) : Option EqProof := do
  let .app (.kind .IMPLIES) #[_, C] := F | none
  let t := Node.mkNode .IMPLIES #[Node.mkTrue, C]
  if Telos.rewrite t != Telos.rewrite C then none
  let q : EqProof := .trans (.symm (.congAt F #[some pH, none])) pF
  some (.trans (.trans (.rw C) (.symm (.rw t))) q)

/-- A proof of the conclusion of a core inference, from its CPC proof (`prove`)
and proofs of `(pᵢ, true)` for its premises `P`. -/
def proveFromProof (proof : Option (Node × List CCmd)) (P : Array Node) (ps : Array EqProof) : Option EqProof := do
  let (F, cs) ← proof
  let pH ← andIntro P ps
  modusPonens F (.valid F cs) pH

/-- A proof of `(conc, true)` from proofs of `(pᵢ, true)` for the premises `P`
of the core inference `id`. -/
def proveFrom (id : String) (P : Array Node) (ps : Array EqProof) (conc : Node) : Option EqProof := do
  if isReInter id then
    if conc != Node.mkFalse then none
    let (C, F, cs) ← proveReInter P
    let q ← proveFromProof (some (F, cs)) P ps
    -- `(false, C)`, then `(C, true)`
    return .trans (.symm (.rw C)) q
  proveFromProof (prove id P conc) P ps

/-- The CPC proof of `(=> h conc)`, for `h` the conjunction of `E`, from a proof
of `(conc, true)` (`(x, false)` for `conc` the negation of `x`) from `E`. -/
def discharge (E : Array Node) (h conc : Node) (q : EqProof) : Option (List CCmd) := do
  let act : M Unit := do
    let p ← push ⟨.refl, [.node h], [], .assume⟩
    if E.size == 1 then let _ ← known h p
    else
      for i in [0:E.size] do
        let r ← push ⟨.and_elim, [.term (Term.Numeral i)], [p], .step⟩
        let _ ← known E[i]! r
    let (F, c) ← litFact q
    if F != conc then throw "a conclusion of another form"
    let _ ← push ⟨.scope, [], [← posOf c], .pop⟩
  match (act.run {}).run {} with
  | .ok (((), _), st) =>
    let cs := toCmds st.steps
    if (EqProof.check #[] (.valid (Node.mkNode .IMPLIES #[h, conc]) cs)).isSome then some cs else none
  | .error _ => none

end Telos.Solver.StringsCore
