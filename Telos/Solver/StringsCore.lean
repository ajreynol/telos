import Telos.Solver.DtLemma
import Telos.Core.Node.OfEo
import Telos.Preprocess.Theory.StringsStaticRewrite
import Telos.Solver.Theory.StringsRegexOps

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
  deriving Inhabited

abbrev M := StateT Known EmitM

/-- Record a fact `F` proven at step `p`: its index among the known facts. -/
def known (F : Node) (p : Nat) : M Nat :=
  modifyGet fun k => (k.A.size, { k with A := k.A.push F, pos := k.pos.push p, env := k.env ++ F.vars })

def posOf (i : Nat) : M Nat := do
  let some p := (← get).pos[i]? | throw "a fact out of range"
  return p

/-- The last fact proven, read back from Logos. -/
def lastFact : M Node := do
  let st ← getThe EmitState
  let cmds := (toCmds st.steps).foldr CCmdList.cons CCmdList.nil
  let t := __eo_state_proven_nth (runFromEmpty cmds) 0
  let some n := Node.ofEo (← get).env t | throw "a conclusion that does not read back"
  return n

/-- Apply a CPC rule to known facts: its conclusion becomes known. -/
def rule (r : CRule) (args : List PArg) (prems : List Nat) : M (Node × Nat) := do
  let ps ← prems.mapM posOf
  let p ← push ⟨r, args, ps, .step⟩
  let F ← lastFact
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

def mkConcat (cs : Array Node) : Node :=
  if h : cs.size = 1 then cs[0] else if cs.isEmpty then emptyStr else Node.mkNode .STRING_CONCAT cs

def word? (t : Node) : Option (List Nat) :=
  match t with
  | .const (.string w) => some w
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

/-- `t` with each subterm `x` replaced by `y`, for the known equality `(= x y)`
at index `i` (oriented by `flip`), and its proof. -/
partial def substOne (x y : Node) (p : EqProof) (t : Node) : Option EqProof :=
  if t == x then some p else
  match t with
  | .app _ cs =>
    let args := cs.map (substOne x y p)
    if args.all (·.isNone) then none else some (.congAt t args)
  | _ => none

/-- `(t, t')` for `t'` the rewrite of `t` with the substitution of the known
equalities `R` applied in turn (`SBA_SEQUENTIAL`). -/
def substRw (R : Array Nat) (t : Node) : M (Node × Option EqProof) := do
  let A := (← get).A
  let mut cur := t
  let mut acc : Option EqProof := none
  -- in turn, until nothing changes (an equality may bring a term that an
  -- earlier one replaces)
  for _ in [0:R.size + 1] do
    let mut changed := false
    for i in R do
      let some (.app (.kind .EQUAL) #[x, y]) := A[i]? | continue
      -- (a constant replaces the other side)
      let (x, y, p) : Node × Node × EqProof :=
        if x.isConst && !y.isConst then (y, x, .symm (.assume i)) else (x, y, .assume i)
      if let some q := substOne x y p cur then
        let some (_, c') := EqProof.check A q | continue
        cur := c'
        acc := compose acc (some q)
        changed := true
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
      if t == emptyStr && s.typeHint == some .string then
        let _ ← rule .string_length_non_empty [] [i]
      else if s == emptyStr && t.typeHint == some .string then
        let (_, j) ← eqFact (.symm (.assume i))
        let _ := j
        pure ()
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
  | csplit | cprop | split | lprop | unify | const | eq
  /-- Substitution and rewriting: the main equality rewrites to `false` (a
  conflict), or the conclusion to `true`. -/
  | sr
  deriving BEq, Inhabited

def kindOf (id : String) : Option Kind :=
  match id with
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
def conclude (C : Node) (j : Nat) (conc : Node) : M Nat := do
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
  let some q := bridge C conc | throw "a conclusion that does not bridge"
  let q := match q with
    | some q => EqProof.trans (.symm q) pc
    | none => pc
  let (F, i) ← litFact q
  if F != conc then throw "a conclusion of another form"
  return i

/-- The steps of the inference from the known premises: the main equality
`m` (oriented by `flip`), in the direction `rev`. The index of `conc`. -/
def coreSteps (k : Kind) (n : Nat) (m : Nat) (flip rev : Bool) (conc : Node) : M Nat := do
  let A := (← get).A
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
      let (r, q) ← substRw R atom
      if r != Node.mkBool pol then throw "a conclusion that does not rewrite"
      let some q := q | throw "a conclusion that does not rewrite"
      let (F, i) ← litFact q
      if F != conc then throw "a conclusion of another form"
      return i
    let (F, i) ← litFact q
    if F != conc then throw "a conclusion of another form"
    return i
  let some (.app (.kind .EQUAL) #[a, b]) := A[m]? | throw "a main equality that is not one"
  let R := ((List.range n).filter fun i => i != m && match A[i]! with
    | .app (.kind .EQUAL) #[x, _] => x.typeHint == some .string
    | _ => false).toArray
  nonEmptyLengths
  -- the main equality, with the substitution and rewritten
  let (t, qa) ← substRw R (if flip then b else a)
  let (s, qb) ← substRw R (if flip then a else b)
  let main : EqProof := if flip then .symm (.assume m) else .assume m
  let q := compose (qa.map .symm) (compose (some main) qb)
  let (_, _, e₀) ← eqFact (q.getD main)
  if t == s then throw "a main equality that is trivial"
  if k == .sr then return ← conclude (Node.eqNode t s) e₀ conc
  -- the common prefix stripped
  let (E, e) ← rule .concat_eq [.node (Node.mkBool rev)] [e₀]
  if k == .eq then return ← conclude E e conc
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
    conclude C c conc
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
    conclude C c conc
  | .split =>
    let li ← lengthFact R (Node.notNode (Node.eqNode (len ht) (len hs)))
    let (C, c) ← rule .concat_split [.node (Node.mkBool rev)] [e, li]
    conclude C c conc
  | .lprop =>
    let li ← lengthFact R (Node.mkNode .GT #[len ht, len hs])
    let (C, c) ← rule .concat_lprop [.node (Node.mkBool rev)] [e, li]
    conclude C c conc
  | .unify =>
    let li ← lengthFact R (Node.eqNode (len ht) (len hs))
    let (C, c) ← rule .concat_unify [.node (Node.mkBool rev)] [e, li]
    conclude C c conc
  | .eq | .sr => throw "unreachable"

/-- The premises as a formula: their conjunction, or the one premise. -/
def premiseFormula (P : Array Node) : Node :=
  if h : P.size = 1 then P[0] else Node.mkNode .AND P

/-- The intersection inferences (`STRINGS_RE_INTER_INCLUDE`, `_CONF`, `_INFER`),
as cvc5's `InferProofCons`: each membership of the premises as a positive one
(a negative one is a membership in the complement, by their rewrites), over
the first one's string (by the premises' equalities), their intersection by
`re_inter`, and its rewrite to the conclusion (`false`). -/
partial def hasReInter (n : Node) : Bool :=
  n.getKind == .REGEXP_INTER || n.getChildren.any hasReInter

def proveReInter (P : Array Node) (conc : Node) : Option (Node × List CCmd) := do
  if P.isEmpty || conc != Node.mkFalse then none
  -- (a guard: the inclusion is decided by CPC's `$str_re_includes`, run by
  -- Logos, whose search over intersections nested in concatenations is
  -- exponential without cvc5's cache; such a conflict stays uncertified)
  if P.any hasReInter then none
  let h := premiseFormula P
  let F := Node.mkNode .IMPLIES #[h, conc]
  let act : M Unit := do
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
    let c ← conclude cur.1 cur.2 conc
    let _ ← push ⟨.scope, [], [← posOf c], .pop⟩
  match (act.run {}).run {} with
  | .ok (((), _), st) =>
    let cs := toCmds st.steps
    if (EqProof.check #[] (.valid F cs)).isSome then some (F, cs) else none
  | .error _ => none

/-- **A CPC proof of `(=> (premiseFormula P) conc)`** for the core inference
`id`, which Logos checks. -/
def prove (id : String) (P : Array Node) (conc : Node) : Option (Node × List CCmd) := do
  if id == "STRINGS_RE_INTER_INCLUDE" || id == "STRINGS_RE_INTER_CONF" || id == "STRINGS_RE_INTER_INFER" then
    return ← proveReInter P conc
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
    | .app (.kind .EQUAL) #[x, _] => x.typeHint == some .string
    | _ => false) ++ derived.toList
  let tries := mains.flatMap fun m => [false, true].flatMap fun rev => [false, true].map fun flip => (k, m, rev, flip)
  -- (substitution and rewriting: for a conflict, each main equality; else once)
  let srTries := if conc == Node.mkFalse then mains.map fun m => (Kind.sr, m, false, false) else [(Kind.sr, 0, false, false)]
  let tries := if k == .sr then srTries else tries ++ srTries
  tries.findSome? fun (k, m, rev, flip) =>
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
    match (act.run {}).run {} with
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

/-- A proof of `(conc, true)` from proofs of `(pᵢ, true)` for the premises `P`
of the core inference `id`. -/
def proveFrom (id : String) (P : Array Node) (ps : Array EqProof) (conc : Node) : Option EqProof := do
  let (F, cs) ← prove id P conc
  let pH ← andIntro P ps
  modusPonens F (.valid F cs) pH

end Telos.Solver.StringsCore
