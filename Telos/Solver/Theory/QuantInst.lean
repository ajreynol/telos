import Telos.Solver.Theory.QuantConflictFind
import Telos.Solver.Theory.QuantTrigger
import Telos.Solver.Theory.QuantAlpha

/-!
# The quantifiers engine's state, and instantiation

The state of cvc5's quantifiers engine beyond the term database (the
information of conflict-based instantiation, the data of E-matching), what a
call of the engine gives back, and the instantiation manager
(`Instantiate::addInstantiation`): instantiations are skipped when the
instance is entailed (`inst-no-entail`) or recorded, and the lemma
`(=> q body)` is rewritten and sent once (the inference manager's cache).
-/

namespace Telos.Solver.Quant

/-- The quantifiers engine's state. -/
structure Eng where
  st : State := {}
  /-- The information of each registered formula (`d_qinfo`, user context). -/
  qinfo : Std.HashMap Key QInfo := {}
  /-- `d_func_rel_dom`: the formulas whose propagating variables have each
  operator. -/
  funcRelDom : Std.HashMap Key (Array Node) := {}
  /-- E-matching (`QuantTrigger.lean`). -/
  em : EmData := {}
  /-- Alpha-equivalence (`QuantAlpha.lean`). -/
  alpha : AlphaDb := {}
  /-- The nodes made while solving, numbered (the equality engine's
  `freshIds`, given and taken back by each call). -/
  fresh : Std.HashMap Key Nat := {}
  deriving Inhabited

/-- A trigger made (`-o trigger`): its formula, its terms, and its tag
(`simple`, `multi`, or none); or a formula with no trigger (`no-trigger`). -/
inductive TrigOut where
  | trigger (q : Node) (nodes : Array Node) (tag : String) (user : Bool := false)
  | noTrigger (q : Node)
  deriving Inhabited

/-- What a call of the engine gives back. -/
structure Out where
  lemmas : Array Lemma := #[]
  /-- The skolems created, in order. -/
  skolems : Array Node := #[]
  /-- The model is unsound (`setModelUnsound`, `QUANTIFIERS`). -/
  modelUnsound : Bool := false
  /-- Another check is asked for (`markUsed`). -/
  markUsed : Bool := false
  /-- With the number of lemmas before each. -/
  triggers : Array (Nat × TrigOut) := #[]
  deriving Inhabited

abbrev EM := StateT Eng (StateT Out (ReaderT Ctx Id))

def ectx : EM Ctx := (read : ReaderT Ctx Id Ctx)

/-- Run an operation of the term database and the round's data. -/
def runM (rd : Round) (x : M α) : EM (α × Round) := do
  let c ← ectx
  let e ← get
  let (a, s) := (x.run c).run { st := e.st, rd }
  set { e with st := s.st }
  return (a, s.rd)

/-- Send a lemma, unless it was sent (up to rewriting: the lemmas are
rewritten). The cache starts with `true` (`TheoryInferenceManager`), so a
lemma that rewrites to `true` is not sent. -/
def emitLemma (l : Lemma) : EM Bool := do
  let e ← get
  if l.lem == Node.mkTrue || e.st.lemmaCache.contains ⟨l.lem⟩ then return false
  set { e with st := { e.st with lemmaCache := e.st.lemmaCache.insert ⟨l.lem⟩ } }
  modifyThe Out fun o => { o with lemmas := o.lemmas.push l }
  return true

/-- `Instantiate::addInstantiation`: false if the instance is entailed, recorded,
or its lemma was sent. -/
def addInstantiation (rd : Round) (q : Node) (terms : Array Node) (id : String) : EM (Bool × Round) := do
  let vs := quantVars q
  let subs : Subs := (vs.zip terms).foldl (fun m (v, t) => m.insert ⟨v⟩ t) {}
  let (ent, rd) ← runM rd (isEntailed (quantBody q) subs false true)
  if ent then return (false, rd)
  let key : Key := ⟨Node.mkNode .AND (#[q] ++ terms)⟩
  if (← get).st.insts.contains key then return (false, rd)
  modify fun e => { e with st := { e.st with insts := e.st.insts.insert key } }
  let body := substitute vs terms (quantBody q)
  let c ← ectx
  let lem₀ := Node.mkNode .IMPLIES #[q, body]
  -- the instance's nodes, made by the substitution, numbered (children first),
  -- then the lemma rewritten at that order
  let fresh := c.order.numberFreshRewrite (← get).fresh lem₀
  modify fun e => { e with fresh }
  let o := { c.order with fresh }
  let lem := c.rewriteAt o lem₀
  return (← emitLemma { id, lem, inst := some (q, terms, lem₀), order := some o }, rd)

/-- `QuantifiersEngine::reduceQuantifier`: `q` is alpha-equivalent to a formula
registered before, `q'`: the lemma `(= q' q)` (`QUANTIFIERS_REDUCE_ALPHA_EQ`),
and `q` is reduced. Once per formula (user context). -/
def reduceQuantifier (q : Node) : EM Bool := do
  if let some b := (← get).alpha.red.get? ⟨q⟩ then return b
  let c ← ectx
  let key := alphaKey c.lt (quantVars q) (quantBody q)
  let red ← match (← get).alpha.trie.get? key with
    | some q' =>
      if q' != q then
        let _ ← emitLemma { id := "QUANTIFIERS_REDUCE_ALPHA_EQ", lem := Node.eqNode q' q }
        pure true
      else pure false
    | none =>
      modify fun e => { e with alpha := { e.alpha with trie := e.alpha.trie.insert key q } }
      pure false
  modify fun e => { e with alpha := { e.alpha with red := e.alpha.red.insert ⟨q⟩ red } }
  return red

/-- `FirstOrderModel::markRelevant`. -/
def markRelevant (q : Node) : EM Unit :=
  modify fun e =>
    if e.st.lastRlv == some q then e else
    { e with st := { e.st with rlvVec := (e.st.rlvVec.filter (· != q)).push q, lastRlv := some q } }

/-- The asserted formulas in the order of relevance (`reset_round`). -/
def orderedAsserted : EM (Array Node) := do
  let st := (← get).st
  if st.rlvVec.isEmpty then return st.asserted
  let mut rest := st.asserted
  let mut out := #[]
  for i in [0:st.rlvVec.size] do
    let q := st.rlvVec[st.rlvVec.size - 1 - i]!
    if rest.contains q then
      out := out.push q
      rest := rest.erase q
  return out ++ st.asserted.filter fun q => !out.contains q

end Telos.Solver.Quant
