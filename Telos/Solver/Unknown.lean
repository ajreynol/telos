/-!
# Why an answer is `unknown`

Every `unknown` of the solver carries an `Unknown`, which says whether it is
**intentional**, an incompleteness that cvc5 itself declares at the same point
(a theory's `setModelUnsound` or `setIncomplete` with an `IncompleteId`), or
not:
- a part of cvc5 that telos does not port, so that cvc5 would decide the
  benchmark (`notPorted`);
- a certificate that did not check: a `sat` whose model does not satisfy the
  input (`modelFalse`, a bug of the solver or of the model builder;
  `modelNotEvaluated`, a gap of the model evaluator), or an `unsat` whose
  refutation needs lemmas without a certificate (`missingProof`), or whose
  certificate does not check (`badJustification`, `certBroken`, bugs);
- an input outside what telos handles (`unsupported`), or an internal failure
  (`internal`).

The goal is that only intentional ones remain, as in cvc5, on the inputs telos
supports.
-/

namespace Telos.Solver

/-- cvc5's `IncompleteId` (`src/theory/incomplete_id.h`): those its theories
can declare in safe mode. -/
inductive IncompleteId where
  | ARITH_NL
  | QUANTIFIERS
  | QUANTIFIERS_CEGQI
  | QUANTIFIERS_RECORDED_INST
  | QUANTIFIERS_MAX_INST_ROUNDS
  | STRINGS_LOOP_SKIP
  | STRINGS_REGEXP_NO_SIMPLIFY
  | UNPROCESSED_THEORY_CONFLICT
  | STOP_SEARCH
  deriving DecidableEq, Repr, Inhabited

namespace IncompleteId

def all : List IncompleteId :=
  [.ARITH_NL, .QUANTIFIERS, .QUANTIFIERS_CEGQI, .QUANTIFIERS_RECORDED_INST, .QUANTIFIERS_MAX_INST_ROUNDS,
   .STRINGS_LOOP_SKIP, .STRINGS_REGEXP_NO_SIMPLIFY, .UNPROCESSED_THEORY_CONFLICT, .STOP_SEARCH]

def name : IncompleteId → String
  | .ARITH_NL => "ARITH_NL"
  | .QUANTIFIERS => "QUANTIFIERS"
  | .QUANTIFIERS_CEGQI => "QUANTIFIERS_CEGQI"
  | .QUANTIFIERS_RECORDED_INST => "QUANTIFIERS_RECORDED_INST"
  | .QUANTIFIERS_MAX_INST_ROUNDS => "QUANTIFIERS_MAX_INST_ROUNDS"
  | .STRINGS_LOOP_SKIP => "STRINGS_LOOP_SKIP"
  | .STRINGS_REGEXP_NO_SIMPLIFY => "STRINGS_REGEXP_NO_SIMPLIFY"
  | .UNPROCESSED_THEORY_CONFLICT => "UNPROCESSED_THEORY_CONFLICT"
  | .STOP_SEARCH => "STOP_SEARCH"

def ofName? (s : String) : Option IncompleteId := all.find? (·.name == s)

end IncompleteId

/-- Why an answer is `unknown`. -/
inductive Unknown where
  /-- cvc5 makes the same call: the theory declared the model unsound or the
  check incomplete, with this id. -/
  | intentional (theory : String) (id : IncompleteId)
  /-- A part of cvc5 that telos does not port (a theory, a stage of one, an
  operator the engine treats as uninterpreted). -/
  | notPorted (what : String)
  /-- The engine alone stopped at a lemma: the SAT solver is needed (retried). -/
  | needsSat
  /-- A `sat` whose model makes an assertion false. -/
  | modelFalse (detail : String)
  /-- A `sat` whose model the evaluator cannot evaluate. -/
  | modelNotEvaluated (detail : String)
  /-- An `unsat` whose refutation needs these lemmas or conflicts, which have
  no certificate. -/
  | missingProof (lemmas : List String)
  /-- An `unsat` with a clause whose certificate does not check. -/
  | badJustification (detail : String)
  /-- An `unsat` whose refutation does not follow from its clauses. -/
  | certBroken (detail : String)
  /-- The input is outside what telos handles. -/
  | unsupported (detail : String)
  /-- An internal failure. -/
  | internal (detail : String)
  deriving Inhabited, Repr

namespace Unknown

/-- The stable code of a reason (printed as `[code]`). -/
def code : Unknown → String
  | .intentional .. => "intentional"
  | .notPorted _ => "not-ported"
  | .needsSat => "needs-sat"
  | .modelFalse _ => "cert-sat/model-false"
  | .modelNotEvaluated _ => "cert-sat/not-evaluated"
  | .missingProof _ => "cert-unsat/missing-proof"
  | .badJustification _ => "cert-unsat/bad-justification"
  | .certBroken _ => "cert-unsat/broken"
  | .unsupported _ => "unsupported"
  | .internal _ => "internal"

def detail : Unknown → String
  | .intentional T id => s!"{T} declared the model incomplete ({id.name}), as cvc5 does"
  | .notPorted w => w
  | .needsSat => "the engine alone stopped at a lemma"
  | .modelFalse d | .modelNotEvaluated d | .badJustification d | .certBroken d
  | .unsupported d | .internal d => d
  | .missingProof ls => s!"the refutation needs clauses with no certificate, of: {", ".intercalate ls}"

def message (w : Unknown) : String := s!"[{w.code}] {w.detail}"

/-- An incompleteness that cvc5 declares too. -/
def isIntentional : Unknown → Bool
  | .intentional .. => true
  | _ => false

/-- A certificate that did not check (of a `sat` or an `unsat`). -/
def isCertFailure : Unknown → Bool
  | .modelFalse _ | .modelNotEvaluated _ | .missingProof _ | .badJustification _ | .certBroken _ => true
  | _ => false

end Unknown

end Telos.Solver
