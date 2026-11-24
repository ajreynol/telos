# Solving, as an SMT solver

Each `NAME.smt2` is a script that `telos NAME.smt2` runs as cvc5 would
(`Telos/Frontend/Run.lean`); `NAME.expected` is its standard output. A line
`; telos: OPTIONS` gives the options to run it with (`--dump-models`).

- `models`, `dump-models`: models and values, printed as cvc5 prints them;
- `strings-bounded`: reductions with bounded quantified formulas;
- `strings-extended`, `proof-strings-extended`: extended functions of strings
  (reductions, a model, a full proof);
- `notations`, `notations-binder`: SMT-LIB notations read as cvc5 reads them
  (`define-sort`, `define-const`, `:named`, quoted symbols, legacy testers,
  `divisible`, numerals bound by `let` or quantifiers);
- `commands`: the errors cvc5 gives without model or proof generation, `echo`,
  `get-info`;
- `unknown-reason`: an `unknown`, with `:reason-unknown` (telos says why on
  standard error);
- `proof-*`: `unsat` answers whose full CPC proofs (`--dump-proofs`) go through
  preprocessing, the CNF translation, a theory (Boolean, UF, LRA, LIA,
  datatypes, strings) and resolution. `scripts/check-full-proofs.py
  test/solve/*.smt2` checks them with Ethos.
