# Tests

Each directory tests one part of telos, with inputs (`.smt2`) and the output
telos must give (`.expected`), checked by CI:

| directory | what it tests | how it is run |
|---|---|---|
| `rewriter/` | the rewriter: `(simplify t)` queries, one theory per file | `telos FILE` |
| `rewriter/cvc5-holes/`, `rewriter/cvc5-trust/` | rewrites that cvc5 has no proof of (see their READMEs) | `telos FILE`, `scripts/check-proofs.py` |
| `preprocess/` | the preprocessor, as cvc5's `-o post-asserts` | `telos --post-asserts FILE` (and with `--proof --check-proof`) |
| `theory-events/` | the theory engine, event by event against cvc5's recorded traces (`.cvc5`) | `telos --theory-events FILE`, `scripts/fuzz-solve.py --recorded --strict` |
| `replay/` | the theories fed cvc5's own trace (`.trace`) | `telos --replay FILE.trace FILE.smt2` |
| `solve/` | telos as an SMT solver: answers, models, `get-value`, errors, and full proofs | `telos [OPTIONS] FILE`, `scripts/check-full-proofs.py` |

The proofs are checked with Ethos, which CI does not install:
`scripts/check-proofs.py test/rewriter/*.smt2` for rewrites,
`scripts/fuzz-pp.py --proofs` for preprocessing, and
`scripts/check-full-proofs.py test/solve/*.smt2 test/theory-events/*.smt2` for
the full proofs of `unsat`.
