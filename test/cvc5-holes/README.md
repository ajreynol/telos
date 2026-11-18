# cvc5 rewrites without proofs

Each file asserts the negation of one rewrite `(= t s)` that cvc5's rewriter
makes. cvc5's proof of it, at `--proof-granularity=dsl-rewrite`, has a `trust`
step: a proof hole. To check one:

```
cvc5 --dump-proofs --proof-granularity=dsl-rewrite --proof-format=cpc FILE | grep -B1 ':rule trust'
```

or run with `--check-proofs-complete`, which fails on the trusted step. Each file's
first lines name the rewrite in `SequencesRewriter`/`ArithRewriter` and say what
is missing.

They were found with `scripts/find-holes.py`, against cvc5 `bab27e4f17`. Logos
`512983a8` (the pinned commit) adds rules for all of them but `idof-norm-prefix`,
and telos proves those, with the same result as cvc5 up to the orientation of
equalities. cvc5 PR #13167 fills these holes in cvc5, and moves
`IDOF_NORM_PREFIX` to the extended rewriter.

## No CPC rule in cvc5 `bab27e4f17`

| File | cvc5 rewrite | Logos `512983a8` rule |
|---|---|---|
| `ctn-repl-len-one-to-ctn` | `CTN_REPL_LEN_ONE_TO_CTN` when `\|z\| <= 1` (the old rule requires `= 1`) | `str-contains-repl-self-tgt-leq-one` |
| `idof-len` | `IDOF_LEN` | `str-indexof-len` |
| `idof-strip-sym-len` | `IDOF_STRIP_SYM_LEN` | `str-indexof-strip-prefix-len`, `str-indexof-strip-sym-len` |
| `idof-norm-prefix` | `IDOF_NORM_PREFIX` | none (telos leaves it unchanged) |
| `idof-strip-cnst-endpts` | `IDOF_STRIP_CNST_ENDPTS` | `str-indexof-strip-char-pre` |
| `re-char-in-str-star` | `RE_CHAR_IN_STR_STAR` | `re-char-in-str-star` |
| `ctn-strip-endpt-from-int` | `CTN_STRIP_ENDPT` past a `str.from_int` (`str-overlap-endpoints-ctn` needs constants) | `str-contains-strip-from-int-pre/post` |
| `ctn-split-const` | `CTN_SPLIT` with a constant first argument | `str-contains-cnst-split-leq-one` |
| `str-leq-id` | `STR_LEQ_ID` | `str-leq-id` |
| `arith-div-int-const` | `(/ c y)` → `(/ c.0 (to_real y))` for Int `c`, `y` | `arith-div-int-to-real` |

## CPC has the rules; cvc5's reconstruction fails

| File | cvc5 rewrite | telos |
|---|---|---|
| `re-inter-const-const-conflict` | `RE_INTER_CONST_CONST_CONFLICT` | `re-inter-const-const-conflict` |
| `arith-int-geq-tighten-coeff` | tightening with a rational coefficient | `arith_poly_norm_rel`, `arith-int-geq-tighten` |
| `arith-int-eq-coeff-false` | integer equality with no integer solution | proved |
| `re-andor-const-remove-inter` | `RE_ANDOR_CONST_REMOVE` (the elaborator handles only results that are `str.to_re` or `re.none`) | `re-inter-const-elim` (Logos `512983a8`) |
| `re-andor-const-remove-union` | `RE_ANDOR_CONST_REMOVE` (`re-union-const-elim`) | `re-union-const-elim` with a list (Logos `512983a8`) |

Not listed: `bvite` with a constant condition and `/`, `/_total` and `is_int`
over `to_real`. The rules for these are in Logos (`bv-ite-const-cond-1/2`,
`arith-div-int-to-real`, `arith-div-total-int-to-real`) but not in this cvc5.
