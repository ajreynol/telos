#!/usr/bin/env python3
"""Find rewrites that cvc5 cannot prove: trusted steps in its rewrite proofs.

Runs `telos-fuzz SEED COUNT DEPTH MODE` for random terms, asks cvc5 for the
rewrite `s` of each term `t`, then asks cvc5 to prove `(= t s)` at DSL-rewrite
granularity. Every `trust` step in a proof is a rewrite that cvc5 takes without
a proof rule (a proof hole). For each, the trusted equality `(= l r)` is
re-checked on its own; the ones still trusted are grouped by the theory and the
operators at the top of `l` and `r`, and one reproducer per group, the smallest,
is written to `OUT/<theory>-<op>-<n>.smt2`.

Usage:
  CVC5=PATH scripts/find-holes.py [--seed N] [--count N] [--depth N] [--jobs N]
                                  [--out DIR] [MODE ...]

MODE is one of telos-fuzz's modes (bool, arith, uf, bv, arrays, mixed, strings);
the default is all of them. Build the fuzzer first: `lake build telos telos-fuzz`.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fuzz import FUZZ, PRELUDE, parse_sexpr  # noqa: E402

MODES = ["bool", "arith", "uf", "bv", "arrays", "mixed", "strings"]
PROOF_OPTS = ["--dump-proofs", "--proof-granularity=dsl-rewrite", "--proof-format=cpc",
              "--tlimit-per=5000"]


def cvc5(binary, script, extra=()):
    out = subprocess.run([binary, "--lang", "smt2", "--print-arith-lit-token", *extra],
                         input=script, capture_output=True, text=True, check=False)
    return out.stdout


def unparse(e):
    return e if isinstance(e, str) else "(" + " ".join(unparse(x) for x in e) + ")"


def trusted_steps(proof):
    """The (trust id, formula) of each trust step in a CPC proof, with the
    `@t` definitions expanded, and the declarations of the proof."""
    defs, decls, steps, last_id = {}, [], [], None
    for line in proof.splitlines():
        if line.startswith("(declare-") :
            decls.append(line)
        elif m := re.match(r"\(define (@t\d+) \(\) (.*)\)$", line):
            defs[m.group(1)] = m.group(2)
        elif m := re.match(r"; trust (\S+)", line):
            last_id = m.group(1)
        elif m := re.match(r"\(step @p\d+ :rule trust :premises \(.*?\) :args \((.*)\)\)$", line):
            steps.append((last_id, m.group(1)))

    def expand(s):
        while True:
            s2 = re.sub(r"@t\d+", lambda m: defs.get(m.group(0), m.group(0)), s)
            if s2 == s:
                return s
            s = s2

    return [(tid, expand(f)) for tid, f in steps], decls


def head(e):
    if isinstance(e, str):
        return "const" if re.match(r'^[-0-9"#]', e) or e in ("true", "false") else "var"
    return unparse(e[0]) if isinstance(e[0], str) else unparse(e[0])


def size(e):
    return 1 if isinstance(e, str) else sum(size(x) for x in e)


def check_formula(binary, decls, formula):
    """The trust steps of cvc5's proof that the equality `formula` holds."""
    script = "(set-logic ALL)\n" + "\n".join(decls) + f"\n(assert (not {formula}))\n(check-sat)\n"
    out = cvc5(binary, script, PROOF_OPTS)
    if not out.startswith("unsat"):
        return None, script
    return trusted_steps(out)[0], script


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cvc5", default=os.environ.get("CVC5") or shutil.which("cvc5") or "cvc5")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=300)
    ap.add_argument("--depth", type=int, default=3)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("--out", default="holes")
    ap.add_argument("modes", nargs="*", default=MODES)
    a = ap.parse_args()
    if not FUZZ.exists():
        sys.exit("error: build the fuzzer first: lake build telos telos-fuzz")

    terms = []
    for mode in a.modes:
        args = [str(FUZZ), str(a.seed), str(a.count), str(a.depth)] + ([] if mode == "bool" else [mode])
        lines = subprocess.run(args, capture_output=True, text=True, check=True).stdout.splitlines()
        terms += [line.split("\t")[0] for line in lines]
    terms = list(dict.fromkeys(terms))

    simplified = cvc5(a.cvc5, PRELUDE + "".join(f"(simplify {t})\n" for t in terms),
                      ["--incremental", "--dag-thresh=0"]).splitlines()
    simplified = [s for s in simplified if s.strip()]
    if len(simplified) != len(terms):
        sys.exit(f"error: expected {len(terms)} results from cvc5, got {len(simplified)}")

    def prove(pair):
        t, s = pair
        if t == s:
            return []
        out = cvc5(a.cvc5, PRELUDE + f"(assert (not (= {t} {s})))\n(check-sat)\n", PROOF_OPTS)
        steps, decls = trusted_steps(out)
        return [(tid, f, decls) for tid, f in steps]

    with ThreadPoolExecutor(a.jobs) as ex:
        found = [x for xs in ex.map(prove, zip(terms, simplified)) for x in xs]
    print(f"{len(terms)} terms, {len(found)} trust steps")

    # Distinct trusted formulas, re-checked on their own.
    uniq = {}
    for tid, f, decls in found:
        uniq.setdefault(f, (tid, decls))

    def recheck(item):
        f, (tid, decls) = item
        steps, script = check_formula(a.cvc5, decls, f)
        return f, tid, steps, script

    with ThreadPoolExecutor(a.jobs) as ex:
        checked = list(ex.map(recheck, uniq.items()))

    groups = {}
    for f, tid, steps, script in checked:
        e = parse_sexpr(f)
        if not (isinstance(e, list) and len(e) == 3 and e[0] == "="):
            key = (tid, "other", "")
        else:
            key = (tid, head(e[1]), head(e[2]))
        if not steps:
            key = ("(not reproduced alone) " + key[0],) + key[1:]
        groups.setdefault(key, []).append((size(e), f, script))

    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    print(f"{len(uniq)} distinct trusted formulas, {len(groups)} groups:")
    for key in sorted(groups, key=lambda k: (-len(groups[k]), k)):
        members = sorted(groups[key])
        _, f, script = members[0]
        print(f"\n[{len(members)}] {key[0]}  {key[1]} -> {key[2]}\n    {f}")
        if key[0].startswith("(not"):
            continue
        name = re.sub(r"[^A-Za-z0-9_.+-]", "_", f"{key[0].replace('TRUST_', '').lower()}-{key[1]}")
        n = 1
        while (out / f"{name}-{n}.smt2").exists():
            n += 1
        (out / f"{name}-{n}.smt2").write_text(f"; trusted: {f}\n" + script)


if __name__ == "__main__":
    main()
