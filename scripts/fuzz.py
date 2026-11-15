#!/usr/bin/env python3
"""Differential testing of telos's rewriter against cvc5's.

Runs `telos-fuzz SEED COUNT DEPTH` (random terms and their telos rewrites), asks
cvc5 to rewrite the same terms with `(simplify t)`, and reports:

* the rate at which telos and cvc5 reach the same term, and the same term up to
  the orientation of equalities (cvc5 orients them by node id, which telos
  replaces by a structural order), with the remaining mismatches;
* semantic checks, by cvc5: the telos output is equivalent to the input, and to
  cvc5's output. telos's output is *proved* equivalent to its input in Logos's
  semantics, so a failure here is a disagreement between Logos's semantics and
  cvc5's, which is a bug in one of them.

Usage:
  CVC5=PATH scripts/fuzz.py ...  or  scripts/fuzz.py [--cvc5 PATH] [--seed N] [--count N] [--depth N] [--show N] [--arith | --uf | --bv | --arrays]

Build the fuzzer first: `lake build telos-fuzz`.
"""

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FUZZ = ROOT / ".lake" / "build" / "bin" / "telos-fuzz"
PRELUDE = """(set-logic ALL)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(declare-const x Int)
(declare-const y Int)
(declare-const r Real)
(declare-const s Real)
(declare-sort U 0)
(declare-const u U)
(declare-const v U)
(declare-const w U)
(declare-fun f (U) U)
(declare-const bx (_ BitVec 4))
(declare-const by (_ BitVec 4))
(declare-const bz (_ BitVec 4))
(declare-const aa (Array Int Int))
(declare-const ab (Array Int Int))
"""


def parse_sexpr(text):
    import re
    toks = re.findall(r'\(|\)|"(?:[^"]|"")*"|[^\s()]+', text)
    pos = 0

    def go():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t != "(":
            return t
        lst = []
        while toks[pos] != ")":
            lst.append(go())
        pos += 1
        return lst

    return go()


def orient_free(e):
    """`e` with the arguments of every `=` sorted: equal for terms that differ
    only in how equalities are oriented, which depends on cvc5's node ids."""
    if isinstance(e, str):
        return e
    e = [orient_free(x) for x in e]
    if e and e[0] == "=" and len(e) == 3:
        e = ["="] + sorted(e[1:], key=repr)
    return e


def run_cvc5(cvc5, script):
    out = subprocess.run([cvc5, "--lang", "smt2", "--incremental", "--dag-thresh=0",
                          "--print-arith-lit-token"], input=script,
                         capture_output=True, text=True, check=False)
    if out.returncode != 0:
        sys.exit(f"error: cvc5 failed:\n{out.stderr or out.stdout}")
    return [line for line in out.stdout.splitlines() if line.strip()]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    # The reference cvc5: `--cvc5`, else `$CVC5`, else `cvc5` on the path. Use a
    # recent build of cvc5's main branch: the rewriter changes (for example,
    # arithmetic equalities are not solved since cvc5 PR #12833).
    ap.add_argument("--cvc5", default=os.environ.get("CVC5") or shutil.which("cvc5") or "cvc5")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=500)
    ap.add_argument("--depth", type=int, default=3)
    ap.add_argument("--show", type=int, default=10, help="mismatches to print")
    ap.add_argument("--arith", action="store_true", help="include arithmetic comparisons")
    ap.add_argument("--uf", action="store_true", help="include equalities and distinct over an uninterpreted sort")
    ap.add_argument("--bv", action="store_true", help="include bit-vector comparisons")
    ap.add_argument("--arrays", action="store_true", help="include array equalities")
    a = ap.parse_args()
    if not FUZZ.exists():
        sys.exit("error: build the fuzzer first: lake build telos-fuzz")

    lines = subprocess.run([str(FUZZ), str(a.seed), str(a.count), str(a.depth)] + (["arith"] if a.arith else ["uf"] if a.uf else ["bv"] if a.bv else ["arrays"] if a.arrays else []),
                           capture_output=True, text=True, check=True).stdout.splitlines()
    cases = [tuple(line.split("\t")) for line in lines]

    simplified = run_cvc5(a.cvc5, PRELUDE + "".join(f"(simplify {t})\n" for t, _ in cases))
    if len(simplified) != len(cases):
        sys.exit(f"error: expected {len(cases)} results from cvc5, got {len(simplified)}")

    checks = []
    for (t, ours), theirs in zip(cases, simplified):
        checks.append(f"(push)(assert (not (= {t} {ours})))(check-sat)(pop)\n")
        checks.append(f"(push)(assert (not (= {ours} {theirs})))(check-sat)(pop)\n")
    verdicts = run_cvc5(a.cvc5, PRELUDE + "".join(checks))

    same, oriented, mismatches, unsound = 0, 0, [], []
    for i, ((t, ours), theirs) in enumerate(zip(cases, simplified)):
        if ours == theirs:
            same += 1
        elif orient_free(parse_sexpr(ours)) == orient_free(parse_sexpr(theirs)):
            oriented += 1
        else:
            mismatches.append((t, ours, theirs))
        if verdicts[2 * i] != "unsat":
            unsound.append(("input vs telos", t, ours))
        if verdicts[2 * i + 1] != "unsat":
            unsound.append(("telos vs cvc5", ours, theirs))

    n = len(cases)
    version = subprocess.run([a.cvc5, "--version"], capture_output=True, text=True).stdout.splitlines()
    print(f"reference: {version[0] if version else a.cvc5}")
    print(f"{n} terms: {same} identical to cvc5 ({100 * same / n:.1f}%), "
          f"{oriented} identical up to the orientation of equalities, "
          f"{len(mismatches)} different, {len(unsound)} semantic disagreements")
    for t, ours, theirs in mismatches[: a.show]:
        print(f"\n  input: {t}\n  telos: {ours}\n  cvc5:  {theirs}")
    for what, l, r in unsound:
        print(f"\nSEMANTIC DISAGREEMENT ({what}):\n  {l}\n  {r}")
    sys.exit(1 if unsound else 0)


if __name__ == "__main__":
    main()
