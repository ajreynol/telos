#!/usr/bin/env python3
"""Differential testing of telos's rewriter against cvc5's.

Runs `telos-fuzz SEED COUNT DEPTH` (random terms and their telos rewrites), asks
cvc5 to rewrite the same terms with `(simplify t)`, and reports:

* the rate at which telos and cvc5 reach the same term, and the same term up to
  the orientation of equalities (cvc5 orients them by node id, which telos
  replaces by a structural order), and up to the order of the arguments of
  commutative operators and of `store`s at distinct literal indices (also by
  node id in cvc5), with the remaining mismatches;
* semantic checks, by cvc5: the telos output is equivalent to the input, and to
  cvc5's output. telos's output is *proved* equivalent to its input in Logos's
  semantics, so a failure here is a disagreement between Logos's semantics and
  cvc5's, which is a bug in one of them.

Usage:
  CVC5=PATH scripts/fuzz.py ...  or  scripts/fuzz.py [--cvc5 PATH] [--seed N] [--count N] [--depth N] [--show N] [--arith | --uf | --bv | --arrays | --mixed | --strings | --sets | --datatypes | --quantifiers]

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
(declare-const am (Array (_ BitVec 4) Int))
(declare-const bm (Array U U))
(declare-const cm (Array U U))
(declare-const su String)
(declare-const sv String)
(declare-const sa (Set Int))
(declare-const sb (Set Int))
(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))
(declare-datatypes ((Color 0)) (((red) (green) (blue))))
(declare-const la Lst)
(declare-const lb Lst)
(declare-const co Color)
(declare-datatypes ((Pair 2)) ((par (T S) ((pair (first T) (second S))))))
(declare-datatypes ((PL 1)) ((par (T) ((pnil) (pcons (phd T) (ptl (PL T)))))))
(declare-const pa (Pair Int Color))
(declare-const pl (PL Int))
(declare-const tp (Tuple Int Color))
(declare-const tq (Tuple Int Int))
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


def let_free(e, env=None):
    """`e` with its `let`s expanded (cvc5 and telos print shared subterms with
    `let`, as `_let_1`, …; a quantifier body shadows the names it binds). The
    expansion shares the values, so it is linear as a DAG."""
    env = env or {}
    if isinstance(e, str):
        return env.get(e, e)
    if len(e) == 3 and e[0] == "let" and isinstance(e[1], list):
        env2 = dict(env)
        for b in e[1]:
            env2[b[0]] = let_free(b[1], env)
        return let_free(e[2], env2)
    if len(e) == 3 and e[0] in ("forall", "exists", "lambda", "set.comprehension") and isinstance(e[1], list):
        env2 = {k: v for k, v in env.items() if not any(isinstance(d, list) and d and d[0] == k for d in e[1])}
        return [e[0], e[1], let_free(e[2], env2)]
    return [let_free(x, env) for x in e]


def read_term(text):
    """A printed term, parsed, its `let`s expanded."""
    return let_free(parse_sexpr(text))


def alpha_free(e, env=None, counter=None):
    """`e` with its bound variables renamed `@b0`, `@b1`, … in order of binding:
    equal for terms that differ only in the names of bound variables (cvc5
    gives the quantifiers it creates fresh variables)."""
    env = env or {}
    counter = counter if counter is not None else [0]
    if isinstance(e, str):
        return env.get(e, e)
    if len(e) == 3 and e[0] in ("forall", "exists") and isinstance(e[1], list):
        env = dict(env)
        decls = []
        for d in e[1]:
            if isinstance(d, list) and len(d) == 2 and isinstance(d[0], str):
                env[d[0]] = f"@b{counter[0]}"
                counter[0] += 1
                decls.append([env[d[0]], d[1]])
            else:
                decls.append(d)
        return [e[0], decls, alpha_free(e[2], env, counter)]
    return [alpha_free(x, env, counter) for x in e]


COMMUTATIVE = {"and", "or", "xor", "+", "*", "distinct", "bvand", "bvor", "bvxor",
               "bvadd", "bvmul", "re.union", "re.inter", "set.union", "set.inter"}


def is_literal(e):
    return isinstance(e, str) and (e[0] in '#"-' or e[0].isdigit())


def order_free(e):
    """`orient_free(e)`, also with the arguments of commutative operators
    sorted, and runs of `store` at distinct literal indices sorted: equal for
    terms that differ only in orders that cvc5 takes from node ids, where telos
    uses a structural order."""
    if isinstance(e, str):
        return e
    e = [order_free(x) for x in e]
    head = e[0] if e and isinstance(e[0], str) else None
    if head == "=" and len(e) == 3 or head in COMMUTATIVE:
        e = [e[0]] + sorted(e[1:], key=repr)
    if head == "store" and len(e) == 4:
        writes, base = [], e
        while isinstance(base, list) and base and base[0] == "store" and len(base) == 4 \
                and is_literal(base[2]):
            writes.append((base[2], base[3]))
            base = base[1]
        if len(writes) > 1 and len({i for i, _ in writes}) == len(writes):
            for i, v in sorted(writes, key=repr):
                base = ["store", base, i, v]
            e = base
    return e


def run_cvc5(cvc5, script, extra=()):
    out = subprocess.run([cvc5, "--lang", "smt2", "--incremental",
                          "--no-var-ent-eq-elim-quant",
                          "--print-arith-lit-token", *extra], input=script,
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
    ap.add_argument("--mixed", action="store_true", help="include atoms mixing theories")
    ap.add_argument("--strings", action="store_true", help="include string predicates")
    ap.add_argument("--sets", action="store_true", help="include set predicates")
    ap.add_argument("--datatypes", action="store_true", help="include datatype predicates")
    ap.add_argument("--quantifiers", action="store_true", help="include quantified formulas")
    a = ap.parse_args()
    if not FUZZ.exists():
        sys.exit("error: build the fuzzer first: lake build telos-fuzz")

    lines = subprocess.run([str(FUZZ), str(a.seed), str(a.count), str(a.depth)] + (["arith"] if a.arith else ["uf"] if a.uf else ["bv"] if a.bv else ["arrays"] if a.arrays else ["mixed"] if a.mixed else ["strings"] if a.strings else ["sets"] if a.sets else ["datatypes"] if a.datatypes else ["quantifiers"] if a.quantifiers else []),
                           capture_output=True, text=True, check=True).stdout.splitlines()
    cases = [tuple(line.split("\t")) for line in lines]

    simplified = run_cvc5(a.cvc5, PRELUDE + "".join(f"(simplify {t})\n" for t, _ in cases))
    if len(simplified) != len(cases):
        sys.exit(f"error: expected {len(cases)} results from cvc5, got {len(simplified)}")

    checks = []
    for (t, ours), theirs in zip(cases, simplified):
        checks.append(f"(push)(assert (not (= {t} {ours})))(check-sat)(pop)\n")
        checks.append(f"(push)(assert (not (= {ours} {theirs})))(check-sat)(pop)\n")
    # Each equivalence check gets a time limit: some string equivalences are hard
    # for cvc5. A check that times out (`unknown`) is reported as unverified.
    verdicts = run_cvc5(a.cvc5, PRELUDE + "".join(checks), ["--tlimit-per=2000"])

    same, renamed, oriented, ordered, mismatches, unsound, unverified = 0, 0, 0, 0, [], [], 0
    for i, ((t, ours), theirs) in enumerate(zip(cases, simplified)):
        if ours == theirs:
            same += 1
        elif alpha_free(read_term(ours)) == alpha_free(read_term(theirs)):
            renamed += 1
        elif orient_free(alpha_free(read_term(ours))) == orient_free(alpha_free(read_term(theirs))):
            oriented += 1
        elif order_free(alpha_free(read_term(ours))) == order_free(alpha_free(read_term(theirs))):
            ordered += 1
        else:
            mismatches.append((t, ours, theirs))
        for v, what, l, r in ((verdicts[2 * i], "input vs telos", t, ours),
                              (verdicts[2 * i + 1], "telos vs cvc5", ours, theirs)):
            if v == "sat":
                unsound.append((what, l, r))
            elif v != "unsat":
                unverified += 1

    n = len(cases)
    version = subprocess.run([a.cvc5, "--version"], capture_output=True, text=True).stdout.splitlines()
    print(f"reference: {version[0] if version else a.cvc5}")
    print(f"{n} terms: {same} identical to cvc5 ({100 * same / n:.1f}%), "
          + (f"{renamed} up to the names of bound variables, " if renamed else "")
          + f"{oriented} identical up to the orientation of equalities, "
          f"{ordered} up to the order of commutative arguments, "
          f"{len(mismatches)} different, {len(unsound)} semantic disagreements"
          + (f" ({unverified} checks timed out)" if unverified else ""))
    for t, ours, theirs in mismatches[: a.show]:
        print(f"\n  input: {t}\n  telos: {ours}\n  cvc5:  {theirs}")
    for what, l, r in unsound:
        print(f"\nSEMANTIC DISAGREEMENT ({what}):\n  {l}\n  {r}")
    sys.exit(1 if unsound else 0)


if __name__ == "__main__":
    main()
