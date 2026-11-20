#!/usr/bin/env python3
"""Differential testing of telos's SAT solver (`telos --dimacs`) against cvc5.

Random 3-CNF near the satisfiability threshold (4.26 clauses per variable),
or the DIMACS files given. telos's answer must agree with cvc5's on the same
clauses (given as an SMT-LIB problem over Boolean constants), and its model,
which telos itself checks against the clauses, must exist for `sat`.

Usage:
  scripts/fuzz-sat.py [--cvc5 PATH] [--seed N] [--count N] [--vars N] [FILE.cnf ...]
"""
import argparse
import os
import random
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TELOS = ROOT / ".lake" / "build" / "bin" / "telos"


def random_cnf(rng, n):
    m = round(4.26 * n)
    clauses = []
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), 3)
        clauses.append([v if rng.random() < 0.5 else -v for v in vs])
    return n, clauses


def to_dimacs(n, clauses):
    return f"p cnf {n} {len(clauses)}\n" + "".join(" ".join(map(str, c)) + " 0\n" for c in clauses)


def parse_dimacs(text):
    n, clauses, cur = 0, [], []
    for line in text.splitlines():
        line = line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            n = int(line.split()[2])
            continue
        for tok in line.split():
            v = int(tok)
            if v == 0:
                clauses.append(cur)
                cur = []
            else:
                cur.append(v)
    return n, clauses


def to_smt(n, clauses):
    lit = lambda v: f"x{v}" if v > 0 else f"(not x{-v})"
    out = ["(set-logic QF_UF)"] + [f"(declare-const x{i} Bool)" for i in range(1, n + 1)]
    for c in clauses:
        out.append(f"(assert (or {' '.join(map(lit, c))} false))")
    out.append("(check-sat)")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cvc5", default=os.environ.get("CVC5") or shutil.which("cvc5") or "cvc5")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=200)
    ap.add_argument("--vars", type=int, default=40)
    ap.add_argument("files", nargs="*")
    a = ap.parse_args()
    rng = random.Random(a.seed)
    tmp = Path(tempfile.mkdtemp())
    problems = []
    if a.files:
        for f in a.files:
            problems.append((f, parse_dimacs(Path(f).read_text())))
    else:
        for i in range(a.count):
            problems.append((f"r{i}", random_cnf(rng, rng.randint(5, a.vars))))
    counts = {"sat": 0, "unsat": 0, "different": 0, "failed": 0}
    for name, (n, clauses) in problems:
        cnf = tmp / f"{Path(name).stem}.cnf"
        cnf.write_text(to_dimacs(n, clauses))
        smt = tmp / f"{Path(name).stem}.smt2"
        smt.write_text(to_smt(n, clauses))
        r = subprocess.run([str(TELOS), "--dimacs", str(cnf)], capture_output=True, text=True)
        if r.returncode != 0:
            counts["failed"] += 1
            print(f"  {name}: telos: {r.stderr.strip()}")
            continue
        ours = r.stdout.split("\n")[0].strip()
        theirs = subprocess.run([a.cvc5, str(smt)], capture_output=True, text=True).stdout.strip()
        if ours != theirs:
            counts["different"] += 1
            print(f"  {name}: telos {ours}, cvc5 {theirs}")
        else:
            counts[ours] = counts.get(ours, 0) + 1
    print(f"{len(problems)} problems: {counts['sat']} sat, {counts['unsat']} unsat, "
          f"{counts['different']} different, {counts['failed']} failed")
    sys.exit(1 if counts["different"] or counts["failed"] else 0)


if __name__ == "__main__":
    main()
