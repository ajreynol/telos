#!/usr/bin/env python3
"""Check telos's CPC proofs with Ethos.

Runs `telos --proof-dir` on SMT-LIB scripts of `(simplify t)` queries, then checks
every proof it prints with Ethos, against the CPC signature of the pinned Logos
checkout. telos already checks each proof with Logos's checker before printing it;
this checks the printed text independently.

With `--fuzz N`, the queries are N random terms from `telos-fuzz` instead.

Usage:
  scripts/check-proofs.py [--ethos PATH] FILE.smt2 ...
  scripts/check-proofs.py [--ethos PATH] --fuzz N [--seed S] [--depth D] [--arith | --uf | --bv | --arrays | --mixed | --strings | --sets | --datatypes]

Build first: `lake build telos telos-fuzz`.
"""

import argparse
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / ".lake" / "build" / "bin"
SIGNATURE = ROOT / ".lake" / "packages" / "Cpc" / "install" / "defs" / "Cpc.cached.eo"
FUZZ_PRELUDE = """(declare-const a Bool)
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
"""


def fuzz_script(n, seed, depth, arith, uf=False, bv=False, arrays=False, mixed=False, strings=False, sets=False, datatypes=False):
    out = subprocess.run([str(BIN / "telos-fuzz"), str(seed), str(n), str(depth)] + (["arith"] if arith else ["uf"] if uf else ["bv"] if bv else ["arrays"] if arrays else ["mixed"] if mixed else ["strings"] if strings else ["sets"] if sets else ["datatypes"] if datatypes else []),
                         capture_output=True, text=True, check=True).stdout
    terms = [line.split("\t")[0] for line in out.splitlines()]
    return FUZZ_PRELUDE + "".join(f"(simplify {t})\n" for t in terms)


def check(ethos, script_path, tmp):
    proof_dir = Path(tmp) / script_path.stem
    run = subprocess.run([str(BIN / "telos"), "--proof-dir", str(proof_dir), str(script_path)],
                         capture_output=True, text=True)
    if run.stderr:
        print(run.stderr, end="", file=sys.stderr)
    proofs = sorted(proof_dir.glob("proof-*.eo"), key=lambda p: int(p.stem.split("-")[1]))
    # A supported query whose proof telos could not print (it says so on stderr).
    missing = sum(1 for line in run.stderr.splitlines() if "no proof for" in line)
    failed = []
    for p in proofs:
        # telos prints a proof in parentheses, as cvc5's `get-proof` does; Ethos
        # reads the commands inside.
        text = p.read_text().strip()
        if not (text.startswith("(\n") and text.endswith("\n)")):
            failed.append((p, "not a parenthesized list of commands"))
            continue
        eo = p.with_suffix(".cmds.eo")
        eo.write_text(text[2:-2] + "\n")
        r = subprocess.run([ethos, f"--include={SIGNATURE}", str(eo)], capture_output=True, text=True)
        if r.returncode != 0 or r.stdout.strip().splitlines()[-1:] != ["correct"]:
            failed.append((p, (r.stdout + r.stderr).strip()))
    return len(proofs), failed, missing


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*", type=Path)
    ap.add_argument("--ethos", default=shutil.which("ethos") or "ethos")
    ap.add_argument("--fuzz", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--depth", type=int, default=3)
    ap.add_argument("--arith", action="store_true", help="include arithmetic comparisons")
    ap.add_argument("--uf", action="store_true", help="include equalities and distinct over an uninterpreted sort")
    ap.add_argument("--bv", action="store_true", help="include bit-vector comparisons")
    ap.add_argument("--arrays", action="store_true", help="include array equalities")
    ap.add_argument("--mixed", action="store_true", help="include atoms mixing theories")
    ap.add_argument("--strings", action="store_true", help="include string predicates")
    ap.add_argument("--sets", action="store_true", help="include set predicates")
    ap.add_argument("--datatypes", action="store_true", help="include datatype predicates")
    a = ap.parse_args()
    if not (BIN / "telos").exists():
        sys.exit("error: build telos first: lake build telos telos-fuzz")
    total, failures, missing = 0, [], 0
    with tempfile.TemporaryDirectory() as tmp:
        files = list(a.files)
        if a.fuzz:
            f = Path(tmp) / "fuzz.smt2"
            f.write_text(fuzz_script(a.fuzz, a.seed, a.depth, a.arith, a.uf, a.bv, a.arrays, a.mixed, a.strings, a.sets, a.datatypes))
            files.append(f)
        for f in files:
            n, failed, m = check(a.ethos, f, tmp)
            total += n
            failures += failed
            missing += m
        for p, msg in failures[:10]:
            print(f"\nREJECTED {p.name}:\n{p.read_text()}{msg}")
    print(f"{total} proofs, {total - len(failures)} accepted by Ethos, {len(failures)} rejected, "
          f"{missing} missing")
    sys.exit(1 if failures or missing else 0)


if __name__ == "__main__":
    main()
