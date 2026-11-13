#!/usr/bin/env python3
"""Check telos's CPC proofs with Ethos.

Runs `telos --proof-dir` on SMT-LIB scripts of `(simplify t)` queries, then checks
every proof it prints with Ethos, against the CPC signature of the pinned Logos
checkout. telos already checks each proof with Logos's checker before printing it;
this checks the printed text independently.

With `--fuzz N`, the queries are N random terms from `telos-fuzz` instead.

Usage:
  scripts/check-proofs.py [--ethos PATH] FILE.smt2 ...
  scripts/check-proofs.py [--ethos PATH] --fuzz N [--seed S] [--depth D] [--arith]

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
"""


def fuzz_script(n, seed, depth, arith):
    out = subprocess.run([str(BIN / "telos-fuzz"), str(seed), str(n), str(depth)] + (["arith"] if arith else []),
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
    failed = []
    for p in proofs:
        r = subprocess.run([ethos, f"--include={SIGNATURE}", str(p)], capture_output=True, text=True)
        if r.returncode != 0 or r.stdout.strip().splitlines()[-1:] != ["correct"]:
            failed.append((p, (r.stdout + r.stderr).strip()))
    return len(proofs), failed


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="*", type=Path)
    ap.add_argument("--ethos", default=shutil.which("ethos") or "ethos")
    ap.add_argument("--fuzz", type=int, default=0)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--depth", type=int, default=3)
    ap.add_argument("--arith", action="store_true", help="include arithmetic comparisons")
    a = ap.parse_args()
    if not (BIN / "telos").exists():
        sys.exit("error: build telos first: lake build telos telos-fuzz")
    total, failures = 0, []
    with tempfile.TemporaryDirectory() as tmp:
        files = list(a.files)
        if a.fuzz:
            f = Path(tmp) / "fuzz.smt2"
            f.write_text(fuzz_script(a.fuzz, a.seed, a.depth, a.arith))
            files.append(f)
        for f in files:
            n, failed = check(a.ethos, f, tmp)
            total += n
            failures += failed
        for p, msg in failures[:10]:
            print(f"\nREJECTED {p.name}:\n{p.read_text()}{msg}")
    print(f"{total} proofs, {total - len(failures)} accepted by Ethos, {len(failures)} rejected")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
