#!/usr/bin/env python3
"""Check telos's full CPC proofs of `unsat` with Ethos.

Runs `telos --dump-proofs FILE` on each benchmark; for each `unsat` answer,
checks the proof that follows it (from the input assertions to `false`, through
preprocessing, the CNF translation, the theory lemmas and conflicts, and
resolution: `Telos/Frontend/FullProof.lean`) with Ethos, against the CPC
signature of the pinned Logos checkout.

Each benchmark is classified as:
  ok          the proof is accepted;
  rejected    Ethos rejects it (a bug);
  no-proof    telos answered unsat but printed no proof (a gap: what has no
              CPC proof yet is named);
  other       the answer is not unsat (nothing to check);
  timeout     telos or Ethos ran out of time.

Usage:
  scripts/check-full-proofs.py [--ethos PATH] [--timeout S] [--jobs N] [-v] FILE.smt2 ...

The exit status is 1 if a proof is rejected or missing. Build first: `lake build`.
"""

import argparse
import collections
import concurrent.futures as cf
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TELOS = ROOT / ".lake" / "build" / "bin" / "telos"
SIGNATURE = ROOT / ".lake" / "packages" / "Cpc" / "install" / "defs" / "Cpc.cached.eo"


def first_proof(lines):
    """The proof printed right after the first `unsat`, without its outer
    parentheses (a Eunoia file), or the error printed instead."""
    if "unsat" not in lines:
        return None, None
    i = lines.index("unsat")
    rest = lines[i + 1:]
    if not rest:
        return None, "no proof printed"
    if rest[0].startswith("(error"):
        return None, re.sub(r"\s+", " ", rest[0])[:200]
    if rest[0] != "(":
        return None, "no proof printed"
    body = rest[1:rest.index(")")] if ")" in rest else rest[1:]
    return "\n".join(body) + "\n", None


def check(path, ethos, timeout, tmp):
    try:
        r = subprocess.run([str(TELOS), "--dump-proofs", str(path)], capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", "telos"
    lines = r.stdout.split("\n")
    proof, err = first_proof(lines)
    if proof is None and err is None:
        return "other", (lines[0] if lines else "")
    if proof is None:
        return "no-proof", err
    eo = Path(tmp) / (path.name + ".eo")
    eo.write_text(proof)
    try:
        e = subprocess.run([ethos, f"--include={SIGNATURE}", str(eo)], capture_output=True, text=True,
                           timeout=timeout * 3)
    except subprocess.TimeoutExpired:
        return "timeout", "ethos"
    if e.stdout.strip().split("\n")[-1:] == ["correct"]:
        return "ok", ""
    msg = [l for l in (e.stdout + e.stderr).strip().split("\n") if "associative application" not in l]
    return "rejected", (msg[-1] if msg else "")[:200]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+", type=Path)
    ap.add_argument("--ethos", default=shutil.which("ethos") or "ethos")
    ap.add_argument("--timeout", type=int, default=20)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 4)
    ap.add_argument("-v", "--verbose", action="store_true", help="list every benchmark that is not ok")
    a = ap.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        with cf.ThreadPoolExecutor(a.jobs) as ex:
            res = list(ex.map(lambda f: (f, *check(f, a.ethos, a.timeout, tmp)), a.files))
    counts = collections.Counter(k for _, k, _ in res)
    print(f"{len(res)} benchmarks: " + ", ".join(f"{counts[k]} {k}" for k in
          ["ok", "rejected", "no-proof", "other", "timeout"] if counts[k]))
    reasons = collections.Counter((k, m) for _, k, m in res if k in ("rejected", "no-proof"))
    for (k, m), n in reasons.most_common(20):
        print(f"  {n:4} {k:9} {m}")
    if a.verbose:
        for f, k, m in res:
            if k not in ("ok", "other"):
                print(f"  {k:9} {f} {m}")
    return 1 if counts["rejected"] or counts["no-proof"] else 0


if __name__ == "__main__":
    sys.exit(main())
