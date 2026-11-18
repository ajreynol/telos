#!/usr/bin/env python3
"""Differential testing of telos's preprocessor against cvc5's.

Runs `telos --post-asserts` and `cvc5 -o post-asserts` on benchmarks, with
cvc5's passes that telos does not port yet switched off (`CVC5_OPTS` below), and
compares the preprocessed assertions, in order, and the declarations, as a set.
Assertions are compared as `fuzz.py` compares terms: identical, or up to the
names of bound variables, the orientation of equalities, and the order of
commutative arguments (which cvc5 takes from node ids). `define-fun`s are
macros in telos (`Telos/Frontend/PostAsserts.lean`), so cvc5's `define-fun`
lines are ignored, and for a benchmark with `define-fun`s so are the
`(assert true)` that cvc5 keeps in their place (all `(assert true)`, on both
sides).

The benchmarks are random (default): scripts of 1 to 4 assertions, each a
random Boolean term from `telos-fuzz` (with the declarations of `fuzz.py`), or
the SMT-LIB files given as arguments.

Usage:
  scripts/fuzz-pp.py [--cvc5 PATH] [--seed N] [--count N] [--depth N] [--show N] [MODE]
  scripts/fuzz-pp.py [--cvc5 PATH] [--show N] FILE.smt2 ...

MODE is one of `fuzz.py`'s term modes (`--arith`, `--uf`, …). Build first:
`lake build telos telos-fuzz`.
"""
import argparse
import os
import random
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
import fuzz  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
TELOS = ROOT / ".lake" / "build" / "bin" / "telos"
# cvc5's passes that telos does not port yet, switched off. `theory-preprocess`
# and `static-rewrite` cannot be: benchmarks they change differ.
CVC5_OPTS = ["--simplification=none", "--no-static-learning"]
MODES = ["arith", "uf", "bv", "arrays", "mixed", "strings", "sets", "datatypes", "quantifiers"]


def post_asserts(text):
    """The declarations (a set) and assertions (a list) of a post-asserts output."""
    lines = text.splitlines()
    try:
        lines = lines[lines.index(";; post-asserts start") + 1:lines.index(";; post-asserts end")]
    except ValueError:
        return None
    decls = {l for l in lines if l.startswith("(declare-")}
    asserts = [l[len("(assert "):-1] for l in lines if l.startswith("(assert ")]
    return decls, asserts


def run(cmd, path):
    r = subprocess.run(cmd + [str(path)], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None, r.stderr.strip()


def compare(ours, theirs):
    """`same`, `renamed`, `oriented`, `ordered` or None."""
    if ours == theirs:
        return "same"
    o, t = [fuzz.alpha_free(fuzz.parse_sexpr(x)) for x in ours], [fuzz.alpha_free(fuzz.parse_sexpr(x)) for x in theirs]
    if o == t:
        return "renamed"
    if [fuzz.orient_free(x) for x in o] == [fuzz.orient_free(x) for x in t]:
        return "oriented"
    if [fuzz.order_free(x) for x in o] == [fuzz.order_free(x) for x in t]:
        return "ordered"
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cvc5", default=os.environ.get("CVC5") or shutil.which("cvc5") or "cvc5")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=200, help="random benchmarks")
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument("--show", type=int, default=5, help="mismatches to print")
    for m in MODES:
        ap.add_argument(f"--{m}", action="store_true")
    ap.add_argument("files", nargs="*")
    a = ap.parse_args()
    if not TELOS.exists():
        sys.exit("error: build telos first: lake build telos telos-fuzz")
    cvc5 = [a.cvc5, "-o", "post-asserts", "--print-arith-lit-token", "--dag-thresh=0",
            "--no-var-ent-eq-elim-quant", *CVC5_OPTS]
    tmp = Path(tempfile.mkdtemp())
    files = [Path(f) for f in a.files]
    if not files:
        mode = next((m for m in MODES if getattr(a, m)), None)
        rng = random.Random(a.seed)
        sizes = [rng.randint(1, 4) for _ in range(a.count)]
        out = subprocess.run([str(fuzz.FUZZ), str(a.seed), str(sum(sizes)), str(a.depth)] + ([mode] if mode else []),
                             capture_output=True, text=True, check=True).stdout.splitlines()
        terms = [line.split("\t")[0] for line in out]
        for i, k in enumerate(sizes):
            path = tmp / f"b{i}.smt2"
            body = "".join(f"(assert {t})\n" for t in terms[:k])
            terms = terms[k:]
            path.write_text(fuzz.PRELUDE + body + "(check-sat)\n")
            files.append(path)
    counts = {"same": 0, "renamed": 0, "oriented": 0, "ordered": 0}
    mismatches, failures = [], []
    for path in files:
        ours, err = run([str(TELOS), "--post-asserts"], path)
        theirs, cerr = run(cvc5, path)
        if ours is None or theirs is None:
            failures.append((path, err if ours is None else cerr))
            continue
        o, t = post_asserts(ours), post_asserts(theirs)
        if o is None or t is None:
            failures.append((path, "no post-asserts output"))
            continue
        (od, oa), (td, ta) = o, t
        if "define-fun" in path.read_text():
            oa = [x for x in oa if x != "true"]
            ta = [x for x in ta if x != "true"]
        verdict = compare(oa, ta)
        if verdict and od == td:
            counts[verdict] += 1
        else:
            mismatches.append((path, oa, ta, od ^ td))
    n = len(files)
    version = subprocess.run([a.cvc5, "--version"], capture_output=True, text=True).stdout.splitlines()
    print(f"reference: {version[0] if version else a.cvc5} {' '.join(CVC5_OPTS)}")
    print(f"{n} benchmarks: {counts['same']} identical to cvc5, {counts['renamed']} up to the names of "
          f"bound variables, {counts['oriented']} up to the orientation of equalities, "
          f"{counts['ordered']} up to the order of commutative arguments, {len(mismatches)} different, "
          f"{len(failures)} failed")
    for path, oa, ta, dd in mismatches[:a.show]:
        print(f"\n  {path}:")
        for x, y in zip(oa + [""] * (len(ta) - len(oa)), ta + [""] * (len(oa) - len(ta))):
            mark = " " if x == y else "*"
            print(f"  {mark} telos: {x}\n  {mark} cvc5:  {y}")
        if dd:
            print(f"    declarations differing: {sorted(dd)}")
    for path, err in failures[:a.show]:
        print(f"\n  {path}: {err.splitlines()[0] if err else 'failed'}")


if __name__ == "__main__":
    main()
