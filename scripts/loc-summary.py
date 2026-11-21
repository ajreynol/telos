#!/usr/bin/env python3
"""Lines of code in telos, by role.

Every Lean file of the repository is put in exactly one bucket:

  (1) specification: what `Telos.rewrite_correct`, `Telos.preprocess_correct`,
      `Telos.solve_unsat_correct` and `Telos.solve_sat_correct` mean. This is telos's part of the trusted base (TRUSTED.md): the `Node`
      datatype (with `SkolemId`), its translation to Logos terms (`toEo`) and the
      definition of `Node.Equiv`. For reference, the Logos specification it
      builds on (the import closure of `Cpc.Spec` and `Cpc.SmtTranslate` in the
      pinned Logos checkout) is reported separately.
  (2) core: the rest of `Telos/Core/`, untrusted: node utilities, certified
      rewrites (`Rw`) and static steps, shared by the rewriter and the
      preprocessor.
  (3) rewriter: `Telos/Rewriter/`, untrusted: the driver, the rule matcher and
      the theory strategies. Generated files are counted separately.
  (4) preprocessor: `Telos/Preprocess/`, untrusted: the pipeline and the passes.
  (5) solver: `Telos/Solver/`, untrusted, in two parts: the certificate
      checkers and the model evaluator, which the solver theorems prove sound
      (`SatProof`, `EqProof`, `LinCert`, `Explain`, `Model`), and the rest (the
      theory engine, the SAT solver, the CNF stream, the theories and the
      builders of certificates), whose answers stand only if they check.
  (6) front end and proof output: SMT-LIB input, CPC proof printing, the `telos`
      executable. Untrusted, and outside the theorems.
  (7) proofs: `verification/TelosProofs/` and `verification/TelosFull/`, minus
      the specification.
  (8) tests and fuzzing.

A line of code is a non-blank, non-comment line (Lean `--` and nested `/- -/`
comments stripped), as in Logos's `scripts/cpc-loc-summary.py`.

Usage:
  scripts/loc-summary.py           # totals per bucket
  scripts/loc-summary.py --files   # also every file with its count

Fails if a Lean file is in no bucket, so the classification stays complete.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOGOS = ROOT / ".lake" / "packages" / "Cpc"

SPEC = [
    "Telos/Core/Node/Kind.lean",
    "Telos/Core/Node/TypeNode.lean",
    "Telos/Core/Node/SkolemId.lean",
    "Telos/Core/Node/Node.lean",
    "Telos/Core/Node/ToEo.lean",
    "verification/TelosProofs/Core/Spec.lean",
]
GENERATED = ["Telos/Rewriter/Rules/Generated.lean", "Telos/Core/RuleNames.lean"]
FRONTEND = ["Telos/Frontend/", "Telos/Core/Proof/", "Telos/Solver/EqProofCpc.lean", "Main.lean"]
CHECKERS = ["Telos/Solver/SatProof.lean", "Telos/Solver/EqProof.lean", "Telos/Solver/LinCert.lean",
            "Telos/Solver/Explain.lean", "Telos/Solver/Model.lean"]
SOLVER = ["Telos/Solver/"]
TESTS = ["TelosTests/", "FuzzMain.lean"]
PROOFS = ["verification/TelosProofs/", "verification/TelosFull/"]
REWRITER = ["Telos/Rewriter/"]
PREPROCESSOR = ["Telos/Preprocess/"]
CORE = ["Telos/Core/", "Telos.lean"]

# (key, title, path prefixes); the first bucket whose prefix matches owns a file.
BUCKETS = [
    ("spec", "(1) specification (trusted)", SPEC),
    ("gen", "(3) rewriter: generated rule tables", GENERATED),
    ("front", "(6) front end and proof output", FRONTEND),
    ("tests", "(8) tests and fuzzing", TESTS),
    ("proofs", "(7) proofs", PROOFS),
    ("check", "(5) solver: checkers and evaluator", CHECKERS),
    ("solver", "(5) solver: engine, SAT solver, theories", SOLVER),
    ("rw", "(3) rewriter: hand-written", REWRITER),
    ("pp", "(4) preprocessor", PREPROCESSOR),
    ("core", "(2) core (shared, untrusted)", CORE),
]
DISPLAY = ["spec", "core", "rw", "gen", "pp", "check", "solver", "front", "proofs", "tests"]
SKIP_DIRS = {".lake", ".git"}


def count_loc(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return sum(1 for line in "".join(out).splitlines() if line.strip())


def lean_files(base: Path):
    for p in sorted(base.rglob("*.lean")):
        if not SKIP_DIRS & set(p.relative_to(base).parts):
            yield p


def bucket_of(rel: str) -> str | None:
    for key, _, prefixes in BUCKETS:
        if any(rel == p or (p.endswith("/") and rel.startswith(p)) for p in prefixes):
            return key
    return None


IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(?:all\s+)?((?:Cpc|Logos)[\w.]*)")


def logos_spec_loc() -> int | None:
    """LOC of the Logos specification: the import closure of `Cpc.Spec` and
    `Cpc.SmtTranslate`."""
    if not LOGOS.exists():
        return None
    seen, stack = set(), ["Cpc.Spec", "Cpc.SmtTranslate"]
    while stack:
        m = stack.pop()
        path = LOGOS / (m.replace(".", "/") + ".lean")
        if m in seen or not path.exists():
            continue
        seen.add(m)
        for line in path.read_text(encoding="utf-8").splitlines():
            if (mm := IMPORT_RE.match(line)):
                stack.append(mm.group(1))
    return sum(count_loc(LOGOS / (m.replace(".", "/") + ".lean")) for m in seen)


def main():
    show_files = "--files" in sys.argv[1:]
    per: dict[str, list[tuple[str, int]]] = {k: [] for k, _, _ in BUCKETS}
    missing = []
    for p in lean_files(ROOT):
        rel = p.relative_to(ROOT).as_posix()
        key = bucket_of(rel)
        if key is None:
            missing.append(rel)
            continue
        per[key].append((rel, count_loc(p)))
    if missing:
        sys.exit("error: not in any bucket (edit scripts/loc-summary.py): " + ", ".join(missing))
    titles = {k: t for k, t, _ in BUCKETS}
    total = 0
    for key in DISPLAY:
        loc = sum(n for _, n in per[key])
        total += loc
        print(f"{titles[key]:<42} {loc:>6}  ({len(per[key])} files)")
        if show_files:
            for rel, n in per[key]:
                print(f"    {n:>6}  {rel}")
    print(f"{'total':<42} {total:>6}")
    logos = logos_spec_loc()
    if logos is not None:
        print(f"\nfor reference, the Logos specification telos builds on "
              f"(Cpc.Spec, Cpc.SmtTranslate and their imports): {logos}")


if __name__ == "__main__":
    main()
