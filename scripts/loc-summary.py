#!/usr/bin/env python3
"""Nonblank, noncomment Lean LOC: TCB/spec, solver, verification proofs.

TCB/spec files are listed in lean_inventory.py, including the trusted profiling
implementation. Solver includes core, rewriting, preprocessing, checking, model
evaluation, front end and proof output. Proofs include verification/ except its
specification, plus standalone theorem/lemma commands in solver files. Inline
proof terms and termination proofs stay with their definitions; TCB/spec files
are counted whole. Tests, fuzzing and audit tools are reported separately.

Every repository Lean file is accounted for exactly once. No build is needed.
External Logos specification LOC is reported separately. Use --files for detail.
"""

import argparse
from collections import defaultdict

from lean_inventory import (
    ROOT, LOGOS, category_of, count_loc, inline_proof_lines, lean_files,
    logos_spec_modules, mask_comments, module_path,
)

TITLES = {
    "spec": "(1) TCB/spec",
    "solver": "(2) solver code",
    "proofs": "(3) verification proofs of solver code",
    "support": "Supporting code: tests, fuzzing, audit tools",
}


def detail(rel: str) -> str:
    if rel in {"Telos/Rewriter/Rules/Generated.lean", "Telos/Core/RuleNames.lean"}:
        return "generated rule tables"
    if rel.startswith("Telos/Core/Proof/") or rel == "Telos/Solver/EqProofCpc.lean":
        return "front end and proof output"
    if rel.startswith("Telos/Core/") or rel == "Telos.lean":
        return "shared core"
    if rel.startswith("Telos/Rewriter/"):
        return "rewriter"
    if rel.startswith("Telos/Preprocess/"):
        return "preprocessor"
    if rel.startswith("Telos/Solver/"):
        return "solver engine, checkers and evaluator"
    return "front end and proof output"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--files", action="store_true", help="list each file's contribution")
    args = parser.parse_args()
    per = {key: [] for key in TITLES}
    missing = []
    for path in lean_files(ROOT):
        rel = path.relative_to(ROOT).as_posix()
        key = category_of(rel)
        if key is None:
            missing.append(rel)
            continue
        text = path.read_text()
        lines = {i for i, line in enumerate(mask_comments(text).splitlines()) if line.strip()}
        proofs = lines & inline_proof_lines(text) if key == "solver" else set()
        per[key].append((rel, len(lines - proofs)))
        if proofs:
            per["proofs"].append((rel + " (standalone theorems/lemmas)", len(proofs)))
    if missing:
        parser.error("unclassified Lean files (edit lean_inventory.py): " + ", ".join(missing))

    totals = {key: sum(n for _, n in rows) for key, rows in per.items()}
    for key, title in TITLES.items():
        if key == "support":
            production = sum(totals[k] for k in ("spec", "solver", "proofs"))
            print(f"{'Production total (1 + 2 + 3)':<47} {production:>7}\n")
        print(f"{title:<47} {totals[key]:>7}  ({len(per[key])} file contributions)")
        if key == "solver" and not args.files:
            groups = defaultdict(int)
            for rel, n in per[key]:
                groups[detail(rel)] += n
            for group, n in sorted(groups.items()):
                print(f"    {group:<43} {n:>7}")
        if args.files:
            for rel, n in sorted(per[key]):
                print(f"    {n:>7}  {rel}")
    print(f"{'Repository total':<47} {sum(totals.values()):>7}")
    print("\nLOC convention: inline proof terms/termination proofs stay with definitions;")
    print("TCB/spec files are counted whole. External Logos LOC is not in these totals.")
    if LOGOS.is_dir():
        modules = logos_spec_modules()
        loc = sum(count_loc(LOGOS / module_path(m)) for m in modules)
        print(f"Logos TCB/spec import closure (Cpc.Spec + Cpc.SmtTranslate): {loc} ({len(modules)} files)")
    else:
        print("Logos TCB/spec: unavailable (run `lake build` to fetch the pinned checkout).")


if __name__ == "__main__":
    main()
