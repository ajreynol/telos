#!/usr/bin/env python3
"""Inventory runtime references to Logos and check the solver/TCB boundary.

Uses the pinned Lean compiler's saved base LCNF: proof-erased, after early
simplification/specialization. Counts static application/reference sites in all compiled
production declarations, including implicit instances and compiler helpers.
These are neither source-token counts nor dynamic execution counts. Unused
compiled definitions are included. Constructors, types and theorem bodies are
excluded. Applications through variables cannot be resolved by this inventory;
named function references passed to them are counted where they are supplied.

By default builds all production Lean modules first (no verification/Mathlib
build), then reports calls from category (2). --scope all also reports callers
in category (1). --check-no-spec fails on calls from (2) into Telos's TCB/spec
or Logos's specification, including paths through Logos's checker/helpers.
Shared datatype constructors are allowed; functions in TCB files are not.
"""

import argparse
from collections import Counter, defaultdict, deque
import json
import subprocess
import sys

from lean_inventory import (
    ROOT, category_of, lean_files, logos_spec_modules, module_path,
)


def is_logos(module: str) -> bool:
    return module in {"Cpc", "Logos"} or module.startswith(("Cpc.", "Logos."))


def is_spec(module: str, logos_spec: set[str]) -> bool:
    return module in logos_spec or category_of(module_path(module)) == "spec"


def purpose(row: dict) -> str:
    module, name = row["target_module"], row["callee"]
    if module == "Cpc.SmtTranslate":
        return "SMT translation (spec)"
    if module == "Cpc.SmtTyping":
        return "SMT typing (spec)"
    if module == "Cpc.SmtEval":
        return "native primitives (spec)"
    if module in {"Cpc.SmtModel", "Cpc.Spec"}:
        return "model semantics (spec)"
    if module == "Cpc.TranslationChecks":
        return "translation side-condition checks"
    if module in {"Cpc.LogosTerm", "Cpc.SmtSyntax"}:
        return "datatype helpers (spec): " + module
    if module == "Cpc.LogosTermOrder":
        return "term ordering"
    if module == "Logos.Sexp":
        return "S-expression parsing/printing"
    if module == "Cpc.Logos":
        if any(part in name for part in ("__eo_invoke", "__eo_state", "__eo_is_refutation")):
            return "CPC checker/state"
        if any(part in name for part in ("__eo_typeof", "__eo_nil")):
            return "EO typing/nil"
        return "CPC rule programs/helpers"
    if "Parser" in module or "Elab" in module:
        return "parser/elaborator"
    return module  # New APIs remain visible, never silently dropped.


def spec_paths(rows: list[dict], logos_spec: set[str]) -> dict[str, list[str]]:
    """One shortest named-reference path to a spec function, including cycles."""
    reverse = defaultdict(set)
    paths = {}
    for row in rows:
        caller, callee = row["caller"], row["callee"]
        reverse[callee].add(caller)
        if is_spec(row["target_module"], logos_spec):
            paths[callee] = [callee]
    todo = deque(sorted(paths))
    while todo:
        callee = todo.popleft()
        for caller in sorted(reverse[callee]):
            if caller not in paths:
                paths[caller] = [caller] + paths[callee]
                todo.append(caller)
    return paths


def analyze(rows: list[dict], logos_spec: set[str], scope: str) -> dict:
    paths = spec_paths(rows, logos_spec)
    logos, boundary = [], []
    for row in rows:
        category = category_of(module_path(row["module"]))
        if category not in {"solver", "spec"}:
            continue
        if is_logos(row["target_module"]) and (scope == "all" or category == "solver"):
            logos.append({**row, "category": category, "purpose": purpose(row)})
        if category != "solver":
            continue
        direct = is_spec(row["target_module"], logos_spec)
        via_logos = is_logos(row["target_module"]) and row["callee"] in paths
        if direct or via_logos:
            boundary.append({**row, "path": [row["caller"]] + paths[row["callee"]],
                             "boundary": "direct" if direct else "via Logos"})
    return {"metric": "static base-LCNF application/reference sites (proof-erased)",
            "scope": scope, "logos_sites": len(logos), "logos": logos,
            "spec_boundary_sites": len(boundary), "spec_boundary": boundary}


def report(data: dict, *, symbols: bool, files: bool, sites: bool):
    rows = data["logos"]
    print("Logos runtime references: " + data["metric"])
    print("Callers: " + ("(2) solver code" if data["scope"] == "solver" else "(1) TCB/spec and (2) solver code"))
    print("Includes unused compiled definitions; excludes constructors, types and proofs.\n")
    counts = Counter((r["category"], r["purpose"]) for r in rows)
    for (category, group), count in sorted(counts.items()):
        print(f"  {category + ': ' + group:<52} {count:>7}")
    print(f"  {'TOTAL Logos application/reference sites':<52} {len(rows):>7}")
    print(f"  Distinct Logos targets: {len({r['callee'] for r in rows})}")
    print("\nForms:")
    for form, count in sorted(Counter(r["form"] for r in rows).items()):
        print(f"  {form:<52} {count:>7}")
    if symbols:
        print("\nBy Logos target and form:")
        for (module, name, form), count in sorted(Counter(
                (r["target_module"], r["callee"], r["form"]) for r in rows).items()):
            print(f"  {count:>6}  {name} [{module}; {form}]")
    if files:
        print("\nBy caller file:")
        for module, count in sorted(Counter(r["module"] for r in rows).items()):
            print(f"  {count:>6}  {module_path(module)}")
    boundary = data["spec_boundary"]
    print(f"\n(2) -> (1) dependency check: {'FAIL' if boundary else 'PASS'} ({len(boundary)} sites)")
    for (kind, module), count in sorted(Counter(
            (r["boundary"], r["target_module"]) for r in boundary).items()):
        print(f"  {count:>6}  {kind}: {module}")
    if sites:
        print("\nLogos sites (locations identify the containing declaration):")
        for row in rows:
            print(f"  {module_path(row['module'])}:{row['line']}  {row['caller']} -> {row['callee']} ({row['form']})")
        print("\nTCB/spec dependency paths:")
        for row in boundary:
            print(f"  {module_path(row['module'])}:{row['line']}  " + " -> ".join(row["path"]))
    print("\nUse --symbols, --files, --sites or --json for details; --check-no-spec enforces the boundary.")
    print("Named references are followed transitively; dynamic calls through variables are not resolved.")
    print("Early compiler simplification/inlining/specialization can remove or duplicate source calls.")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-build", action="store_true", help="use existing artifacts (caller must ensure they are current)")
    parser.add_argument("--scope", choices=("solver", "all"), default="solver")
    parser.add_argument("--symbols", action="store_true", help="counts by target function and application form")
    parser.add_argument("--files", action="store_true", help="counts by caller file")
    parser.add_argument("--sites", action="store_true", help="list declarations/locations and spec dependency paths")
    parser.add_argument("--json", action="store_true", help="machine-readable report with all sites")
    parser.add_argument("--check-no-spec", action="store_true", help="exit 1 if solver runtime references reach the TCB/spec")
    args = parser.parse_args()
    modules = []
    for path in lean_files(ROOT):
        rel = path.relative_to(ROOT).as_posix()
        if category_of(rel) in {"solver", "spec"} and not rel.startswith("verification/"):
            modules.append(rel.removesuffix(".lean").replace("/", "."))
    try:
        if not args.no_build:
            subprocess.run(["lake", "build", *["+" + m for m in modules]], cwd=ROOT,
                           stdout=sys.stderr, check=True)
        spec = logos_spec_modules()
        result = subprocess.run(
            ["lake", "env", "lean", "--run", "scripts/LogosRuntime.lean", *modules],
            cwd=ROOT, capture_output=True, text=True, check=True,
        )
        rows = [json.loads(line) for line in result.stdout.splitlines() if line.strip()]
        data = analyze(rows, spec, args.scope)
    except (OSError, subprocess.CalledProcessError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        if isinstance(error, subprocess.CalledProcessError):
            print((error.stdout or "") + (error.stderr or ""), file=sys.stderr)
        return 2
    if args.json:
        print(json.dumps(data, indent=2))
    else:
        report(data, symbols=args.symbols, files=args.files, sites=args.sites)
    return 1 if args.check_no_spec and data["spec_boundary_sites"] else 0


if __name__ == "__main__":
    sys.exit(main())
