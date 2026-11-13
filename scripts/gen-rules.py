#!/usr/bin/env python3
"""Generate telos's rule table from the CPC Eunoia signature.

Reads the `declare-rule` forms of the signature Logos compiled
(`install/defs/Cpc.cached.eo` in the pinned Logos checkout) and writes
`Telos/Rules/Generated.lean`: one `RuleSpec` per rewrite rule whose left-hand side
uses only operators telos has kinds for. Also writes `Telos/Rules/RuleNames.lean`,
the Eunoia name of every `CRule`, for printing proofs.

The output is untrusted data. A wrong entry only means a missed rewrite, since
every step is validated by Logos's checker (see `Telos/Rules/Pattern.lean`).

Usage:
  scripts/gen-rules.py            regenerate Telos/Rules/{Generated,RuleNames}.lean
  scripts/gen-rules.py --check    exit 1 if either is out of date
  scripts/gen-rules.py --report   also list the rules skipped, and why
"""

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LOGOS = ROOT / ".lake" / "packages" / "Cpc"
SIGNATURE = LOGOS / "install" / "defs" / "Cpc.cached.eo"
LOGOS_LEAN = LOGOS / "Cpc" / "Logos.lean"
OUTPUT = ROOT / "Telos" / "Rules" / "Generated.lean"
NAMES_OUTPUT = ROOT / "Telos" / "Rules" / "RuleNames.lean"

# Eunoia operator -> telos Kind. Keep in line with `Kind.eoShape`
# (Telos/Node/ToEo.lean), read in the other direction.
KINDS = {
    "not": "NOT",
    "and": "AND",
    "or": "OR",
    "=>": "IMPLIES",
    "xor": "XOR",
    "=": "EQUAL",
    "ite": "ITE",
    "+": "ADD",
    "*": "MULT",
    "/": "DIVISION",
    "div": "INTS_DIVISION",
    "mod": "INTS_MODULUS",
    "abs": "ABS",
    "<": "LT",
    "<=": "LEQ",
    ">": "GT",
    ">=": "GEQ",
    "to_real": "TO_REAL",
    "to_int": "TO_INTEGER",
    "is_int": "IS_INTEGER",
}
# Operators whose kind depends on the number of arguments.
KINDS_BY_ARITY = {("-", 1): "NEG", ("-", 2): "SUB"}
# Kinds whose applications are `:right-assoc-nil`, where `:list` variables match
# a run of children.
NARY = {"AND", "OR", "ADD", "MULT"}
CONSTS = {"true": ".const (.boolean true)", "false": ".const (.boolean false)"}


class Skip(Exception):
    pass


def tokenize(src):
    src = re.sub(r";[^\n]*", "", src)
    return re.findall(r'\(|\)|"(?:[^"]|"")*"|[^\s()]+', src)


def parse_all(toks):
    out, i = [], 0

    def parse(i):
        if toks[i] == "(":
            lst, i = [], i + 1
            while toks[i] != ")":
                x, i = parse(i)
                lst.append(x)
            return lst, i + 1
        return toks[i], i + 1

    while i < len(toks):
        f, i = parse(i)
        out.append(f)
    return out


def show(x):
    return x if isinstance(x, str) else "(" + " ".join(map(show, x)) + ")"


def crule_names():
    names = set()
    for m in re.finditer(r"^\s*\|\s*(\w+)\s*:\s*CRule\s*$", LOGOS_LEAN.read_text(), re.M):
        names.add(m.group(1))
    return names


def lean_string(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def spec_of_rule(form, crules):
    name, params = form[1], form[2]
    attrs, key = {}, None
    for x in form[3:]:
        if isinstance(x, str) and x.startswith(":"):
            key = x
            attrs[key] = None
        elif key is not None:
            attrs[key] = x
            key = None
        else:
            raise Skip(f"unexpected attribute value {show(x)}")
    for bad in (":premise-list", ":assumption", ":requires", ":arg-list", ":sorry"):
        if bad in attrs:
            raise Skip(f"uses {bad}")
    concl = attrs.get(":conclusion")
    if not (isinstance(concl, list) and len(concl) == 3 and concl[0] == "="):
        raise Skip("conclusion is not an equality")
    crule = name.replace("-", "_")
    if crule not in crules:
        raise Skip(f"no CRule.{crule}")

    variables, is_list = {}, {}
    for p in params:
        vname, attrs_p = p[0], p[2:]
        if vname.startswith("@"):
            continue  # implicit parameter, inferred by Logos from the arguments
        variables[vname] = len(variables)
        is_list[vname] = ":list" in attrs_p

    def pat(t, parent_kind=None):
        if isinstance(t, str):
            if t in variables:
                if is_list[t]:
                    if parent_kind not in NARY:
                        raise Skip(f"list variable {t} outside an n-ary operator")
                    return f".listVar {variables[t]}"
                return f".var {variables[t]}"
            if t in CONSTS:
                return CONSTS[t]
            if re.fullmatch(r"-?[0-9]+", t):
                return f".const (.integer ({t}))"
            m = re.fullmatch(r"(-?[0-9]+)/([0-9]+)", t)
            if m:
                return f".const (.rational (mkRat ({m.group(1)}) {m.group(2)}))"
            raise Skip(f"symbol {t}")
        head = t[0] if t and isinstance(t[0], str) else None
        kind = KINDS.get(head) or KINDS_BY_ARITY.get((head, len(t) - 1))
        if kind is None:
            raise Skip(f"operator {show(t[0]) if t else '()'}")
        args = [pat(a, kind) for a in t[1:]]
        return f".app .{kind} [{', '.join(args)}]"

    if not isinstance(concl[1], list):
        raise Skip("left-hand side is not an application")
    lhs = pat(concl[1])
    args_form = attrs.get(":args", [])
    if not isinstance(args_form, list) or not all(isinstance(a, str) and a in variables for a in args_form):
        raise Skip("arguments are not plain variables")
    premises = []
    for prem in attrs.get(":premises", []) or []:
        if not (isinstance(prem, list) and len(prem) == 3 and prem[0] == "="):
            raise Skip("premise is not an equality")
        premises.append(pat(prem[1]))
    lhs_vars = set(re.findall(r"\.(?:listVar|var) (\d+)", lhs))
    if {str(variables[a]) for a in args_form} - lhs_vars:
        raise Skip("an argument does not occur in the left-hand side")
    args_str = ", ".join(str(variables[a]) for a in args_form)
    return (
        f"  {{ name := {lean_string(name)}, rule := .{crule}, numVars := {len(variables)},\n"
        f"    args := [{args_str}],\n"
        f"    lhs := {lhs},\n"
        f"    premises := [{', '.join(premises)}] }}"
    )


HEADER = """\
-- This file is generated by scripts/gen-rules.py from the CPC signature that
-- Logos compiled (install/defs/Cpc.cached.eo in the pinned Logos checkout).
-- Do not edit. Regenerate with: python3 scripts/gen-rules.py
import Telos.Rules.Pattern

namespace Telos

/-- The rewrite rules of CPC whose left-hand sides telos can match:
{count} of the signature's {total} rules. -/
def generatedRules : List RuleSpec := [
"""

FOOTER = """\
]

end Telos
"""


def generate():
    forms = parse_all(tokenize(SIGNATURE.read_text()))
    rules = [f for f in forms if isinstance(f, list) and f and f[0] == "declare-rule"]
    crules = crule_names()
    specs, skipped = [], []
    for r in rules:
        try:
            specs.append(spec_of_rule(r, crules))
        except Skip as e:
            skipped.append((r[1], str(e)))
    text = HEADER.format(count=len(specs), total=len(rules)) + ",\n".join(specs) + "\n" + FOOTER
    return text, specs, skipped


NAMES_HEADER = """\
-- This file is generated by scripts/gen-rules.py from the CPC signature that
-- Logos compiled (install/defs/Cpc.cached.eo in the pinned Logos checkout).
-- Do not edit. Regenerate with: python3 scripts/gen-rules.py
import Cpc.Logos

namespace Telos

/-- The Eunoia name of each CPC rule, for printing proofs. -/
def ruleName : Eo.CRule → String
"""


def generate_names():
    forms = parse_all(tokenize(SIGNATURE.read_text()))
    crules = crule_names()
    arms, covered = [], set()
    for f in forms:
        if isinstance(f, list) and f and f[0] == "declare-rule":
            crule = f[1].replace("-", "_")
            if crule in crules and crule not in covered:
                covered.add(crule)
                arms.append(f"  | .{crule} => {lean_string(f[1])}")
    if covered != crules:
        arms.append('  | _ => "unknown-rule"')
    return NAMES_HEADER + "\n".join(arms) + "\n\nend Telos\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--report", action="store_true")
    a = ap.parse_args()
    if not SIGNATURE.exists():
        sys.exit(f"error: {SIGNATURE} not found; run `lake build` first to fetch Logos")
    text, specs, skipped = generate()
    if a.report:
        for name, why in skipped:
            print(f"skipped {name}: {why}")
    print(f"{len(specs)} rules generated, {len(skipped)} skipped", file=sys.stderr)
    names = generate_names()
    if a.check:
        for path, content in ((OUTPUT, text), (NAMES_OUTPUT, names)):
            if not path.exists() or path.read_text() != content:
                sys.exit(f"error: {path.relative_to(ROOT)} is out of date; run scripts/gen-rules.py")
        return
    OUTPUT.write_text(text)
    NAMES_OUTPUT.write_text(names)


if __name__ == "__main__":
    main()
