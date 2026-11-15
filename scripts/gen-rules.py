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
PROGRAMS_OUTPUT = ROOT / "Telos" / "Rules" / "Programs.lean"

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
    "/_total": "DIVISION_TOTAL",
    "div_total": "INTS_DIVISION_TOTAL",
    "mod_total": "INTS_MODULUS_TOTAL",
    "<": "LT",
    "<=": "LEQ",
    ">": "GT",
    ">=": "GEQ",
    "to_real": "TO_REAL",
    "to_int": "TO_INTEGER",
    "is_int": "IS_INTEGER",
    "int.pow2": "POW2",
    "int.log2": "INTS_LOG2",
    "int.ispow2": "INTS_ISPOW2",
    "concat": "BITVECTOR_CONCAT",
    "bvand": "BITVECTOR_AND",
    "bvor": "BITVECTOR_OR",
    "bvxor": "BITVECTOR_XOR",
    "bvadd": "BITVECTOR_ADD",
    "bvmul": "BITVECTOR_MULT",
    "bvnot": "BITVECTOR_NOT",
    "bvneg": "BITVECTOR_NEG",
    "bvredor": "BITVECTOR_REDOR",
    "bvredand": "BITVECTOR_REDAND",
    "bvnego": "BITVECTOR_NEGO",
    "@bvsize": "BITVECTOR_SIZE",
    "bvnand": "BITVECTOR_NAND",
    "bvnor": "BITVECTOR_NOR",
    "bvxnor": "BITVECTOR_XNOR",
    "bvcomp": "BITVECTOR_COMP",
    "bvsub": "BITVECTOR_SUB",
    "bvudiv": "BITVECTOR_UDIV",
    "bvurem": "BITVECTOR_UREM",
    "bvsdiv": "BITVECTOR_SDIV",
    "bvsrem": "BITVECTOR_SREM",
    "bvsmod": "BITVECTOR_SMOD",
    "bvshl": "BITVECTOR_SHL",
    "bvlshr": "BITVECTOR_LSHR",
    "bvashr": "BITVECTOR_ASHR",
    "bvult": "BITVECTOR_ULT",
    "bvule": "BITVECTOR_ULE",
    "bvugt": "BITVECTOR_UGT",
    "bvuge": "BITVECTOR_UGE",
    "bvslt": "BITVECTOR_SLT",
    "bvsle": "BITVECTOR_SLE",
    "bvsgt": "BITVECTOR_SGT",
    "bvsge": "BITVECTOR_SGE",
    "bvultbv": "BITVECTOR_ULTBV",
    "bvsltbv": "BITVECTOR_SLTBV",
    "bvuaddo": "BITVECTOR_UADDO",
    "bvsaddo": "BITVECTOR_SADDO",
    "bvumulo": "BITVECTOR_UMULO",
    "bvsmulo": "BITVECTOR_SMULO",
    "bvusubo": "BITVECTOR_USUBO",
    "bvssubo": "BITVECTOR_SSUBO",
    "bvsdivo": "BITVECTOR_SDIVO",
    "bvite": "BITVECTOR_ITE",
    "select": "SELECT",
    "str.++": "STRING_CONCAT",
    "re.++": "REGEXP_CONCAT",
    "re.inter": "REGEXP_INTER",
    "re.union": "REGEXP_UNION",
    "str.len": "STRING_LENGTH",
    "str.substr": "STRING_SUBSTR",
    "str.update": "STRING_UPDATE",
    "str.at": "STRING_CHARAT",
    "str.contains": "STRING_CONTAINS",
    "str.<": "STRING_LT",
    "str.<=": "STRING_LEQ",
    "str.indexof": "STRING_INDEXOF",
    "str.indexof_re": "STRING_INDEXOF_RE",
    "str.replace": "STRING_REPLACE",
    "str.replace_all": "STRING_REPLACE_ALL",
    "str.replace_re": "STRING_REPLACE_RE",
    "str.replace_re_all": "STRING_REPLACE_RE_ALL",
    "str.prefixof": "STRING_PREFIX",
    "str.suffixof": "STRING_SUFFIX",
    "str.is_digit": "STRING_IS_DIGIT",
    "str.from_int": "STRING_ITOS",
    "str.to_int": "STRING_STOI",
    "str.to_code": "STRING_TO_CODE",
    "str.from_code": "STRING_FROM_CODE",
    "str.to_lower": "STRING_TO_LOWER",
    "str.to_upper": "STRING_TO_UPPER",
    "str.rev": "STRING_REV",
    "str.to_re": "STRING_TO_REGEXP",
    "str.in_re": "STRING_IN_REGEXP",
    "re.none": "REGEXP_NONE",
    "re.all": "REGEXP_ALL",
    "re.allchar": "REGEXP_ALLCHAR",
    "re.diff": "REGEXP_DIFF",
    "re.*": "REGEXP_STAR",
    "re.+": "REGEXP_PLUS",
    "re.opt": "REGEXP_OPT",
    "re.range": "REGEXP_RANGE",
    "re.comp": "REGEXP_COMPLEMENT",
    "store": "STORE",
    "ubv_to_int": "BITVECTOR_UBV_TO_INT",
    "sbv_to_int": "BITVECTOR_SBV_TO_INT",
}
# The signature's sequence names for the string operators (`(define seq.extract
# () str.substr)`, ...).
SEQ_ALIASES = {
    "seq.len": "str.len", "seq.++": "str.++", "seq.extract": "str.substr",
    "seq.contains": "str.contains", "seq.replace": "str.replace",
    "seq.replace_all": "str.replace_all", "seq.indexof": "str.indexof",
    "seq.prefixof": "str.prefixof", "seq.suffixof": "str.suffixof", "seq.rev": "str.rev",
    "seq.update": "str.update", "seq.at": "str.at",
}
# Fixed types of rule parameters, as `TypeNode` constructors.
VAR_TYPES = {"String": "string", "Int": "integer", "Real": "real", "Bool": "boolean",
             "RegLan": "regExp"}
# Nullary operators, written as symbols.
NULLARY = {"re.allchar": "REGEXP_ALLCHAR", "re.none": "REGEXP_NONE", "re.all": "REGEXP_ALL"}
# Indexed operators: kind and number of indices. In the signature the indices
# come first, as in `(extract i j x)`.
INDEXED = {
    "extract": ("BITVECTOR_EXTRACT", 2),
    "int_to_bv": ("INT_TO_BITVECTOR", 1),
    "re.^": ("REGEXP_REPEAT", 1),
    "re.loop": ("REGEXP_LOOP", 2),
    "repeat": ("BITVECTOR_REPEAT", 1),
    "zero_extend": ("BITVECTOR_ZERO_EXTEND", 1),
    "sign_extend": ("BITVECTOR_SIGN_EXTEND", 1),
    "rotate_left": ("BITVECTOR_ROTATE_LEFT", 1),
    "rotate_right": ("BITVECTOR_ROTATE_RIGHT", 1),
}
# Operators whose kind depends on the number of arguments.
KINDS_BY_ARITY = {("-", 1): "NEG", ("-", 2): "SUB"}
# Kinds whose applications are `:right-assoc-nil`, where `:list` variables match
# a run of children.
NARY = {"AND", "OR", "ADD", "MULT", "BITVECTOR_CONCAT", "BITVECTOR_AND", "BITVECTOR_OR",
        "BITVECTOR_XOR", "BITVECTOR_ADD", "BITVECTOR_MULT",
        "STRING_CONCAT", "REGEXP_CONCAT", "REGEXP_INTER", "REGEXP_UNION"}
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


def expand_defines(t, env=None):
    """`t` with every `(eo::define ((v E) ...) body)` replaced by `body` with each
    `v` replaced by its definition."""
    env = env or {}
    if isinstance(t, str):
        return env.get(t, t)
    if t and t[0] == "eo::define" and len(t) == 3:
        env = dict(env)
        for v, e in t[1]:
            env[v] = expand_defines(e, env)
        return expand_defines(t[2], env)
    return [expand_defines(x, env) for x in t]


def spec_of_rule(form, crules):
    form = expand_defines(form)
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

    variables, is_list, var_types = {}, {}, []
    for p in params:
        vname, attrs_p = p[0], p[2:]
        if vname.startswith("@"):
            continue  # implicit parameter, inferred by Logos from the arguments
        variables[vname] = len(variables)
        is_list[vname] = ":list" in attrs_p
        var_types.append(VAR_TYPES.get(p[1]) if isinstance(p[1], str) else None)

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
            if t in NULLARY:
                return f".app .{NULLARY[t]} []"
            m = re.fullmatch(r'"((?:[^"]|"")*)"', t)
            if m:
                codes = [ord(c) for c in m.group(1).replace('""', '"')]
                return f".const (.string [{', '.join(map(str, codes))}])"
            if re.fullmatch(r"-?[0-9]+", t):
                return f".const (.integer ({t}))"
            m = re.fullmatch(r"(-?[0-9]+)/([0-9]+)", t)
            if m:
                return f".const (.rational (mkRat ({m.group(1)}) {m.group(2)}))"
            raise Skip(f"symbol {t}")
        head = t[0] if t and isinstance(t[0], str) else None
        head = SEQ_ALIASES.get(head, head)
        if head == "@bv" and len(t) == 3:
            return f".bvLit ({pat(t[1])}) ({pat(t[2])})"
        if head in INDEXED:
            kind, k = INDEXED[head]
            if len(t) != k + 2:
                raise Skip(f"arity of {head}")
            idx = [pat(a) for a in t[1:1 + k]]
            args = [pat(a, kind) for a in t[1 + k:]]
            return f".indexed .{kind} [{', '.join(idx)}] [{', '.join(args)}]"
        kind = KINDS.get(head) or KINDS_BY_ARITY.get((head, len(t) - 1))
        if kind is None:
            raise Skip(f"operator {show(t[0]) if t else '()'}")
        args = [pat(a, kind) for a in t[1:]]
        return f".app .{kind} [{', '.join(args)}]"

    if not isinstance(concl[1], list):
        raise Skip("left-hand side is not an application")
    lhs = pat(concl[1])
    args_form = attrs.get(":args", [])
    if not isinstance(args_form, list):
        raise Skip("arguments are not plain variables")
    # A type argument such as `(Seq @T0)` is the declared type of a variable.
    declared = {p[0]: p[1] for p in params}
    type_args, plain = [], []
    for pos, a in enumerate(args_form):
        if isinstance(a, str) and a in variables:
            plain.append(a)
        else:
            owner = next((v for v in variables if declared.get(v) == a), None)
            if owner is None:
                raise Skip("arguments are not plain variables")
            type_args.append((pos, variables[owner]))
    args_form = plain
    premises = []
    bound = set(re.findall(r"\.(?:listVar|var) (\d+)", lhs))
    for prem in attrs.get(":premises", []) or []:
        if not (isinstance(prem, list) and len(prem) == 3 and prem[0] == "="):
            raise Skip("premise is not an equality")
        a, b = prem[1], prem[2]
        other = None
        if isinstance(a, str) and a in variables and (str(variables[a]) not in bound or isinstance(b, list)):
            # `(= v E)` defines `v`, or checks it against the value of the term `E`:
            # proven by evaluating `E`, then `symm`.
            expr, value, symm = pat(b), pat(a), "true"
        elif isinstance(b, list) and b and b[0] != "@bv":
            # `(= A B)` between two terms: both are evaluated.
            expr, value, symm, other = pat(a), ".const (.boolean true)", "false", pat(b)
        else:
            expr, value, symm = pat(a), pat(b), "false"
        other_str = f", other := some ({other})" if other else ""
        premises.append(f"{{ expr := {expr}, value := {value}, symm := {symm}{other_str} }}")
        bound |= set(re.findall(r"\.(?:listVar|var) (\d+)", value))
    lhs_vars = bound
    if {str(variables[a]) for a in args_form} - lhs_vars:
        raise Skip("an argument does not occur in the left-hand side")
    args_str = ", ".join(str(variables[a]) for a in args_form)
    return (
        f"  {{ name := {lean_string(name)}, rule := .{crule}, numVars := {len(variables)},\n"
        f"    args := [{args_str}],\n"
        + (f"    typeArgs := [{', '.join(f'({p}, {i})' for p, i in type_args)}],\n" if type_args else "")
        + f"    lhs := {lhs},\n"
        f"    premises := [{', '.join(premises)}],\n"
        f"    varTypes := [{', '.join('some .' + t if t else 'none' for t in var_types)}] }}"
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


# Rules whose argument is `(= l r)` and whose `:requires` is `(f l) r`: the
# right-hand side `f l` is extracted from the rule's compiled program, so that
# telos can compute it (`(name, Lean name, lhs pattern variables)`).
PROGRAM_RULES = [
    ("bv_umulo_elim", "umuloElim", ["a", "b"]),
    ("bv_smulo_elim", "smuloElim", ["a", "b"]),
]

PROGRAMS_HEADER = """\
-- This file is generated by scripts/gen-rules.py from Logos's compiled rule
-- programs (Cpc/Logos.lean in the pinned Logos checkout). Do not edit.
-- Regenerate with: python3 scripts/gen-rules.py
import Cpc.Logos

/-!
The right-hand sides that some CPC rules compute in their `:requires`, as Lean
functions: the first argument of the `__eo_requires` the rule's program ends
with. They are untrusted: the rule step that uses the result is checked.
-/

open Eo SmtEval

namespace Telos.Programs
"""


def first_arg(text, start):
    """The first argument of the application starting at `text[start] == '('`."""
    i = start + 1
    while text[i] != " ":
        i += 1
    i += 1
    depth, j = 0, i
    while True:
        c = text[j]
        if c == "(":
            depth += 1
        elif c == ")":
            if depth == 0:
                return text[i:j]
            depth -= 1
        elif c == " " and depth == 0:
            return text[i:j]
        j += 1


def generate_programs():
    src = LOGOS_LEAN.read_text()
    out = [PROGRAMS_HEADER]
    for crule, lean_name, params in PROGRAM_RULES:
        head = f"def __eo_prog_{crule} : Term -> Term\n"
        i = src.index(head)
        j = src.index("\n  | _ => Term.Stuck", i)
        lines = src[i:j].split("\n")[2:]
        body, last = lines[:-1], lines[-1]
        k = last.index("(__eo_requires ")
        rhs = first_arg(last, k)
        out.append(f"\n/-- The right-hand side `{crule}` computes. -/\n"
                   f"def {lean_name} ({' '.join(params)} : Term) : Term :=\n"
                   + "\n".join(body) + "\n    " + rhs + "\n")
    out.append("\nend Telos.Programs\n")
    return "".join(out)


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
    programs = generate_programs()
    if a.check:
        for path, content in ((OUTPUT, text), (NAMES_OUTPUT, names), (PROGRAMS_OUTPUT, programs)):
            if not path.exists() or path.read_text() != content:
                sys.exit(f"error: {path.relative_to(ROOT)} is out of date; run scripts/gen-rules.py")
        return
    OUTPUT.write_text(text)
    NAMES_OUTPUT.write_text(names)
    PROGRAMS_OUTPUT.write_text(programs)


if __name__ == "__main__":
    main()
