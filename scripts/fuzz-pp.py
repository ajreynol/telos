#!/usr/bin/env python3
"""Differential testing of telos's preprocessor against cvc5's.

Runs `telos --post-asserts` and `cvc5 -o post-asserts` on benchmarks, with
cvc5's passes that telos does not port yet switched off (`CVC5_OPTS` below), and
compares the preprocessed assertions, in order, and the declarations, as a set.
Assertions are compared as `fuzz.py` compares terms: identical, or up to the
names of bound variables, the orientation of equalities, and the order of
commutative arguments (which cvc5 takes from node ids). The `define-fun`s of
the variables solved by non-clausal simplification are compared with the
declarations, as a set. The input's `define-fun`s are macros in telos
(`Telos/Frontend/PostAsserts.lean`), so for a benchmark with `define-fun`s
cvc5's `define-fun` lines are ignored, and so are the
`(assert true)` that cvc5 keeps in their place (all `(assert true)`, on both
sides).

Skolems (`@purify_2`, `@int_div_by_zero_3`, …) are numbered by cvc5 in the order
it creates them, and by telos in the order they occur, so both outputs are
compared with their skolems renumbered in order of first occurrence. Last, the
assertions are compared up to Int/Real casts: cvc5's arithmetic is mixed
internally, and `-o post-asserts` prints it so (`(+ r (* -1 x))`, `0`), where
telos, like cvc5's `simplify`, keeps the casts (`(+ r (to_real (* -1 x)))`, `0/1`).

The benchmarks are random (default): scripts of 1 to 4 assertions, each a
random Boolean term from `telos-fuzz` (with the declarations of `fuzz.py`), or
the SMT-LIB files given as arguments. cvc5 runs with proofs on
(`--produce-proofs`), which telos matches (`Telos/Preprocess/Options.lean`).

With `--logics`, a random benchmark declares only the symbols it uses, and its
logic is the smallest that cvc5 accepts for it (quantifier-free if it can be,
with the theories of its declarations and the least arithmetic), so that cvc5's
defaults that depend on the logic are compared. With `--options`, each
benchmark is run, on both sides, with one of the preprocessing options telos
has (`PP_OPTIONS`), or none, at random: safe mode allows one regular option.

Usage:
  scripts/fuzz-pp.py [--cvc5 PATH] [--seed N] [--count N] [--depth N] [--show N]
                     [--logics] [--options] [MODE]
  scripts/fuzz-pp.py [--cvc5 PATH] [--show N] FILE.smt2 ...

MODE is one of `fuzz.py`'s term modes (`--arith`, `--uf`, …). Build first:
`lake build telos telos-fuzz`.
"""
import argparse
import os
import random
import re
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
CVC5_OPTS = []
MODES = ["arith", "uf", "bv", "arrays", "mixed", "strings", "sets", "datatypes", "quantifiers"]
# cvc5's regular options that change preprocessing, and that telos has.
PP_OPTIONS = ["--simplification=none", "--arith-rewrite-equalities",
              "--no-arith-rewrite-equalities", "--no-static-learning",
              "--no-arith-static-learning"]
# The arithmetic of logics, least first.
ARITH = ["", "LIA", "LRA", "LIRA", "NIA", "NRA", "NIRA"]


BUILTIN = {"declare-const", "declare-fun", "declare-sort", "declare-datatypes", "par", "T", "S",
           "0", "1", "2", "4", "_", "Int", "Real", "Bool", "String", "BitVec", "Array", "Set", "Tuple"}


def declared(line):
    """The names a prelude line declares (for a datatype: its sorts, constructors
    and selectors), and the names it uses."""
    toks = re.findall(r"[^\s()]+", line)
    if line.startswith("(declare-datatypes"):
        names = set(toks) - BUILTIN
        return names, names
    return {toks[1]}, set(toks[2:]) - BUILTIN


def prelude_for(body):
    """The declarations of `fuzz.PRELUDE` that `body` needs (without `set-logic`),
    in order, and the theory letters of the logics they need."""
    lines = [l for l in fuzz.PRELUDE.splitlines() if l and not l.startswith("(set-logic")]
    want = set(re.findall(r"[^\s()]+", body))
    keep = set()
    changed = True
    while changed:
        changed = False
        for i, l in enumerate(lines):
            names, uses = declared(l)
            if i not in keep and names & want:
                keep.add(i)
                want |= uses
                changed = True
    out = [l for i, l in enumerate(lines) if i in keep]
    text = " ".join(out) + " " + body
    theories = set()
    if re.search(r"\bU\b", text) or "(declare-fun" in text: theories.add("UF")
    if "Array" in text: theories.add("A")
    if "BitVec" in text or "#b" in body: theories.add("BV")
    if "declare-datatypes" in text or "Tuple" in text or "tuple" in body: theories.add("DT")
    if "String" in text or "str." in body or "re." in body: theories.add("S")
    if "Set" in text or "set." in body: theories.add("FS")
    return out, theories


def logic_candidates(theories, quantified):
    order = ["A", "UF", "BV", "DT", "S"]
    base = "".join(t for t in order if t in theories)
    tail = "FS" if "FS" in theories else ""
    qs = [""] if quantified else ["QF_", ""]
    out = []
    for q in qs:
        for ar in ARITH:
            core = base + ar + tail
            out.append(q + (core if core else "SAT" if q == "" else "SAT"))
    return out + ["ALL"]


def post_asserts(text):
    """The declarations (a set) and assertions (a list) of a post-asserts output."""
    lines = text.splitlines()
    try:
        lines = lines[lines.index(";; post-asserts start") + 1:lines.index(";; post-asserts end")]
    except ValueError:
        return None
    decls = {l for l in lines if l.startswith("(declare-") or l.startswith("(define-fun")}
    asserts = [l[len("(assert "):-1] for l in lines if l.startswith("(assert ")]
    return decls, asserts


SKOLEM = re.compile(r"@([a-z_]+?)_(\d+)\b")


def renumber_skolems(asserts, decls):
    """The assertions and declarations with skolems renumbered `@purify_#1`, …
    in order of first occurrence (in the assertions, then the declarations)."""
    names = {}
    for text in list(asserts) + sorted(decls):
        for m in SKOLEM.finditer(text):
            names.setdefault(m.group(0), f"@{m.group(1)}_#{len(names) + 1}")
    sub = lambda text: SKOLEM.sub(lambda m: names[m.group(0)], text)
    # declarations up to spacing between parentheses (cvc5 prints `(par (T)((c)))`)
    norm = lambda d: re.sub(r"\)\s+\(", ")(", d)
    return [sub(a) for a in asserts], {norm(sub(d)) for d in decls}


DEF0 = re.compile(r"\(define-fun (\S+) \(\) ")


def split_defs(decls):
    """The `define-fun`s of constants among `decls`, by name."""
    out = {}
    for d in decls:
        m = DEF0.match(d)
        if m:
            out[m.group(1)] = d
    return out


def def_body(d):
    """The body of `(define-fun x () T body)`: the text after the sort."""
    e = fuzz.parse_sexpr(d)
    return print_sexpr(e[4])


def print_sexpr(e):
    return e if isinstance(e, str) else "(" + " ".join(print_sexpr(x) for x in e) + ")"


def read_labeled(x):
    """A term, or `[x] t` (the body of `x`'s `define-fun`) as `["[x]", t]`."""
    m = re.match(r"\[(\S+)\] (.*)", x, re.S)
    return [f"[{m.group(1)}]", fuzz.read_term(m.group(2))] if m else fuzz.read_term(x)


def cast_free(e):
    """`e` without Int/Real casts: `(to_real t)` is `t`, and `n/1` is `n`."""
    if isinstance(e, str):
        return e[:-2] if e.endswith("/1") and is_number(e[:-2]) else e
    if len(e) == 2 and e[0] == "to_real":
        return cast_free(e[1])
    return [cast_free(x) for x in e]


def is_number(t):
    return t.lstrip("-").isdigit()


def run(cmd, path, timeout=120):
    try:
        r = subprocess.run(cmd + [str(path)], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, f"timeout ({timeout}s)"
    return r.stdout if r.returncode == 0 else None, r.stderr.strip()


def compare(ours, theirs):
    """`same`, `renamed`, `oriented`, `ordered` or None."""
    if ours == theirs:
        return "same"
    o, t = [fuzz.alpha_free(read_labeled(x)) for x in ours], [fuzz.alpha_free(read_labeled(x)) for x in theirs]
    if o == t:
        return "renamed"
    if [fuzz.orient_free(x) for x in o] == [fuzz.orient_free(x) for x in t]:
        return "oriented"
    if [fuzz.order_free(x) for x in o] == [fuzz.order_free(x) for x in t]:
        return "ordered"
    if [fuzz.order_free(cast_free(x)) for x in o] == [fuzz.order_free(cast_free(x)) for x in t]:
        return "casts"
    return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cvc5", default=os.environ.get("CVC5") or shutil.which("cvc5") or "cvc5")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=200, help="random benchmarks")
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument("--show", type=int, default=5, help="mismatches to print")
    ap.add_argument("--logics", action="store_true", help="the smallest logic of each benchmark")
    ap.add_argument("--options", action="store_true", help="one random preprocessing option")
    for m in MODES:
        ap.add_argument(f"--{m}", action="store_true")
    ap.add_argument("files", nargs="*")
    a = ap.parse_args()
    if not TELOS.exists():
        sys.exit("error: build telos first: lake build telos telos-fuzz")
    cvc5 = [a.cvc5, "-o", "post-asserts", "--print-arith-lit-token", "--produce-proofs",
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
            if a.logics:
                decls, theories = prelude_for(body)
                quantified = "forall" in body or "exists" in body
                for logic in logic_candidates(theories, quantified):
                    path.write_text(f"(set-logic {logic})\n" + "\n".join(decls) + "\n" + body + "(check-sat)\n")
                    # whether cvc5 accepts the logic: preprocessing is enough
                    try:
                        r = subprocess.run(cvc5 + ["--preprocess-only", str(path)],
                                           capture_output=True, text=True, timeout=60)
                    except subprocess.TimeoutExpired:
                        continue
                    if r.returncode == 0 and "(error" not in r.stdout:
                        break
            else:
                path.write_text(fuzz.PRELUDE + body + "(check-sat)\n")
            files.append(path)
    counts = {"same": 0, "renamed": 0, "oriented": 0, "ordered": 0, "casts": 0}
    mismatches, failures = [], []
    # no need to solve the benchmarks: post-asserts is printed after preprocessing
    cvc5 = cvc5 + ["--preprocess-only"]
    orng = random.Random(a.seed + 1)
    for path in files:
        opt = []
        if a.options:
            choice = orng.randrange(len(PP_OPTIONS) + 1)
            opt = PP_OPTIONS[choice:choice + 1]
        ours, err = run([str(TELOS), "--post-asserts", *opt], path)
        theirs, cerr = run(cvc5 + opt, path)
        if ours is None or theirs is None:
            failures.append((path, err if ours is None else cerr))
            continue
        o, t = post_asserts(ours), post_asserts(theirs)
        if o is None or t is None:
            failures.append((path, "no post-asserts output"))
            continue
        (od, oa), (td, ta) = o, t
        oa, od = renumber_skolems(oa, od)
        ta, td = renumber_skolems(ta, td)
        if "define-fun" in path.read_text():
            oa = [x for x in oa if x != "true"]
            ta = [x for x in ta if x != "true"]
            od = {d for d in od if not d.startswith("(define-fun")}
            td = {d for d in td if not d.startswith("(define-fun")}
        # the solved variables' `define-fun`s are compared as the assertions are
        # (their bodies up to orientation, …), in the order of their names
        ofs, tfs = split_defs(od), split_defs(td)
        od, td = od - set(ofs.values()), td - set(tfs.values())
        if ofs.keys() == tfs.keys():
            oa = oa + [f"[{k}] " + def_body(ofs[k]) for k in sorted(ofs)]
            ta = ta + [f"[{k}] " + def_body(tfs[k]) for k in sorted(tfs)]
        else:
            od, td = od | set(ofs.values()), td | set(tfs.values())
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
          f"{counts['ordered']} up to the order of commutative arguments, {counts['casts']} up to Int/Real "
          f"casts, {len(mismatches)} different, "
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
