#!/usr/bin/env python3
"""Differential testing of telos's rewriter on the lemmas of cvc5's solver.

The terms of `fuzz.py` are random; the terms cvc5's rewriter sees most are the
lemmas, conflicts and facts of its theory solvers. This script collects them
and compares the rewriter on them:

1. Random benchmarks, each a conjunction of 2 to `--size` theory literals: the
   theory atoms of random `telos-fuzz` terms (in one of `fuzz.py`'s modes),
   each asserted positively or negated.
2. cvc5 solves each benchmark with `-t im`, which prints every inference of its
   theory inference managers, before rewriting, as `(lemma ID φ)`,
   `(conflict ID φ)` or `(fact ID φ)`. `-t` needs a cvc5 built with tracing
   (`cvc5 --show-config`): `--solver`, if the reference cvc5 (`--cvc5`, which
   rewrites) is not.
3. Skolems are not SMT-LIB input, so each is abstracted: cvc5 prints it as the
   term that defines it (`--print-skolem-definitions`: `(@purify t)`), which
   tells skolems apart and gives their sort, and each distinct one becomes a
   declared symbol `sk_<id>_<n>`, applied to the bound variables it contains.
   Where cvc5 mixes Int and Real, the casts SMT-LIB needs are added.
   Formulas with cvc5-internal symbols (instantiation constants, ...) mean
   nothing outside cvc5 and are skipped.
4. The formulas, without duplicates, are rewritten by telos (`(simplify φ)`)
   and compared with cvc5's rewrites as `fuzz.py` compares terms, with the same
   semantic checks.

The report also counts the inferences by identifier and the skolems by kind,
and lists the formulas that telos or cvc5 cannot read.

Usage:
  scripts/fuzz-lemmas.py [--cvc5 PATH] [--solver PATH] [--seed N] [--count N] [--depth N]
                         [--size N] [--show N] [--save DIR] [MODE]

MODE is one of `fuzz.py`'s term modes (`--arith`, `--strings`, ...). With
`--save DIR`, the formulas are also written to `DIR`, one benchmark each (an
assertion), for `fuzz-pp.py`. Build first: `lake build telos telos-fuzz`.
"""
import argparse
import collections
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
MODES = ["arith", "uf", "bv", "arrays", "mixed", "strings", "sets", "datatypes", "quantifiers"]
# The solver's trace: skolems printed as their definitions, so that they can be
# told apart and given a sort, and no `let`s, since with
# `--print-skolem-definitions` cvc5 can print a `let` variable inside a skolem's
# definition before the `let` that binds it (`cvc5-let-skolem-bug.md`).
SOLVER_OPTS = ["-t", "im", "--print-skolem-definitions", "--dag-thresh=0", "--tlimit=5000"]
# Lines of the trace longer than this (printed without sharing) are left out.
MAX_LINE = 20000
# The Boolean connectives: a term headed by one is not a theory literal.
CONNECTIVES = {"not", "and", "or", "=>", "xor", "ite"}
BOOL_CONSTS = {"a", "b", "c", "true", "false"}
PREDICATES = CONNECTIVES | {"=", "distinct", "<", "<=", ">", ">="}
INFERENCE_KINDS = ("lemma", "conflict", "fact")


def is_bool(e):
    """`e` is a Boolean term, as far as its head tells (enough to keep `=`
    between formulas, which is Boolean structure, out of the literals)."""
    if isinstance(e, str):
        return e in BOOL_CONSTS
    return bool(e) and isinstance(e[0], str) and e[0] in PREDICATES and not (e[0] == "ite" and len(e) == 4 and not is_bool(e[2]))


def atoms(e, out):
    """The theory atoms of the formula `e`, appended to `out`."""
    if isinstance(e, str) or not e:
        return
    head = e[0] if isinstance(e[0], str) else None
    # at a Boolean position, the children of a connective are formulas too
    if head in CONNECTIVES or (head in ("=", "distinct") and any(is_bool(x) for x in e[1:])):
        for x in e[1:]:
            atoms(x, out)
        return
    out.append(e)


def print_sexpr(e):
    return e if isinstance(e, str) else "(" + " ".join(print_sexpr(x) for x in e) + ")"


def sort_str(e):
    return print_sexpr(e)


def prelude_sorts():
    """The sorts of the constants of `fuzz.PRELUDE`, and the function symbols'
    result sorts."""
    sorts = {}
    for line in fuzz.PRELUDE.splitlines():
        e = fuzz.parse_sexpr(line) if line.startswith("(declare-") else None
        if e and e[0] == "declare-const":
            sorts[e[1]] = sort_str(e[2])
        elif e and e[0] == "declare-fun":
            sorts[e[1]] = sort_str(e[3])
    return sorts


PRELUDE_SORTS = prelude_sorts()
BOOL_OPS = {"not", "and", "or", "=>", "xor", "=", "distinct", "<", "<=", ">", ">=", "str.prefixof",
            "str.suffixof", "str.contains", "str.in_re", "str.<", "str.<=", "str.is_digit",
            "set.member", "set.subset", "forall", "exists", "bvult", "bvule", "bvugt", "bvuge",
            "bvslt", "bvsle", "bvsgt", "bvsge", "is_int", "true", "false"}
INT_OPS = {"str.len", "str.indexof", "str.to_int", "str.to_code", "to_int", "div", "mod", "abs",
           "div_total", "mod_total", "ubv_to_int", "sbv_to_int", "bv2nat", "set.card", "head",
           "@strings_occur_index", "@strings_num_occur", "@strings_stoi_result",
           "@strings_stoi_non_digit", "@strings_itos_result", "@int_div_by_zero", "@mod_by_zero"}
REAL_OPS = {"/", "/_total", "to_real", "@div_by_zero"}
STRING_OPS = {"str.++", "str.substr", "str.at", "str.replace", "str.replace_all", "str.replace_re",
              "str.replace_re_all", "str.from_int", "str.from_code", "str.rev", "str.update",
              "str.to_lower", "str.to_upper", "@strings_replace_all_result",
              "@re_unfold_pos_component"}
ARITH_OPS = {"+", "-", "*"}
COMPARISONS = {"<", "<=", ">", ">=", "="}
DT_SORTS = {"nil": "Lst", "cons": "Lst", "tail": "Lst", "red": "Color", "green": "Color", "blue": "Color"}


def join(ts):
    ts = [t for t in ts if t]
    if "Real" in ts:
        return "Real"
    return ts[0] if ts else None


def bv_width(t):
    m = re.fullmatch(r"\(_ BitVec (\d+)\)", t or "")
    return int(m.group(1)) if m else None


def sort_of(e, env=None):
    """The sort of a let-free term, printed, or None if not known. `env` gives
    the sorts of bound variables."""
    env = env or {}
    if isinstance(e, str):
        if e in env:
            return env[e]
        if e in PRELUDE_SORTS:
            return PRELUDE_SORTS[e]
        if e in ("true", "false"):
            return "Bool"
        if e.startswith('"'):
            return "String"
        if e.startswith("#b"):
            return f"(_ BitVec {len(e) - 2})"
        if e.lstrip("-").isdigit():
            return "Int"
        if re.fullmatch(r"-?\d+(\.\d+|/\d+)", e):
            return "Real"
        return DT_SORTS.get(e)
    if not e:
        return None
    h = e[0]
    if isinstance(h, list) and h[:1] == ["as"] and len(h) == 3:  # `((as pcons (PL Int)) …)`
        return sort_str(h[2])
    if isinstance(h, list):  # an indexed operator
        if h[:2] == ["_", "extract"]:
            return f"(_ BitVec {int(h[2]) - int(h[3]) + 1})"
        if h[:2] in (["_", "zero_extend"], ["_", "sign_extend"]):
            w = bv_width(sort_of(e[1], env))
            return f"(_ BitVec {w + int(h[2])})" if w else None
        if h[:2] == ["_", "repeat"]:
            w = bv_width(sort_of(e[1], env))
            return f"(_ BitVec {w * int(h[2])})" if w else None
        if h[:2] in (["_", "rotate_left"], ["_", "rotate_right"]):
            return sort_of(e[1], env)
        if h[:2] == ["_", "int_to_bv"]:
            return f"(_ BitVec {h[2]})"
        if h[:2] == ["_", "is"]:
            return "Bool"
        if h[:2] == ["_", "tuple.select"]:
            t = sort_of(e[1], env)
            parts = fuzz.parse_sexpr(t) if t and t.startswith("(Tuple") else None
            return sort_str(parts[int(h[2]) + 1]) if parts else None
        if h[:2] == ["_", "re.loop"] or h[:2] == ["_", "re.^"]:
            return "RegLan"
        return None
    if h in ("forall", "exists"):
        return "Bool"
    if h == "as":
        return sort_str(e[2])
    if h in BOOL_OPS:
        return "Bool"
    if h in INT_OPS:
        return "Int"
    if h in REAL_OPS:
        return "Real"
    if h in STRING_OPS:
        return "String"
    if h.startswith("re.") or h == "str.to_re":
        return "RegLan"
    if h in env:  # a skolem's symbol, applied
        return env[h]
    if h in ARITH_OPS:
        return join([sort_of(x, env) for x in e[1:]])
    if h == "ite":
        return join([sort_of(e[2], env), sort_of(e[3], env)])
    if h == "select":
        t = sort_of(e[1], env)
        parts = fuzz.parse_sexpr(t) if t and t.startswith("(Array") else None
        return sort_str(parts[2]) if parts else None
    if h == "store":
        return sort_of(e[1], env)
    if h.startswith("bv") or h == "concat":
        if h == "concat":
            ws = [bv_width(sort_of(x, env)) for x in e[1:]]
            return f"(_ BitVec {sum(ws)})" if all(ws) else None
        if h == "bvcomp":
            return "(_ BitVec 1)"
        return sort_of(e[1], env)
    if h in ("set.union", "set.inter", "set.minus"):
        return sort_of(e[1], env)
    if h == "set.insert":
        return sort_of(e[-1], env)
    if h == "set.singleton":
        t = sort_of(e[1], env)
        return f"(Set {t})" if t else None
    if h == "set.choose":
        t = sort_of(e[1], env)
        parts = fuzz.parse_sexpr(t) if t and t.startswith("(Set") else None
        return sort_str(parts[1]) if parts else None
    if h == "f":
        return "U"
    if h == "pair":
        ts = [sort_of(x, env) for x in e[1:]]
        return f"(Pair {' '.join(ts)})" if all(ts) else None
    if h in ("first", "second", "phd", "ptl", "pcons"):
        t = sort_of(e[1] if h != "pcons" else e[2], env)
        parts = fuzz.parse_sexpr(t) if t and t.startswith("(") else None
        if not parts:
            return None
        if h in ("ptl", "pcons"):
            return t
        return sort_str(parts[1] if h in ("first", "phd") else parts[2])
    if h == "tuple":
        ts = [sort_of(x, env) for x in e[1:]]
        return f"(Tuple {' '.join(ts)})" if all(ts) else None
    if h == "@purify":
        return sort_of(e[1], env)
    if h == "@array_deq_diff":
        t = sort_of(e[1], env)
        parts = fuzz.parse_sexpr(t) if t and t.startswith("(Array") else None
        return sort_str(parts[1]) if parts else None
    if h == "@sets_deq_diff":
        t = sort_of(e[1], env)
        parts = fuzz.parse_sexpr(t) if t and t.startswith("(Set") else None
        return sort_str(parts[1]) if parts else None
    if h == "@quantifiers_skolemize" and len(e) == 3 and isinstance(e[1], list) and e[1][0] in ("forall", "exists"):
        v = e[1][1][int(e[2])] if int(e[2]) < len(e[1][1]) else None
        return sort_str(v[1]) if v else None
    return DT_SORTS.get(h)


def is_skolem_head(h):
    """A skolem as cvc5 prints it with `--print-skolem-definitions`: an `@`
    symbol (not a bound variable `@var.…`, nor cvc5's `@`-prefixed internal
    operators of SMT-LIB terms)."""
    return isinstance(h, str) and h.startswith("@") and not h.startswith("@var")


def free_bound(e, env):
    """The variables of `env` (bound above) that occur in `e`, in order."""
    out = []

    def go(e):
        if isinstance(e, str):
            if e in env and e not in out:
                out.append(e)
        else:
            for x in e:
                go(x)
    go(e)
    return out


class Abstraction:
    """Skolems replaced by fresh symbols: `sk_<id>_<n>`, one per distinct skolem
    term, applied to the bound variables it contains (if any)."""

    def __init__(self):
        self.names = {}     # (skolem term, bound vars) -> name
        self.decls = []     # their declarations
        self.sorts = {}     # name -> sort (of its result)
        self.ids = collections.Counter()

    def abstract(self, e, env=None):
        """`e` with its skolems abstracted, or None if the sort of one is not known."""
        env = env or {}
        if isinstance(e, str):
            if is_skolem_head(e):  # a skolem without arguments
                return self.symbol(e, [e], env)
            return e
        if not e:
            return e
        if is_skolem_head(e[0]):
            return self.symbol(e[0], e, env)
        if e[0] in ("forall", "exists", "lambda") and len(e) == 3 and isinstance(e[1], list):
            env2 = dict(env)
            for v in e[1]:
                env2[v[0]] = sort_str(v[1])
            body = self.abstract(e[2], env2)
            return None if body is None else [e[0], e[1], body]
        out = []
        for x in e:
            y = self.abstract(x, env)
            if y is None:
                return None
            out.append(y)
        return out

    def symbol(self, head, e, env):
        t = sort_of(e, env)
        if t is None:
            self.ids[f"{head} (unknown sort)"] += 1
            return None
        vs = free_bound(e, env)
        key = (print_sexpr(e), tuple(vs))
        if key not in self.names:
            name = f"sk_{head[1:]}_{len(self.names) + 1}"
            self.names[key] = name
            self.decls.append(f"(declare-fun {name} ({' '.join(env[v] for v in vs)}) {t})")
            self.sorts[name] = t
        self.ids[head] += 1
        name = self.names[key]
        return [name, *vs] if vs else name


def to_real(e):
    if isinstance(e, str) and e.lstrip("-").isdigit():
        return ["-", e[1:] + ".0"] if e.startswith("-") else e + ".0"
    if isinstance(e, list) and len(e) == 2 and e[0] == "-" and isinstance(e[1], str) and e[1].isdigit():
        return ["-", e[1] + ".0"]
    return ["to_real", e]


def with_casts(e, sorts, env=None):
    """`e` with the casts that SMT-LIB needs where cvc5 mixes Int and Real
    (`(* (- 1) s)` for a real `s`): in an arithmetic term or a comparison
    with a real argument, the integer arguments are cast to `Real`. `sorts`
    gives the sorts of the skolems' symbols."""
    env = env or {}
    if isinstance(e, str) or not e:
        return e
    if e[0] in ("forall", "exists") and len(e) == 3 and isinstance(e[1], list):
        env2 = dict(env, **{v[0]: sort_str(v[1]) for v in e[1]})
        return [e[0], e[1], with_casts(e[2], sorts, env2)]
    e = [with_casts(x, sorts, env) for x in e]
    h = e[0] if isinstance(e[0], str) else None
    full = dict(sorts, **env)

    def num(x):
        t = sort_of(x, full)
        return t if t in ("Int", "Real") else None
    if h == "ite" and len(e) == 4:
        if {num(x) for x in e[2:]} == {"Int", "Real"}:
            e = e[:2] + [to_real(x) if num(x) == "Int" else x for x in e[2:]]
    elif h in ARITH_OPS or h in COMPARISONS or h in ("/", "/_total"):
        ts = [num(x) for x in e[1:]]
        if "Real" in ts or h in ("/", "/_total"):
            e = [h] + [to_real(x) if t == "Int" else x for x, t in zip(e[1:], ts)]
    return e


# Formulas with these mean nothing outside cvc5: instantiation constants of
# counterexample-guided instantiation, and cvc5's internal names (a tuple's
# constructor).
INTERNAL = re.compile(r"INST_CONSTANT_\d+|__cvc5_")


def inferences(text, abst, skipped):
    """The `(KIND ID φ)` lines of `-t im` output, as (kind, id, φ), with the
    skolems of φ abstracted (`abst`). Formulas that cannot be (`skipped`, by
    reason) are left out."""
    out = []
    for line in text.splitlines():
        line = line.strip()
        for kind in INFERENCE_KINDS:
            if line.startswith(f"({kind} ") and line.endswith(")"):
                rest = line[len(kind) + 2:-1]
                ident, _, phi = rest.partition(" ")
                if not phi or phi.count("(") != phi.count(")"):
                    continue
                if INTERNAL.search(phi):
                    skipped["cvc5-internal symbols"] += 1
                    continue
                e = abst.abstract(fuzz.read_term(phi))
                if e is None:
                    skipped["a skolem of unknown sort"] += 1
                    continue
                out.append((kind, ident, print_sexpr(with_casts(e, abst.sorts))))
    return out


def run(cmd, script, timeout=60, strict=True):
    """Run `cmd` on `script`; its output lines, or None if it fails (with
    `strict`, if it reports an error)."""
    with tempfile.NamedTemporaryFile("w", suffix=".smt2", delete=False) as f:
        f.write(script)
    try:
        r = subprocess.run(cmd + [f.name], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None
    finally:
        os.unlink(f.name)
    if strict and (r.returncode != 0 or "(error" in r.stdout):
        return None
    return [line for line in r.stdout.splitlines() if line.strip()]


def readable(cmd, prelude, phis, lenient=False):
    """The formulas of `phis` that `cmd` rewrites without an error, with its
    rewrites, and the others, with the errors. Tried in one batch, then (unless
    `lenient`: `cmd` answers every query, an error included) one by one."""
    batch = run(cmd, prelude + "".join(f"(simplify {p})\n" for p in phis), strict=not lenient)
    if batch is not None and len(batch) == len(phis):
        ok = [(p, o) for p, o in zip(phis, batch) if not o.startswith("(error")]
        bad = [(p, o) for p, o in zip(phis, batch) if o.startswith("(error")]
        return ok, bad
    ok, bad = [], []
    for p in phis:
        r = run(cmd, prelude + f"(simplify {p})\n")
        (ok if r is not None and len(r) == 1 else bad).append((p, r[0] if r else "error"))
    return ok, bad


def why(err):
    """Why a formula cannot be read: the error, without the term."""
    return re.sub(r":.*", "", err or "error")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cvc5", default=os.environ.get("CVC5") or shutil.which("cvc5") or "cvc5")
    ap.add_argument("--solver", help="the cvc5 that solves the benchmarks, built with tracing "
                    "(default: --cvc5, the reference rewriter)")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=100, help="random benchmarks")
    ap.add_argument("--depth", type=int, default=2)
    ap.add_argument("--size", type=int, default=4, help="most literals in a benchmark")
    ap.add_argument("--show", type=int, default=10, help="mismatches to print")
    ap.add_argument("--max", type=int, default=2000, help="most formulas compared (a random sample)")
    ap.add_argument("--per", type=int, default=200, help="most inferences kept from one benchmark")
    ap.add_argument("--save", help="directory to write the formulas to, for fuzz-pp.py")
    for m in MODES:
        ap.add_argument(f"--{m}", action="store_true")
    a = ap.parse_args()
    if not TELOS.exists() or not fuzz.FUZZ.exists():
        sys.exit("error: build first: lake build telos telos-fuzz")
    mode = next((m for m in MODES if getattr(a, m)), None)

    # 1. theory literals, from random terms
    rng = random.Random(a.seed)
    out = subprocess.run([str(fuzz.FUZZ), str(a.seed), str(4 * a.count), str(a.depth)] + ([mode] if mode else []),
                         capture_output=True, text=True, check=True).stdout.splitlines()
    pool = []
    for line in out:
        found = []
        atoms(fuzz.parse_sexpr(line.split("\t")[0]), found)
        pool.extend(print_sexpr(x) for x in found)
    pool = sorted(set(pool))
    if not pool:
        sys.exit("error: no theory literals in the random terms")

    # 2. cvc5's inferences on conjunctions of them
    ids, skipped = collections.Counter(), collections.Counter()
    phis, answers = {}, collections.Counter()
    abst = Abstraction()
    cvc5_solve = [a.solver or a.cvc5, *SOLVER_OPTS]
    for _ in range(a.count):
        lits = [x if rng.random() < 0.5 else f"(not {x})" for x in rng.sample(pool, min(len(pool), rng.randint(2, a.size)))]
        script = fuzz.PRELUDE + "".join(f"(assert {x})\n" for x in lits) + "(check-sat)\n"
        try:
            r = subprocess.run(cvc5_solve, input=script, capture_output=True, text=True, timeout=30)
            text = r.stdout + r.stderr
        except subprocess.TimeoutExpired as e:
            text = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        verdict = next((line for line in text.splitlines() if line in ("sat", "unsat", "unknown")), "timeout")
        if verdict == "timeout" and "(error" in text:
            sys.exit(f"error: cvc5 failed: {text.strip().splitlines()[-1]}")
        answers[verdict] += 1
        text = "\n".join(line for line in text.splitlines() if len(line) <= MAX_LINE)
        for kind, ident, phi in inferences(text, abst, skipped)[:a.per]:
            ids[f"{kind} {ident}"] += 1
            phis.setdefault(phi, f"{kind} {ident}")
    print(f"{a.count} benchmarks ({', '.join(f'{n} {v}' for v, n in answers.most_common())}), "
          f"{sum(ids.values())} inferences, {len(phis)} distinct formulas")
    print("inferences: " + ", ".join(f"{k} {n}" for k, n in ids.most_common()))
    print(f"skolems abstracted ({len(abst.decls)} symbols): " + ", ".join(f"{k} {n}" for k, n in abst.ids.most_common()))
    if skipped:
        print("skipped: " + ", ".join(f"{n} with {k}" for k, n in skipped.most_common()))
    prelude = fuzz.PRELUDE + "".join(d + "\n" for d in abst.decls)
    if not phis:
        sys.exit("error: no inferences; is cvc5 built with tracing (`cvc5 --show-config`)?")

    # 3. the rewriter on them
    formulas = sorted(phis)
    if len(formulas) > a.max:
        formulas = sorted(rng.sample(formulas, a.max))
        print(f"comparing a sample of {a.max}")
    ours, telos_bad = readable([str(TELOS)], prelude, formulas, lenient=True)
    cvc5_simplify = [a.cvc5, "--lang", "smt2"]
    _, cvc5_bad = readable(cvc5_simplify, prelude, [p for p, _ in ours])
    cvc5_bad_set = {p for p, _ in cvc5_bad}
    cases = [(p, o) for p, o in ours if p not in cvc5_bad_set]
    for what, bad in (("telos", telos_bad), ("cvc5", cvc5_bad)):
        if bad:
            groups = collections.defaultdict(list)
            for p, err in bad:
                groups[why(err)].append(p)
            print(f"{len(bad)} formulas {what} cannot read:")
            for reason, ps in sorted(groups.items(), key=lambda kv: -len(kv[1])):
                srcs = collections.Counter(phis[p] for p in ps)
                print(f"  {len(ps)}: {reason} (from {', '.join(f'{k} {n}' for k, n in srcs.most_common(4))})")
                if a.show:
                    print(f"      e.g. {min(ps, key=len)[:300]}")
    if a.save:
        d = Path(a.save)
        d.mkdir(parents=True, exist_ok=True)
        for i, (p, _) in enumerate(cases):
            (d / f"lemma{i}.smt2").write_text(f"; {phis[p]}\n{prelude}(assert {p})\n(check-sat)\n")
        print(f"wrote {len(cases)} benchmarks to {d}")
    sys.exit(1 if fuzz.compare_rewrites(a.cvc5, cases, a.show, prelude=prelude) else 0)


if __name__ == "__main__":
    main()
