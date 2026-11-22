#!/usr/bin/env python3
"""Differential testing of telos's theory engine against cvc5's, by events.

Runs `telos --theory-events` and cvc5 with `-o theory-events` (a cvc5 built
with `cvc5-theory-events.patch`) on benchmarks whose preprocessed assertions
are conjunctions of literals, and compares the two traces of events
(`docs/theory-engine-plan.md`, "Differential testing by events").

cvc5 runs in the configuration telos targets: `--safe-mode=safe
--ee-mode=central --produce-proofs`.

Comparing:
- the trace is cut into rounds at the input events (`prereg`, `assert`, `check`,
  `pop`), which must agree in order;
- the output events between two inputs (`propagate`, `explain`, `conflict`,
  `lemma`, `fact`, ...) are compared as multisets, since cvc5's order inside a
  round comes from hash maps keyed by node ids;
- terms are compared after expanding `let`s, renaming bound variables by
  position (`alpha_free`), renumbering skolems in order of
  first occurrence, writing `(- n)` as `-n`, and orienting equalities;
- the answers must agree;
- the events of the theories outside safe mode (finite fields, floating point,
  separation logic, bags), which cvc5 enables for `ALL` and telos does not
  model, are dropped from cvc5's traces.

The input events alone are also compared, over the whole trace: they are what
the engine's skeleton produces, whatever the theory solvers do.

A benchmark agrees "up to minimized explanations" when, in addition, some of
cvc5's explanations are strict subsets of telos's. With proofs, cvc5 minimizes
an explanation to the assumptions its proof uses (`ProofNodeManager::mkScope`),
and the proof may reuse facts proven before, so it can be shorter than the
equality engine's (which telos's is, and cvc5's is without proofs).

A benchmark agrees "up to explanations" when the only differences are in the
explanations of `explain` and `conflict` events that have the same literals in
another order.

telos reports some inputs as unsupported (`--theory-events` handles only
conjunctions of literals): they are counted and skipped.

The benchmarks are random (default): conjunctions of 2 to 6 literals over an
uninterpreted sort, made to survive preprocessing (few equalities between
variables, which non-clausal simplification solves), or the SMT-LIB files given
as arguments.

With `--ee`, the central equality engine's notifications (`ee-new-class`,
`ee-merge`, `ee-diseq`) are compared too. Benchmarks whose traces are
identical as text, before any normalization, are also counted.

With `--cvc5-pp`, telos is given cvc5's preprocessed assertions
(`-o post-asserts`) with `--no-preprocess`, so that the engines are compared on
the same input: telos's preprocessor orients equalities by its term order,
cvc5's by node id, which changes the events.

With `--proofs`, the CPC refutation of each `unsat` of telos (`--proof-dir`) is
checked by Ethos; its last step states `false`.

With `--replay`, cvc5 runs on the benchmark with `-o post-asserts` too, and
telos replays its trace on its preprocessed form (`telos --replay`): telos's
theories get the inputs that cvc5's got, including the SAT solver's decisions
and backtracking, and their outputs are compared. The random benchmarks then
have disjunctions (also with `--clauses`).

With `--recorded`, cvc5 is not run: each FILE.smt2 is compared with the trace
recorded next to it, FILE.cvc5 (as in `test/solve/`).

Usage:
  scripts/fuzz-solve.py [--cvc5 PATH] [--seed N] [--count N] [--size N] [--show N] [--ee] [--cvc5-pp]
                        [--proofs] [--replay] [--clauses] [--strict]
                        [--recorded] [FILE.smt2 ...]

Build first: `lake build telos`.
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
SIGNATURE = ROOT / ".lake" / "packages" / "Cpc" / "install" / "defs" / "Cpc.cached.eo"
TELOS = ROOT / ".lake" / "build" / "bin" / "telos"
CVC5_OPTS = ["--safe-mode=safe", "--ee-mode=central", "--produce-proofs", "-o", "theory-events"]
INPUTS = {"prereg", "assert", "check", "pop"}
# Theories outside safe mode, which telos does not model; cvc5 enables them for
# `ALL` (their checks do nothing): their events are dropped from cvc5's traces.
UNSAFE = re.compile(r"\bTHEORY_(FF|FP|SEP|BAGS)\b")
ANSWERS = {"sat", "unsat", "unknown"}
OUTPUTS = {"fact", "lemma", "conflict", "propagate", "explain", "phase", "model-unsound", "trigger", "no-trigger",
           "refutation-unsound", "ee-new-class", "ee-merge", "ee-diseq"}
SKOLEM = re.compile(r"@([a-z_]+?)_(\d+)\b")

UF_PRELUDE = """(set-logic QF_UF)
(declare-sort U 0)
(declare-fun u () U)
(declare-fun v () U)
(declare-fun w () U)
(declare-fun f (U) U)
(declare-fun g (U U) U)
(declare-fun P (U) Bool)
(declare-fun h (U U U) U)
(declare-fun Q (U U) Bool)
"""


def uf_term(rng, depth):
    if depth == 0 or rng.random() < 0.3:
        return rng.choice(["u", "v", "w"])
    r = rng.random()
    if r < 0.6:
        return f"(f {uf_term(rng, depth - 1)})"
    if r < 0.9:
        return f"(g {uf_term(rng, depth - 1)} {uf_term(rng, depth - 1)})"
    return f"(h {uf_term(rng, depth - 1)} {uf_term(rng, depth - 1)} {uf_term(rng, depth - 1)})"


def uf_app(rng, depth):
    """A term that is not a variable."""
    t = uf_term(rng, depth)
    return t if t.startswith("(") else f"(f {t})"


def uf_literal(rng):
    r = rng.random()
    if r < 0.2:
        atom = f"(P {uf_term(rng, 2)})"
    elif r < 0.3:
        atom = f"(Q {uf_term(rng, 2)} {uf_term(rng, 2)})"
    elif r < 0.55:
        # an equality between applications, which preprocessing does not solve
        atom = f"(= {uf_app(rng, 2)} {uf_app(rng, 2)})"
    elif r < 0.75:
        # a cyclic equality: the variable occurs in the other side
        x = rng.choice(["u", "v", "w"])
        t = x
        for _ in range(rng.randint(1, 3)):
            t = f"(f {t})"
        atom = f"(= {x} {t})"
    else:
        atom = f"(= {uf_term(rng, 2)} {uf_term(rng, 2)})"
        return f"(not {atom})"
    return atom if rng.random() < 0.6 else f"(not {atom})"


def uf_benchmark(rng, size, clauses=False):
    """A conjunction of literals; with `clauses`, some of the assertions are
    disjunctions of two or three literals, so that the SAT solver decides and
    backtracks."""
    out = []
    for _ in range(rng.randint(2, size)):
        if clauses and rng.random() < 0.6:
            k = rng.randint(2, 3)
            out.append("(or " + " ".join(uf_literal(rng) for _ in range(k)) + ")")
        else:
            out.append(uf_literal(rng))
    return UF_PRELUDE + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


UFQ_PRELUDE = """(set-logic UF)
(declare-sort U 0)
(declare-fun u () U)
(declare-fun v () U)
(declare-fun w () U)
(declare-fun f (U) U)
(declare-fun g (U U) U)
(declare-fun P (U) Bool)
(declare-fun Q (U U) Bool)
"""


def ufq_term(rng, depth, xs):
    """A term over the constants and the bound variables `xs`."""
    leaves = ["u", "v", "w"] + xs + xs
    if depth == 0 or rng.random() < 0.35:
        return rng.choice(leaves)
    if rng.random() < 0.65:
        return f"(f {ufq_term(rng, depth - 1, xs)})"
    return f"(g {ufq_term(rng, depth - 1, xs)} {ufq_term(rng, depth - 1, xs)})"


def ufq_literal(rng, xs):
    r = rng.random()
    if r < 0.35:
        atom = f"(P {ufq_term(rng, 2, xs)})"
    elif r < 0.5:
        atom = f"(Q {ufq_term(rng, 1, xs)} {ufq_term(rng, 1, xs)})"
    else:
        atom = f"(= {ufq_term(rng, 2, xs)} {ufq_term(rng, 2, xs)})"
    return atom if rng.random() < 0.5 else f"(not {atom})"


def ufq_quant(rng):
    """A quantified clause over one or two variables: universal, or (negated)
    existential."""
    xs = ["x"] if rng.random() < 0.6 else ["x", "y"]
    k = rng.randint(1, 3)
    lits = [ufq_literal(rng, xs) for _ in range(k)]
    body = lits[0] if k == 1 else "(or " + " ".join(lits) + ")"
    binds = " ".join(f"({x} U)" for x in xs)
    q = "forall" if rng.random() < 0.8 else "exists"
    if rng.random() < 0.35:
        # an annotation: user patterns (a term of each variable, or one term of
        # all), a term excluded from triggers, a name
        attrs = []
        for _ in range(rng.randint(1, 2)):
            r = rng.random()
            if r < 0.7:
                if len(xs) == 1 or rng.random() < 0.5:
                    t = f"(f {xs[0]})" if len(xs) == 1 else f"(g {xs[0]} {xs[1]})"
                    if rng.random() < 0.5:
                        t = f"(f {ufq_term(rng, 1, xs)})" if len(xs) == 1 else t
                    pats = [t]
                else:
                    pats = [f"(f {xs[0]})", f"(f {xs[1]})"]
                attrs.append(":pattern (" + " ".join(pats) + ")")
            elif r < 0.85:
                attrs.append(f":no-pattern (f {xs[0]})")
            else:
                attrs.append(f":qid q{rng.randint(0, 99)}")
        body = f"(! {body} {' '.join(attrs)})"
    return f"({q} ({binds}) {body})"


def ufq_benchmark(rng, size, clauses=False):
    """Ground literals and quantified clauses (some in disjunctions)."""
    out = []
    for _ in range(rng.randint(2, size)):
        r = rng.random()
        if r < 0.45:
            out.append(ufq_quant(rng))
        elif clauses and r < 0.7:
            out.append("(or " + ufq_literal(rng, []) + " " + ufq_literal(rng, []) + ")")
        else:
            out.append(ufq_literal(rng, []))
    return UFQ_PRELUDE + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


DT_PRELUDE = """(set-logic QF_UFDT)
(declare-sort U 0)
(declare-datatypes ((Lst 0)) (((nil) (cons (head U) (tail Lst)))))
(declare-datatypes ((Tree 0)) (((leaf (val U)) (node (left Tree) (right Tree)))))
(declare-datatypes ((Col 0)) (((red) (green) (blue))))
(declare-datatypes ((Pr 0)) (((pr (fst Col) (snd Lst)))))
(declare-fun a () U)
(declare-fun b () U)
(declare-fun x () Lst)
(declare-fun y () Lst)
(declare-fun z () Lst)
(declare-fun s () Tree)
(declare-fun t () Tree)
(declare-fun c () Col)
(declare-fun d () Col)
(declare-fun p () Pr)
(declare-fun f (Lst) Lst)
"""

DT_SORTS = ["U", "Lst", "Tree", "Col", "Pr"]


def dt_term(rng, sort, depth):
    """A term of sort `sort`."""
    leaf = depth == 0 or rng.random() < 0.35
    if sort == "U":
        if leaf:
            return rng.choice(["a", "b"])
        return rng.choice([f"(head {dt_term(rng, 'Lst', depth - 1)})", f"(val {dt_term(rng, 'Tree', depth - 1)})"])
    if sort == "Lst":
        if leaf:
            return rng.choice(["x", "y", "z", "x", "y", "nil"])
        r = rng.random()
        if r < 0.35:
            return f"(cons {dt_term(rng, 'U', depth - 1)} {dt_term(rng, 'Lst', depth - 1)})"
        if r < 0.7:
            return f"(tail {dt_term(rng, 'Lst', depth - 1)})"
        if r < 0.85:
            return f"(snd {dt_term(rng, 'Pr', depth - 1)})"
        return f"(f {dt_term(rng, 'Lst', depth - 1)})"
    if sort == "Tree":
        if leaf:
            return rng.choice(["s", "t"])
        r = rng.random()
        if r < 0.25:
            return f"(leaf {dt_term(rng, 'U', depth - 1)})"
        if r < 0.45:
            return f"(node {dt_term(rng, 'Tree', depth - 1)} {dt_term(rng, 'Tree', depth - 1)})"
        return f"({rng.choice(['left', 'right'])} {dt_term(rng, 'Tree', depth - 1)})"
    if sort == "Col":
        if leaf:
            return rng.choice(["c", "d", "red", "green", "blue"])
        return f"(fst {dt_term(rng, 'Pr', depth - 1)})"
    # Pr
    if leaf:
        return "p"
    return f"(pr {dt_term(rng, 'Col', depth - 1)} {dt_term(rng, 'Lst', depth - 1)})"


TESTERS = {"Lst": ["nil", "cons"], "Tree": ["leaf", "node"], "Col": ["red", "green", "blue"], "Pr": ["pr"]}


def dt_literal(rng):
    r = rng.random()
    sort = rng.choice(["Lst", "Lst", "Tree", "Col", "U", "Pr"])
    if r < 0.35 and sort in TESTERS:
        atom = f"((_ is {rng.choice(TESTERS[sort])}) {dt_term(rng, sort, 2)})"
    else:
        atom = f"(= {dt_term(rng, sort, 2)} {dt_term(rng, sort, 2)})"
    return atom if rng.random() < 0.65 else f"(not {atom})"


SETS_PRELUDE = """(set-logic QF_UFFS)
(declare-sort E 0)
(declare-fun A () (Set E))
(declare-fun B () (Set E))
(declare-fun C () (Set E))
(declare-fun D () (Set E))
(declare-fun x () E)
(declare-fun y () E)
(declare-fun z () E)
(declare-fun f (E) E)
"""


def sets_elem(rng, depth):
    if depth == 0 or rng.random() < 0.8:
        return rng.choice(["x", "y", "z"])
    return f"(f {sets_elem(rng, depth - 1)})"


def sets_term(rng, depth):
    """A term of sort `(Set E)`."""
    if depth == 0 or rng.random() < 0.4:
        r = rng.random()
        if r < 0.75:
            return rng.choice(["A", "B", "C", "D"])
        if r < 0.92:
            return f"(set.singleton {sets_elem(rng, 1)})"
        return "(as set.empty (Set E))"
    op = rng.choice(["set.union", "set.inter", "set.minus"])
    return f"({op} {sets_term(rng, depth - 1)} {sets_term(rng, depth - 1)})"


def sets_literal(rng):
    r = rng.random()
    if r < 0.45:
        atom = f"(set.member {sets_elem(rng, 1)} {sets_term(rng, 2)})"
    elif r < 0.85:
        atom = f"(= {sets_term(rng, 2)} {sets_term(rng, 2)})"
    else:
        atom = f"(= {sets_elem(rng, 1)} {sets_elem(rng, 1)})"
    return atom if rng.random() < 0.65 else f"(not {atom})"


def sets_benchmark(rng, size, clauses=False):
    out = []
    for _ in range(rng.randint(2, size)):
        if clauses and rng.random() < 0.5:
            k = rng.randint(2, 3)
            out.append("(or " + " ".join(sets_literal(rng) for _ in range(k)) + ")")
        else:
            out.append(sets_literal(rng))
    return SETS_PRELUDE + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


STRINGS_PRELUDE = """(set-logic QF_SLIA)
(declare-fun w () String)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
"""


def strings_term(rng, depth):
    """A term of sort String: a variable, a constant, or a concatenation."""
    if depth == 0 or rng.random() < 0.55:
        if rng.random() < 0.7:
            return rng.choice(["w", "x", "y", "z"])
        return rng.choice(['""', '"a"', '"b"', '"ab"', '"ba"', '"aab"'])
    k = rng.choice([2, 2, 3])
    return "(str.++ " + " ".join(strings_term(rng, depth - 1) for _ in range(k)) + ")"


def strings_literal(rng):
    r = rng.random()
    if r < 0.5:
        atom = f"(= {strings_term(rng, 2)} {strings_term(rng, 2)})"
    elif r < 0.75:
        atom = f"(= (str.len {strings_term(rng, 1)}) {rng.randint(0, 4)})"
    elif r < 0.9:
        atom = f"(= (str.len {strings_term(rng, 1)}) (str.len {strings_term(rng, 1)}))"
    else:
        atom = f"(> (str.len {strings_term(rng, 1)}) (str.len {strings_term(rng, 1)}))"
    return atom if rng.random() < 0.7 else f"(not {atom})"


def strings_benchmark(rng, size, clauses=False):
    out = []
    for _ in range(rng.randint(2, size)):
        if clauses and rng.random() < 0.5:
            k = rng.randint(2, 3)
            out.append("(or " + " ".join(strings_literal(rng) for _ in range(k)) + ")")
        else:
            out.append(strings_literal(rng))
    return STRINGS_PRELUDE + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


# declared in alphabetical order, so that telos's order of variables (by name)
# is cvc5's (by node id, which follows declaration)
LRA_PRELUDE = """(set-logic QF_LRA)
(declare-fun w () Real)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun z () Real)
"""


def lra_sum(rng):
    """A linear sum of one to three variables, with small coefficients."""
    vs = rng.sample(["x", "y", "z", "w"], rng.randint(1, 3))
    terms = []
    for v in vs:
        c = rng.choice([1, 1, 1, 2, -1, 3, -2])
        terms.append(v if c == 1 else f"(* {c} {v})" if c > 0 else f"(* (- {-c}) {v})")
    return terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"


# (`--ite`: some sums are `ite` terms, for term formula removal's skolems)
ITE_TERMS = False


def lra_literal(rng):
    rel = rng.choice(["<=", "<", ">=", ">", "<=", ">=", "="])
    c = rng.randint(-4, 4)
    rhs = str(c) if c >= 0 else f"(- {-c})"
    lhs = lra_sum(rng)
    if ITE_TERMS and rng.random() < 0.3:
        k = rng.randint(-2, 2)
        cond = f"(>= {lra_sum(rng)} {k if k >= 0 else f'(- {-k})'})"
        lhs = f"(ite {cond} {lhs} {lra_sum(rng)})"
    atom = f"({rel} {lhs} {rhs})"
    return atom if rel == "=" or rng.random() < 0.8 else f"(not {atom})"


LIA_PRELUDE = LRA_PRELUDE.replace("QF_LRA", "QF_LIA").replace("Real", "Int")


def lra_benchmark(rng, size, clauses=False, prelude=LRA_PRELUDE):
    out = []
    for _ in range(rng.randint(2, size)):
        if clauses and rng.random() < 0.5:
            k = rng.randint(2, 3)
            out.append("(or " + " ".join(lra_literal(rng) for _ in range(k)) + ")")
        else:
            out.append(lra_literal(rng))
    return prelude + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


UFLRA_PRELUDE = LRA_PRELUDE.replace("QF_LRA", "QF_UFLRA") + """(declare-fun f (Real) Real)
(declare-fun g (Real Real) Real)
"""


def uflra_term(rng):
    """A variable, or an application of `f` or `g` to variables."""
    vs = ["w", "x", "y", "z"]
    r = rng.random()
    if r < 0.25:
        return f"(f {rng.choice(vs)})"
    if r < 0.35:
        return f"(g {rng.choice(vs)} {rng.choice(vs)})"
    return rng.choice(vs)


def uflra_literal(rng):
    """An arithmetic literal over terms with applications, or an equality of
    applications."""
    if rng.random() < 0.25:
        atom = f"(= {uflra_term(rng)} {uflra_term(rng)})"
        return atom if rng.random() < 0.6 else f"(not {atom})"
    ts = [uflra_term(rng) for _ in range(rng.randint(1, 3))]
    terms = []
    for t in ts:
        c = rng.choice([1, 1, 1, 2, -1, 3, -2])
        terms.append(t if c == 1 else f"(* {c} {t})" if c > 0 else f"(* (- {-c}) {t})")
    lhs = terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"
    rel = rng.choice(["<=", "<", ">=", ">", "<=", ">="])
    c = rng.randint(-4, 4)
    atom = f"({rel} {lhs} {c if c >= 0 else f'(- {-c})'})"
    return atom if rng.random() < 0.8 else f"(not {atom})"


def uflra_benchmark(rng, size, clauses=False):
    out = []
    for _ in range(rng.randint(2, size)):
        if clauses and rng.random() < 0.5:
            out.append("(or " + " ".join(uflra_literal(rng) for _ in range(rng.randint(2, 3))) + ")")
        else:
            out.append(uflra_literal(rng))
    return UFLRA_PRELUDE + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


UFLIA_PRELUDE = UFLRA_PRELUDE.replace("QF_UFLRA", "QF_UFLIA").replace("Real", "Int")


def uflia_benchmark(rng, size, clauses=False):
    """The literals of `uflra_benchmark`, over integers."""
    return uflra_benchmark(rng, size, clauses).replace(UFLRA_PRELUDE, UFLIA_PRELUDE)


# datatypes with integer fields, and linear integer arithmetic over them
DTLIA_PRELUDE = """(set-logic QF_DTLIA)
(declare-datatypes ((P 0)) (((mk (fst Int) (snd Int)))))
(declare-datatypes ((IL 0)) (((inil) (icons (ihd Int) (itl IL)))))
(declare-fun l () IL)
(declare-fun m () IL)
(declare-fun p () P)
(declare-fun q () P)
(declare-fun w () Int)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
"""


def dtlia_term(rng, sort, depth):
    leaf = depth == 0 or rng.random() < 0.4
    if sort == "Int":
        if leaf:
            return rng.choice(["w", "x", "y", "z"])
        return rng.choice([f"(fst {dtlia_term(rng, 'P', depth - 1)})", f"(snd {dtlia_term(rng, 'P', depth - 1)})",
                           f"(ihd {dtlia_term(rng, 'IL', depth - 1)})"])
    if sort == "P":
        if leaf:
            return rng.choice(["p", "q"])
        return f"(mk {dtlia_term(rng, 'Int', depth - 1)} {dtlia_term(rng, 'Int', depth - 1)})"
    if leaf:
        return rng.choice(["l", "m", "inil"])
    if rng.random() < 0.6:
        return f"(icons {dtlia_term(rng, 'Int', depth - 1)} {dtlia_term(rng, 'IL', depth - 1)})"
    return f"(itl {dtlia_term(rng, 'IL', depth - 1)})"


def dtlia_literal(rng):
    r = rng.random()
    if r < 0.45:
        ts = [dtlia_term(rng, "Int", 2) for _ in range(rng.randint(1, 2))]
        terms = []
        for t in ts:
            c = rng.choice([1, 1, 2, -1])
            terms.append(t if c == 1 else f"(* {c} {t})" if c > 0 else f"(* (- {-c}) {t})")
        lhs = terms[0] if len(terms) == 1 else "(+ " + " ".join(terms) + ")"
        rel = rng.choice(["<=", "<", ">=", ">", "="])
        c = rng.randint(-3, 3)
        atom = f"({rel} {lhs} {c if c >= 0 else f'(- {-c})'})"
    elif r < 0.55:
        atom = f"((_ is {rng.choice(['inil', 'icons'])}) {dtlia_term(rng, 'IL', 2)})"
    else:
        sort = rng.choice(["P", "IL", "Int"])
        atom = f"(= {dtlia_term(rng, sort, 2)} {dtlia_term(rng, sort, 2)})"
    return atom if rng.random() < 0.7 else f"(not {atom})"


def dtlia_benchmark(rng, size, clauses=False):
    out = []
    for _ in range(rng.randint(2, size)):
        if clauses and rng.random() < 0.5:
            out.append("(or " + " ".join(dtlia_literal(rng) for _ in range(rng.randint(2, 3))) + ")")
        else:
            out.append(dtlia_literal(rng))
    return DTLIA_PRELUDE + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


def lia_benchmark(rng, size, clauses=False):
    """The literals of `lra_benchmark`, over integers."""
    return lra_benchmark(rng, size, clauses, LIA_PRELUDE)


def bool_formula(rng, lit, depth):
    """A formula over literals made by `lit`, with Boolean connectives."""
    if depth == 0 or rng.random() < 0.3:
        return lit(rng)
    r = rng.random()
    sub = lambda: bool_formula(rng, lit, depth - 1)
    if r < 0.3:
        return f"(or {sub()} {sub()}" + (f" {sub()})" if rng.random() < 0.3 else ")")
    if r < 0.5:
        return f"(and {sub()} {sub()})"
    if r < 0.6:
        return f"(not {sub()})"
    if r < 0.7:
        return f"(=> {sub()} {sub()})"
    if r < 0.8:
        return f"(xor {sub()} {sub()})"
    if r < 0.9:
        return f"(= {sub()} {sub()})"
    return f"(ite {sub()} {sub()} {sub()})"


def bool_benchmark(prelude, lit, rng, size):
    out = [bool_formula(rng, lit, rng.randint(1, 3)) for _ in range(rng.randint(2, size))]
    return prelude + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


def dt_benchmark(rng, size, clauses=False):
    out = []
    for _ in range(rng.randint(2, size)):
        if clauses and rng.random() < 0.5:
            k = rng.randint(2, 3)
            out.append("(or " + " ".join(dt_literal(rng) for _ in range(k)) + ")")
        else:
            out.append(dt_literal(rng))
    return DT_PRELUDE + "".join(f"(assert {l})\n" for l in out) + "(check-sat)\n"


def split_cvc5(text):
    """cvc5's output with `-o post-asserts -o theory-events`: the preprocessed
    benchmark, and the event lines (the answer dropped)."""
    if ";; post-asserts start" not in text:
        return None, None
    before, rest = text.split(";; post-asserts start\n", 1)
    pp, after = rest.split(";; post-asserts end", 1)
    events = [l for l in (before + after).splitlines()
              if l.startswith("(") and l[1:].split(" ", 1)[0] in INPUTS | OUTPUTS]
    return pp, events


def num_atom(e):
    """The numeral `n` or `(- n)`, as an integer, or None."""
    if isinstance(e, str):
        return int(e) if e.isdigit() else None
    if len(e) == 2 and e[0] == "-" and isinstance(e[1], str) and e[1].isdigit():
        return -int(e[1])
    return None


def neg_free(e):
    """`e` with its constants written as telos prints them: cvc5's `(- n)` as
    `-n`, its rational `(/ a b)` as `a/b`; and telos's rationals with an integral
    value, `n/1`, as `n` (cvc5 prints the integral reals as integers)."""
    if isinstance(e, str):
        if e.endswith("/1") and e[:-2].lstrip("-").isdigit():
            return e[:-2]
        return e
    n = num_atom(e)
    if n is not None:
        return str(n)
    if len(e) == 3 and e[0] == "/" and num_atom(e[1]) is not None and num_atom(e[2]) not in (None, 0):
        from fractions import Fraction
        q = Fraction(num_atom(e[1]), num_atom(e[2]))
        return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"
    return [neg_free(x) for x in e]


def norm_term(e):
    return fuzz.orient_free(fuzz.alpha_free(neg_free(fuzz.let_free(e))))


def print_sexpr(e):
    return e if isinstance(e, str) else "(" + " ".join(print_sexpr(x) for x in e) + ")"


def parse_events(text):
    """The events of a trace (as parsed s-expressions, skolems renumbered), and
    the answer."""
    names = {}

    def renumber(line):
        for m in SKOLEM.finditer(line):
            names.setdefault(m.group(0), f"@{m.group(1)}_#{len(names) + 1}")
        return SKOLEM.sub(lambda m: names[m.group(0)], line)

    events, answer = [], None
    for line in text.splitlines():
        line = line.strip()
        if UNSAFE.search(line):
            continue
        if line in ANSWERS:
            answer = line
        elif line.startswith("(") and line[1:].split(" ", 1)[0] in INPUTS | OUTPUTS:
            e = fuzz.parse_sexpr(renumber(line))
            if e[0] == "trigger" and len(e) >= 3 and isinstance(e[1], list) and isinstance(e[2], list):
                # a trigger's terms are over its formula's variables: renamed by
                # their position in the binder (cvc5 may name them internally)
                q = fuzz.let_free(e[1])
                if len(q) == 3 and q[0] in ("forall", "exists"):
                    names = {d[0]: f"@tv_{i}" for i, d in enumerate(q[1]) if isinstance(d, list)}
                    def ren(t):
                        return names.get(t, t) if isinstance(t, str) else [ren(c) for c in t]
                    e = [e[0], e[1], ren(fuzz.let_free(e[2]))] + e[3:]
            # terms are the arguments after the kind, level, theory and id
            events.append(tuple(norm_term(x) if isinstance(x, list) else x for x in e))
    return events, answer


def key(e):
    return repr(e)


def rounds(events):
    """The trace as a list of (input event or None, multiset of outputs that follow)."""
    out = [(None, collections.Counter())]
    for e in events:
        # a lemma's atoms are preregistered as it is sent, between the outputs of
        # a check, which a replay cannot reproduce: a `prereg` does not end a round
        # (the inputs, preregistrations included, are compared in order apart)
        if e[0] == "prereg" and len(out) > 1:
            out[-1][1][key(e)] += 1
        elif e[0] in INPUTS:
            out.append((e, collections.Counter()))
        else:
            out[-1][1][key(e)] += 1
    return out


def loose(counter):
    """The multiset with the explanations of `explain` and `conflict` events
    as sets of literals."""
    out = collections.Counter()
    for k, n in counter.items():
        e = eval(k)  # the repr of a tuple of strings and lists
        if e[0] in ("explain", "conflict"):
            t = e[-1]
            lits = sorted(repr(x) for x in t[1:]) if isinstance(t, list) and t and t[0] == "and" else [repr(t)]
            e = e[:-1] + (tuple(lits),)
        out[repr(e)] += n
    return out


def explanation_lits(t):
    return {repr(x) for x in t[1:]} if isinstance(t, list) and t and t[0] == "and" else {repr(t)}


def minimized(oo, to):
    """The outputs differ only in explanations, each of cvc5's a subset of
    telos's: cvc5 with proofs minimizes an explanation to the assumptions of
    its proof (`ProofNodeManager::mkScope`), which may reuse proofs it stored
    before, so some are shorter than the equality engine's."""
    def strip(c):
        out = collections.Counter()
        for k, n in c.items():
            e = eval(k)
            out[repr(e[:-1] if e[0] in ("explain", "conflict") else e)] += n
        return out
    if strip(oo) != strip(to):
        return False
    ex_o = sorted((eval(k) for k in oo if eval(k)[0] in ("explain", "conflict")), key=lambda e: repr(e[:-1]))
    ex_t = sorted((eval(k) for k in to if eval(k)[0] in ("explain", "conflict")), key=lambda e: repr(e[:-1]))
    return len(ex_o) == len(ex_t) and all(explanation_lits(t[-1]) <= explanation_lits(o[-1])
                                          for o, t in zip(ex_o, ex_t))


def compare(ours, theirs):
    """`same`, `explanations` (same up to the order of explained literals), or
    a description of the first difference."""
    (oe, oa), (te, ta) = ours, theirs
    ro, rt = rounds(oe), rounds(te)
    verdict = "same"
    for i in range(max(len(ro), len(rt))):
        if i >= len(ro) or i >= len(rt):
            extra = (rt if i >= len(ro) else ro)[i][0]
            who = "cvc5" if i >= len(ro) else "telos"
            return f"round {i}: only {who} has {print_sexpr(list(extra))}"
        (oi, oo), (ti, to) = ro[i], rt[i]
        if oi != ti:
            return f"round {i}: telos {fmt(oi)}, cvc5 {fmt(ti)}"
        if oo != to:
            if loose(oo) == loose(to):
                verdict = "explanations"
                continue
            if minimized(oo, to):
                verdict = "minimized"
                continue
            only_o = oo - to
            only_t = to - oo
            return (f"round {i} (after {fmt(oi)}): telos only " + "; ".join(fmt(eval(k)) for k in only_o) +
                    " | cvc5 only " + "; ".join(fmt(eval(k)) for k in only_t))
    if oa != ta:
        return f"answer: telos {oa}, cvc5 {ta}"
    return verdict


def fmt(e):
    return "(none)" if e is None else print_sexpr(list(e))


def check_proof(ethos, cmd, path):
    """Run telos with `--proof-dir` and check the refutation with Ethos:
    (`accepted` | `rejected` | `missing`, message)."""
    d = Path(tempfile.mkdtemp())
    try:
        subprocess.run(cmd + ["--proof-dir", str(d), str(path)], capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        return ("missing", "timeout")
    f = d / "proof.eo"
    if not f.exists():
        return ("missing", "no proof")
    text = f.read_text().strip()
    body = d / "body.eo"
    body.write_text(text[1:-1] if text.startswith("(") else text)
    try:
        e = subprocess.run([ethos, f"--include={SIGNATURE}", str(body)], capture_output=True, text=True, timeout=120)
    except subprocess.TimeoutExpired:
        return ("rejected", "ethos timeout")
    if e.returncode == 0 and e.stdout.strip().endswith("correct"):
        return ("accepted", "")
    return ("rejected", (e.stdout + e.stderr).strip()[-300:])


def run(cmd, path, timeout=60):
    try:
        r = subprocess.run(cmd + [str(path)], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return None, "timeout"
    return (r.stdout if r.returncode == 0 else None), r.stderr.strip()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--cvc5", default=os.environ.get("CVC5") or shutil.which("cvc5") or "cvc5")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--count", type=int, default=200, help="random benchmarks")
    ap.add_argument("--show", type=int, default=5, help="differences to print")
    ap.add_argument("--recorded", action="store_true", help="compare with the recorded FILE.cvc5")
    ap.add_argument("--strict", action="store_true", help="exit with 1 on any difference or failure")
    ap.add_argument("--ee", action="store_true",
                    help="also compare the central equality engine's notifications (-o theory-events-ee)")
    ap.add_argument("--cvc5-pp", action="store_true",
                    help="give telos cvc5's preprocessed assertions (-o post-asserts), with --no-preprocess")
    ap.add_argument("--proofs", action="store_true",
                    help="check the CPC refutation of each unsat with Ethos (telos --proof-dir)")
    ap.add_argument("--ethos", default=shutil.which("ethos") or "ethos")
    ap.add_argument("--replay", action="store_true",
                    help="replay cvc5's trace on telos's theories (telos --replay), on cvc5's preprocessed benchmark")
    ap.add_argument("--clauses", action="store_true", help="random benchmarks with disjunctions")
    ap.add_argument("--bool", action="store_true", help="random benchmarks with nested Boolean connectives")
    ap.add_argument("--sat", action="store_true",
                    help="solve with telos's SAT solver (--via-sat), cvc5 with --sat-solver=minisat")
    ap.add_argument("--size", type=int, default=6, help="the most literals of a random benchmark")
    ap.add_argument("--theory", choices=["uf", "dt", "lra", "lia", "uflra", "uflia", "dtlia", "sets", "strings", "ufq"], default="uf", help="the theory of the random benchmarks")
    ap.add_argument("--decision", choices=["internal", "justification", "stoponly"],
                    help="the SAT solver's decision mode, for both (otherwise the logic's)")
    ap.add_argument("--ite", action="store_true", help="arithmetic literals with ite terms")
    ap.add_argument("--triggers", action="store_true",
                    help="compare the triggers made too (cvc5's -o trigger, telos's --trigger)")
    ap.add_argument("--ieval-off", action="store_true",
                    help="cvc5 with --ieval=off (the form of conflict-based instantiation telos ports); "
                         "safe mode allows one non-default option, so cvc5 runs without --safe-mode=safe "
                         "(the traces are otherwise the same)")
    ap.add_argument("files", nargs="*")
    a = ap.parse_args()
    global ITE_TERMS
    ITE_TERMS = a.ite
    if not TELOS.exists():
        sys.exit("error: build telos first: lake build telos")
    files = [Path(f) for f in a.files]
    if not files:
        tmp = Path(tempfile.mkdtemp())
        rng = random.Random(a.seed)
        for i in range(a.count):
            p = tmp / f"s{i}.smt2"
            if a.bool:
                prelude, lit = {"dt": (DT_PRELUDE, dt_literal), "lra": (LRA_PRELUDE, lra_literal),
                                  "lia": (LIA_PRELUDE, lra_literal), "uflra": (UFLRA_PRELUDE, uflra_literal),
                                  "uflia": (UFLIA_PRELUDE, uflra_literal), "dtlia": (DTLIA_PRELUDE, dtlia_literal),
                                  "sets": (SETS_PRELUDE, sets_literal),
                                  "strings": (STRINGS_PRELUDE, strings_literal)}.get(
                    a.theory, (UF_PRELUDE, uf_literal))
                p.write_text(bool_benchmark(prelude, lit, rng, a.size))
            else:
                gen = {"dt": dt_benchmark, "lra": lra_benchmark, "lia": lia_benchmark,
                       "uflra": uflra_benchmark, "uflia": uflia_benchmark,
                       "dtlia": dtlia_benchmark, "sets": sets_benchmark,
                       "strings": strings_benchmark, "ufq": ufq_benchmark}.get(a.theory, uf_benchmark)
                p.write_text(gen(rng, a.size, a.clauses or a.replay))
            files.append(p)
    counts = collections.Counter()
    diffs, failures, proof_failures = [], [], []
    for path in files:
        if a.replay:
            out, cerr = run([a.cvc5, *CVC5_OPTS, "-o", "post-asserts"] + (["-o", "theory-events-ee"] if a.ee else []),
                            path)
            pp, events = split_cvc5(out or "")
            if pp is None:
                failures.append((path, cerr or "no output"))
                continue
            tpath = path.with_suffix(".pp.smt2")
            tpath.write_text(pp)
            trace = path.with_suffix(".trace")
            trace.write_text("\n".join(events) + "\n")
            ours, err = run([str(TELOS), "--replay", str(trace)] + (["--theory-events-ee"] if a.ee else []), tpath)
            if ours is None:
                failures.append((path, err))
                continue
            theirs_lines = [l for l in events if not UNSAFE.search(l)]
            if ours.strip().splitlines() == theirs_lines:
                counts["identical"] += 1
            po, pt = parse_events(ours), parse_events("\n".join(theirs_lines))
            counts["pops"] += sum(1 for e in pt[0] if e[0] == "pop") > 0
            if [e for e in po[0] if e[0] in INPUTS] == [e for e in pt[0] if e[0] in INPUTS]:
                counts["inputs"] += 1
            v = compare(po, pt)
            if v in ("same", "explanations", "minimized"):
                counts[v] += 1
            else:
                counts["different"] += 1
                diffs.append((path, v))
            continue
        tpath = path
        if a.cvc5_pp:
            pp, perr = run([a.cvc5, "--safe-mode=safe", "--ee-mode=central", "--produce-proofs",
                            "-o", "post-asserts", "--preprocess-only"], path)
            body = pp and pp.split(";; post-asserts start\n", 1)[-1].split(";; post-asserts end", 1)[0]
            if not body:
                failures.append((path, perr or "no post-asserts"))
                continue
            tpath = path.with_suffix(".pp.smt2")
            tpath.write_text(body)
        ours, err = run([str(TELOS), "--theory-events"] + (["--theory-events-ee"] if a.ee else []) +
                        (["--trigger"] if a.triggers else []) +
                        (["--no-preprocess"] if a.cvc5_pp else []) + (["--via-sat"] if a.sat else []) +
                        ([f"--decision={a.decision}"] if a.decision else []), tpath)
        if err and "by certificate" in err:
            counts["by-certificate"] += 1
        if ours is None:
            if "unsupported" in err:
                counts["unsupported"] += 1
            else:
                failures.append((path, err))
            continue
        if a.recorded:
            rec = path.with_suffix(".cvc5")
            theirs, cerr = (rec.read_text(), "") if rec.exists() else (None, f"no recorded trace {rec}")
        else:
            # (the decision mode is the logic's, as in telos, unless `--decision`)
            opts = [o for o in CVC5_OPTS if o != "--safe-mode=safe"] + ["--ieval=off"] if a.ieval_off else CVC5_OPTS
            theirs, cerr = run([a.cvc5, *opts] + (["-o", "theory-events-ee"] if a.ee else []) +
                               (["-o", "trigger"] if a.triggers else []) +
                               (["--sat-solver=minisat"] if a.sat else []) +
                               ([f"--decision={a.decision}"] if a.decision else []), path)
        if theirs is None or "(error" in theirs:
            failures.append((path, cerr or theirs))
            continue
        if ours.strip().splitlines() == [l for l in theirs.strip().splitlines() if not UNSAFE.search(l)]:
            counts["identical"] += 1
        po, pt = parse_events(ours), parse_events(theirs)
        counts[pt[1] or "none"] += 1
        if po[1] == "unknown" and pt[1] == "unsat" and err and "not certified yet" in err:
            # the SAT solver's unsat, not certified yet
            counts["unsat-uncertified"] += 1
            po = (po[0], "unsat")
        if a.proofs and po[1] == "unsat":
            verdict = check_proof(a.ethos, [str(TELOS), "--theory-events"] +
                                  (["--no-preprocess"] if a.cvc5_pp else []), tpath)
            counts["proof-" + verdict[0]] += 1
            if verdict[0] != "accepted":
                proof_failures.append((path, verdict[1]))
        if [e for e in po[0] if e[0] in INPUTS] == [e for e in pt[0] if e[0] in INPUTS]:
            counts["inputs"] += 1
        v = compare(po, pt)
        if v in ("same", "explanations", "minimized"):
            counts[v] += 1
        else:
            counts["different"] += 1
            diffs.append((path, v))
    n = len(files)
    print(f"{n} benchmarks: {counts['same']} the same events as cvc5, {counts['explanations']} up to the "
          f"order of explanations, {counts['minimized']} up to cvc5's minimized explanations, "
          f"{counts['different']} different, {counts['unsupported']} unsupported, "
          f"{len(failures)} failed; the input events (prereg, assert, check, pop) agree on {counts['inputs']}; "
          f"{counts['identical']} identical as text" +
          (f"; {counts['by-certificate']} unsat by certificate" if counts['by-certificate'] else "") +
          (f"; {counts['unsat-uncertified']} unsat not certified yet" if counts['unsat-uncertified'] else "") +
          (f"; {counts['pops']} with backtracking" if a.replay else
           f"; cvc5 answered sat {counts['sat']}, unsat {counts['unsat']}"))
    for path, v in diffs[:a.show]:
        print(f"\n  {path}: {v}")
    for path, err in failures[:a.show]:
        print(f"\n  {path}: {(err or 'failed').splitlines()[0]}")
    if a.proofs:
        print(f"proofs: {counts['proof-accepted']} accepted by Ethos, {counts['proof-rejected']} rejected, "
              f"{counts['proof-missing']} missing")
        for path, msg in proof_failures[:a.show]:
            print(f"  {path}: {msg}")
    if a.strict and (diffs or failures or proof_failures):
        sys.exit(1)


if __name__ == "__main__":
    main()
