#!/usr/bin/env python3
"""The test bed: the cvc5 regressions that telos aims to solve, and how many it does.

    scripts/testbed.py compile --cvc5 PATH --regress DIR     # (re)compile the list
    scripts/testbed.py run --regress DIR                     # run telos on it, compare with the record
    scripts/testbed.py run --regress DIR --update            # ... and record the results
    scripts/testbed.py report                                # summarize the record

DIR is cvc5's `test/regress/cli` (default: the one recorded in the list).

**The list** (`test/testbed/list.tsv`) has the benchmarks that

- are SMT-LIB 2 files of cvc5's regress0, regress1 or regress2
  (`CMakeLists.txt`, so without the disabled ones);
- have a single query: exactly one `check-sat`, with no `check-sat-assuming`,
  `push`, `pop`, `reset`, nor another command that is a query (`get-abduct`,
  `get-interpolant`, `get-qe`, SyGuS, …);
- use no bit-vectors or arrays (by the symbols of the input, not by its logic:
  an input in `AUFLIA` that has no arrays is kept);
- run in cvc5's safe mode: are not left out of a safe build by cvc5's
  regression runner (`; REQUIRES: unrestricted-mode`, `no-safe-mode` or
  `stable-mode`), and `cvc5 --safe-mode=safe FILE` gives an answer
  (`sat`, `unsat`, `unknown`) or reaches the timeout, and no error.

The options of the regression (`COMMAND-LINE`) are not used: cvc5 and telos
run with their defaults. Each line has cvc5's answer and time, and the
expected answer (`EXPECT`, or `:status`), `-` if none.

**The record** (`test/testbed/results.tsv`): telos's result on each, a
benchmark being *solved* if telos gives cvc5's answer, or the expected one
where cvc5 gives none (every answer of telos is certified; an expected answer may
depend on the regression's options). The other results are the codes of telos's `unknown`, `timeout`, `crash`, and
`unsupported/…` for rejected inputs; `WRONG` if telos contradicts the answer.
"""

import argparse
import collections
import os
import re
import resource
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TELOS = ROOT / ".lake/build/bin/telos"
BED = ROOT / "test/testbed"
LIST = BED / "list.tsv"
# The features of a `; REQUIRES:` line by which cvc5's regression runner leaves
# a benchmark out of a safe build (`run_regression.py`: safe and stable builds
# are the restricted ones).
NOT_SAFE = {"unrestricted-mode", "no-safe-mode", "stable-mode"}
RECORD = BED / "results.tsv"
MEMORY = 8 << 30

BAD = ("WRONG", "crash", "cert-sat/model-false", "cert-unsat/broken", "cert-unsat/bad-justification", "internal")

# commands that a single-query script may have, besides its one check-sat
COMMANDS = {
    "set-logic", "set-info", "set-option", "declare-sort", "define-sort", "declare-fun", "declare-const",
    "define-fun", "define-const", "define-fun-rec", "define-funs-rec", "declare-datatype", "declare-datatypes",
    "assert", "check-sat", "exit", "echo", "get-model", "get-value", "get-assignment", "get-info", "get-option",
    "get-proof", "get-unsat-core", "get-unsat-assumptions", "get-assertions", "declare-codatatype",
    "declare-codatatypes", "get-difficulty", "get-learned-literals", "get-unsat-core-lemmas",
    "declare-heap", "declare-pool", "simplify", "include", "get-timeout-core", "block-model",
}
TOKEN = re.compile(r';[^\n]*|"(?:[^"]|"")*"|\|[^|]*\||[()]|[^\s()"|;]+')


def tokens(s):
    return [t for t in TOKEN.findall(s) if not t.startswith(";")]


def commands(toks):
    """The names of the top-level commands."""
    out, depth = [], 0
    for i, t in enumerate(toks):
        if t == "(":
            if depth == 0:
                out.append(toks[i + 1] if i + 1 < len(toks) else "")
            depth += 1
        elif t == ")":
            depth -= 1
    return out


def bv_or_array(toks):
    for t in toks:
        if t in ("BitVec", "Array", "select", "store", "bv2nat", "int2bv", "nat2bv", "ubv_to_int", "sbv_to_int",
                 "int_to_bv", "bv2int") or t.startswith(("#x", "#b")) or re.fullmatch(r"bv\d+", t):
            return True
    return False


def expected(s):
    """The answer of the single query that the file states: `EXPECT`, else `:status`."""
    exp = [e for e in re.findall(r"^[;%] *EXPECT: *(\S+)", s, re.M) if e in ("sat", "unsat", "unknown")]
    st = re.findall(r"\(set-info\s+:status\s+(sat|unsat)\s*\)", s)
    if len(exp) == 1 and exp[0] != "unknown":
        return exp[0]
    if not exp and len(st) == 1:
        return st[0]
    return "-"


def limited():
    resource.setrlimit(resource.RLIMIT_AS, (MEMORY, MEMORY))
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def run(cmd, timeout):
    """(status, stdout, stderr, seconds)"""
    t0 = time.monotonic()
    try:
        r = subprocess.run(cmd, capture_output=True, timeout=timeout, preexec_fn=limited)
        return r.returncode, r.stdout.decode(errors="replace"), r.stderr.decode(errors="replace"), time.monotonic() - t0
    except subprocess.TimeoutExpired:
        return None, "", "", timeout


def candidates(base):
    """(tests, why) the single-query inputs of the lists, and the counts of the others."""
    why = collections.Counter()
    out = []
    s = (base / "CMakeLists.txt").read_text()
    for d in (0, 1, 2):
        m = re.search(r"set\(regress_%d_tests(.*?)^\)" % d, s, re.S | re.M)
        for f in re.findall(r"^\s*(regress\S+)", m.group(1), re.M):
            if not f.endswith(".smt2"):
                why["not smt2"] += 1
                continue
            text = (base / f).read_text(errors="replace")
            toks = tokens(text)
            cmds = commands(toks)
            if cmds.count("check-sat") != 1 or any(c not in COMMANDS for c in cmds):
                why["not a single query"] += 1
            elif bv_or_array(toks):
                why["bit-vectors or arrays"] += 1
            elif set(re.findall(r"^; REQUIRES:\s*(\S+)", text, re.M)) & NOT_SAFE:
                why["not in a safe build (REQUIRES)"] += 1
            else:
                out.append((f, expected(text)))
    return out, why


def compile_list(a):
    base = Path(a.regress)
    cands, why = candidates(base)

    def one(c):
        st, out, err, secs = run([a.cvc5, "--safe-mode=safe", str(base / c[0])], a.timeout)
        if st is None:
            return c, "timeout", secs, ""
        # (a get-value with no models, for want of the regression's options, is no matter)
        out = re.sub(r'\(error "cannot get[^\n]*', "", out)
        m = re.search(r'\(error[^\n]*|^cvc5 (?:interrupted|suffered)[^\n]*|Fatal failure[^\n]*', out + "\n" + err, re.M)
        ans = [l.strip() for l in out.splitlines() if l.strip() in ("sat", "unsat", "unknown")]
        if m or st < 0 or not ans:
            return c, "error", secs, (m.group(0) if m else f"exit {st} {(out + err)[:100]!r}")
        return c, ans[0], secs, ""
    with ThreadPoolExecutor(a.jobs) as ex:
        res = list(ex.map(one, cands))
    errs = collections.Counter()
    rows, conflicts = [], []
    for (f, exp), ans, secs, msg in res:
        if ans == "error":
            why["not in safe mode (cvc5 gives an error)"] += 1
            errs[re.sub(r'".*?"|of kind \S+', lambda m: m.group(0) if m.group(0).startswith("of kind") else "…",
                        msg.replace('(error "', ""))[:110]] += 1
            continue
        if ans in ("sat", "unsat") and exp in ("sat", "unsat") and ans != exp:
            conflicts.append((f, exp, ans))
        rows.append((f, exp, ans, f"{secs:.1f}"))
    ver = subprocess.run([a.cvc5, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    BED.mkdir(parents=True, exist_ok=True)
    LIST.write_text(f"# {ver}\n# timeout {a.timeout}\n# regressions {base}\n# file\texpected\tcvc5 (safe mode)\tseconds\n"
                    + "".join("\t".join(r) + "\n" for r in sorted(rows)))
    print(f"{len(rows)} benchmarks; left out:")
    for k, n in why.most_common():
        print(f"  {n:5}  {k}")
    print("errors:")
    for k, n in errs.most_common(a.show):
        print(f"  {n:5}  {k}")
    print("cvc5:", dict(collections.Counter(r[2] for r in rows)))
    for c in conflicts:
        print("  cvc5 does not give the expected answer:", *c)


def read_list():
    head, rows = {}, []
    for l in LIST.read_text().splitlines():
        if l.startswith("# regressions "):
            head["regress"] = l[len("# regressions "):]
        if not l.startswith("#"):
            rows.append(l.split("\t"))
    return head, rows


def classify(f, want, timeout):
    st, out, err, secs = run([str(TELOS), "--solve", f], timeout)
    if st is None:
        return "timeout", secs, ""
    ans = [l.strip() for l in out.splitlines() if l.strip() in ("sat", "unsat", "unknown")]
    lines = [l for l in err.strip().splitlines() if l.strip()]
    msg = (lines or [""])[-1].replace("\t", " ")
    if st < 0 or "Stack overflow" in err or "out of memory" in err.lower():
        return "crash", secs, msg
    if ans and ans[-1] in ("sat", "unsat"):
        if want == "-":
            return "solved", secs, f"{ans[-1]} (no answer to compare with)"
        return ("solved" if ans[-1] == want else "WRONG"), secs, ans[-1]
    if ans:
        m = re.search(r"\[([a-z\-]+(?:/[a-z\-]+)?)\]", msg)
        return (m.group(1) if m else "unknown"), secs, msg
    for k in ("parse", "operator", "command"):
        if k in msg:
            return f"unsupported/{k}", secs, msg
    return "unsupported/other", secs, msg


def do_run(a):
    if not TELOS.exists():
        sys.exit("error: build telos first: lake build telos")
    head, rows = read_list()
    base = Path(a.regress or head["regress"])
    rows = [r for r in rows if not a.filter or re.search(a.filter, r[0])]
    # the answer to give: cvc5's, else the expected one (which may depend on the
    # regression's options)
    want = lambda r: r[2] if r[2] in ("sat", "unsat") else r[1]
    with ThreadPoolExecutor(a.jobs) as ex:
        got = list(ex.map(lambda r: classify(str(base / r[0]), want(r), a.timeout), rows))
    new = {r[0]: g for r, g in zip(rows, got)}
    old = read_record()
    if a.update and not a.filter:
        RECORD.write_text(f"# timeout {a.timeout}\n# file\tresult\tseconds\tmessage\n" + "".join(
            f"{f}\t{g[0]}\t{g[1]:.1f}\t{g[2][:300]}\n" for f, g in sorted(new.items())))
    report(rows, {f: (g[0], g[1], g[2]) for f, g in new.items()}, a.show)
    changed = [(f, old[f][0], new[f][0]) for f in new if f in old and old[f][0] != new[f][0]]
    if old:
        print(f"\nagainst the record: {len(changed)} changed")
        for c in changed:
            print("  %s: %s -> %s" % c)
    if any(n[0] in BAD and (f not in old or old[f][0] != n[0]) for f, n in new.items()):
        sys.exit(1)


def read_record():
    if not RECORD.exists():
        return {}
    out = {}
    for l in RECORD.read_text().splitlines():
        if not l.startswith("#"):
            f, r, s, *m = l.split("\t")
            out[f] = (r, float(s), m[0] if m else "")
    return out


def family(f):
    """The part of cvc5 a regression tests: its directory."""
    p = f.split("/")
    return p[1] if len(p) > 2 else "(top)"


def table(rows, res, key):
    tot, ok, cv = collections.Counter(), collections.Counter(), collections.Counter()
    for r in rows:
        k = key(r)
        tot[k] += 1
        ok[k] += res[r[0]][0] == "solved"
        cv[k] += r[2] in ("sat", "unsat")
    for k, n in sorted(tot.items(), key=lambda x: -x[1]):
        print(f"  {k:22} {ok[k]:5} / {n:<5} {100 * ok[k] / n:5.1f}%   (cvc5 {cv[k]})")


def report(rows, res, show):
    rows = [r for r in rows if r[0] in res]
    n = len(rows)
    ok = sum(res[r[0]][0] == "solved" for r in rows)
    cv = [r for r in rows if r[2] in ("sat", "unsat")]
    okcv = sum(res[r[0]][0] == "solved" for r in cv)
    print(f"solved: {ok} of {n} ({100 * ok / max(n, 1):.1f}%); cvc5 solves {len(cv)}, of which telos {okcv} "
          f"({100 * okcv / max(len(cv), 1):.1f}%)")
    print("by level:")
    table(rows, res, lambda r: r[0].split("/")[0])
    print("by directory:")
    table(rows, res, lambda r: family(r[0]))
    print("by cvc5's answer:")
    table(rows, res, lambda r: r[2])
    print("the others:")
    counts = collections.Counter(res[r[0]][0] for r in rows)
    for k, c in counts.most_common():
        if k != "solved":
            print(f"  {c:5}  {k}{'  !!' if k in BAD else ''}")
            msgs = collections.Counter(re.sub(r"^.*?telos: ", "", res[r[0]][2])[:130] for r in rows if res[r[0]][0] == k)
            for m, i in msgs.most_common(show):
                print(f"            {i:4}  {m}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    c = sub.add_parser("compile")
    c.add_argument("--cvc5", required=True)
    c.add_argument("--regress", required=True)
    r = sub.add_parser("run")
    r.add_argument("--regress")
    r.add_argument("--update", action="store_true", help="record the results")
    r.add_argument("--filter", help="only the files that match this regular expression")
    p = sub.add_parser("report")
    for q in (c, r, p):
        q.add_argument("--show", type=int, default=4, help="messages to print per result")
    for q in (c, r):
        q.add_argument("--timeout", type=int, default=20)
        q.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) // 2))
    a = ap.parse_args()
    if a.cmd == "compile":
        compile_list(a)
    elif a.cmd == "run":
        do_run(a)
    else:
        report(read_list()[1], read_record(), a.show)


if __name__ == "__main__":
    main()
