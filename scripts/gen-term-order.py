#!/usr/bin/env python3
"""Generate the per-constructor part of verification/TelosProofs/Core/TermOrder.lean.

The proof that Logos's term order `termCmp` is lawful has one case per
constructor of the mutual block `Term`, `DatatypeDecl`, `Datatype`,
`DatatypeCons` (Logos's `Cpc/LogosTerm.lean`). This script writes those cases
between the `BEGIN GENERATED` and `END GENERATED` markers of TermOrder.lean.
The constructor table `TYPES` below must match Logos's block; when Logos adds
or changes a constructor, update it and regenerate.

Usage:
  scripts/gen-term-order.py           regenerate the block
  scripts/gen-term-order.py --check   exit 1 if it is out of date
"""
import sys
from pathlib import Path

TARGET = Path(__file__).resolve().parent.parent / "verification" / "TelosProofs" / "Core" / "TermOrder.lean"
BEGIN = "-- BEGIN GENERATED (scripts/gen-term-order.py)\n"
END = "-- END GENERATED\n"

# Field kinds: (cmp, lawful-or-None, Lean type)
LEAF = {
    'UserOp': ('userOpCmp', 'userOpCmp_lawful', 'UserOp'),
    'UserOp1': ('userOp1Cmp', 'userOp1Cmp_lawful', 'UserOp1'),
    'UserOp2': ('userOp2Cmp', 'userOp2Cmp_lawful', 'UserOp2'),
    'UserOp3': ('userOp3Cmp', 'userOp3Cmp_lawful', 'UserOp3'),
    'Bool': ('boolCmp', 'boolCmp_lawful', 'Bool'),
    'Int': ('intCmp', 'intCmp_lawful', 'Int'),
    'Rat': ('ratCmp', 'ratCmp_lawful', 'Rat'),
    'String': ('stringCmp', 'stringCmp_lawful', 'List Nat'),
    'Nat': ('natCmp', 'natCmp_lawful', 'Nat'),
}
REC = {  # mutual types: cmp name, theorem prefix
    'Term': 'termCmp',
    'DatatypeDecl': 'datatypeDeclCmp',
    'Datatype': 'datatypeCmp',
    'DatatypeCons': 'datatypeConsCmp',
}
TYPES = {
    'Term': [
        ('UOp', ['UserOp']), ('UOp1', ['UserOp1', 'Term']),
        ('UOp2', ['UserOp2', 'Term', 'Term']), ('UOp3', ['UserOp3', 'Term', 'Term', 'Term']),
        ('__eo_List', []), ('__eo_List_nil', []), ('__eo_List_cons', []), ('Bool', []),
        ('Boolean', ['Bool']), ('Numeral', ['Int']), ('Rational', ['Rat']), ('String', ['String']),
        ('Binary', ['Int', 'Int']), ('Type', []), ('Stuck', []), ('Apply', ['Term', 'Term']),
        ('FunType', []), ('Var', ['Term', 'Term']), ('DatatypeType', ['String', 'DatatypeDecl']),
        ('DatatypeTypeRef', ['String']), ('DtcAppType', ['Term', 'Term']),
        ('DtCons', ['String', 'DatatypeDecl', 'Nat']),
        ('DtSel', ['String', 'DatatypeDecl', 'Nat', 'Nat']), ('USort', ['Nat']),
        ('UConst', ['Nat', 'Term']),
    ],
    'DatatypeDecl': [('nil', []), ('cons', ['String', 'Datatype', 'DatatypeDecl'])],
    'Datatype': [('null', []), ('sum', ['DatatypeCons', 'Datatype'])],
    'DatatypeCons': [('unit', []), ('cons', ['Term', 'DatatypeCons'])],
}


def cmp(k):
    return LEAF[k][0] if k in LEAF else REC[k]


def ltype(k):
    return LEAF[k][2] if k in LEAF else k


def eq_lemma(k, x, y):
    return f'{LEAF[k][1]}.eq_iff {x} {y}' if k in LEAF else f'{REC[k]}_eq_iff {x} {y}'


def eq_global(k):
    return f'{LEAF[k][1]}.eq_iff' if k in LEAF else f'{REC[k]}_eq_iff'


def swap_lemma(k, x, y):
    return f'{LEAF[k][1]}.swap {x} {y}' if k in LEAF else f'{REC[k]}_swap {x} {y}'


def trans_lemma(k, x, y, z):
    return f'{LEAF[k][1]}.trans {x} {y} {z}' if k in LEAF else f'{REC[k]}_trans {x} {y} {z}'


def lname(T, c):
    return f'{REC[T]}_{c.strip("_")}'


def app(T, c, vs):
    return f'(.{c} {" ".join(vs)})' if vs else f'.{c}'


def then_expr(fs, xs, ys):
    terms = [f'{cmp(k)} {x} {y}' for k, x, y in zip(fs, xs, ys)]
    if not terms:
        return '.eq'
    e = terms[-1]
    for t in reversed(terms[:-1]):
        e = f'({t}).then ({e})'
    return e


out = []
w = out.append

# Then-form equations.
for T, ctors in TYPES.items():
    for c, fs in ctors:
        xs = [f'x{i+1}' for i in range(len(fs))]
        ys = [f'y{i+1}' for i in range(len(fs))]
        binders = ' '.join(f'({x} {y} : {ltype(k)})' for k, x, y in zip(fs, xs, ys))
        w(f'theorem {lname(T, c)} {binders} :')
        w(f'    {REC[T]} {app(T, c, xs)} {app(T, c, ys)} = {then_expr(fs, xs, ys)} := by')
        w(f'  rw [{REC[T]}] <;> (repeat\' split) <;> simp_all [Ordering.then, natCmp, {T}.ctorIdx]')
        w('')

# eq_iff.
w('mutual')
for T, ctors in TYPES.items():
    f = REC[T]
    w(f'theorem {f}_eq_iff : ∀ a b : {T}, {f} a b = .eq ↔ a = b')
    for c, fs in ctors:
        xs = [f'x{i+1}' for i in range(len(fs))]
        ys = [f'y{i+1}' for i in range(len(fs))]
        w(f'  | {app(T, c, xs)}, b => by')
        w(f'    by_cases h : ({app(T, c, xs)} : {T}).ctorIdx = b.ctorIdx')
        w(f'    · cases b <;> simp [{T}.ctorIdx] at h')
        if fs: w(f'      rename_i {" ".join(ys)}')
        if fs:
            lemmas = ', '.join([eq_lemma(k, x, y) for k, x, y in zip(fs, xs, ys)] + [f'{T}.{c}.injEq'])
            w(f'      rw [{lname(T, c)}]; simp only [then_eq_iff, {lemmas}]')
        else:
            w(f'      simp [{lname(T, c)}]')
        w(f'    · rw [{f}_ne _ _ h]; constructor')
        w(f'      · intro e; exact absurd ((natCmp_eq_iff _ _).1 e) h')
        w(f'      · intro e; subst e; exact absurd rfl h')
    w('termination_by structural a => a')
    w('')
w('end')
w('')

# swap.
w('mutual')
for T, ctors in TYPES.items():
    f = REC[T]
    w(f'theorem {f}_swap : ∀ a b : {T}, {f} b a = ({f} a b).swap')
    for c, fs in ctors:
        xs = [f'x{i+1}' for i in range(len(fs))]
        ys = [f'y{i+1}' for i in range(len(fs))]
        w(f'  | {app(T, c, xs)}, b => by')
        w(f'    by_cases h : ({app(T, c, xs)} : {T}).ctorIdx = b.ctorIdx')
        w(f'    · cases b <;> simp [{T}.ctorIdx] at h')
        if fs: w(f'      rename_i {" ".join(ys)}')
        if fs:
            lemmas = ', '.join(swap_lemma(k, x, y) for k, x, y in zip(fs, xs, ys))
            w(f'      rw [{lname(T, c)}, {lname(T, c)}]; simp only [then_swap, {lemmas}]')
        else:
            w(f'      rw [{lname(T, c)}]; rfl')
        w(f'    · rw [{f}_ne _ _ h, {f}_ne _ _ (Ne.symm h), natCmp_swap]')
    w('termination_by structural a => a')
    w('')
w('end')
w('')

# trans.
w('mutual')
for T, ctors in TYPES.items():
    f = REC[T]
    w(f'theorem {f}_trans : ∀ a b c : {T}, {f} a b = .lt → {f} b c = .lt → {f} a c = .lt')
    for c, fs in ctors:
        xs = [f'x{i+1}' for i in range(len(fs))]
        ys = [f'y{i+1}' for i in range(len(fs))]
        zs = [f'z{i+1}' for i in range(len(fs))]
        w(f'  | {app(T, c, xs)}, b, c => by')
        w(f'    apply {f}_trans_of')
        w(f'    intro hab hbc')
        w(f'    cases b <;> simp [{T}.ctorIdx] at hab')
        w(f'    rename_i {" ".join(ys)}' if fs else '    skip')
        w(f'    cases c <;> simp [{T}.ctorIdx] at hbc')
        w(f'    rename_i {" ".join(zs)}' if fs else '    skip')
        if not fs:
            w(f'    simp [{lname(T, c)}]')
        else:
            w(f'    rw [{lname(T, c)}, {lname(T, c)}, {lname(T, c)}]')
            for i, k in enumerate(fs):
                if i == len(fs) - 1:
                    w(f'    exact {trans_lemma(k, xs[i], ys[i], zs[i])}')
                else:
                    w(f'    apply then_trans_g {eq_global(k)} ({trans_lemma(k, xs[i], ys[i], zs[i])})')
                    w('    rintro rfl rfl')
    w('termination_by structural a => a')
    w('')
w('end')

generated = '\n'.join(out) + '\n'
text = TARGET.read_text()
head, rest = text.split(BEGIN, 1)
_, tail = rest.split(END, 1)
new = head + BEGIN + "\n" + generated + "\n" + END + tail
if "--check" in sys.argv[1:]:
    if new != text:
        sys.exit(f"error: {TARGET} is out of date; run scripts/gen-term-order.py")
    print("TermOrder.lean is up to date")
else:
    TARGET.write_text(new)
    print(f"wrote {TARGET}")
