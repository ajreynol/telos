# Trusted base

Everything the rewriter's correctness theorem relies on without a proof. Keep this
list current: `scripts/check-hygiene.sh` fails on any `unsafe`, `@[extern]` or
`implemented_by` in a file not named below.

## The specification

These define what the theorem *means*. A mistake here makes the theorem true of
the wrong thing, so review them as specifications, not as code.

- The Logos/CPC definitions: `Cpc.eo` compiled to `Cpc/Logos.lean` by
  `ethos-eoc`, the translation `__eo_to_smt` (`Cpc/SmtTranslate.lean`), the SMT
  type checker `__smtx_typeof` (`Cpc/SmtTyping.lean`) and the model semantics
  (`Cpc/SmtModel.lean`, `Cpc/Spec.lean`). Logos commit pinned in `lakefile.toml`.
- `Telos/Node/ToEo.lean`: the translation of `Node` to Logos terms. It assigns
  every node its meaning, so it must match how cvc5 prints that node in CPC. The
  per-operator part is a table (`Kind.eoShape`, `indexedEoShape`, `nodeEoShape`)
  giving each operator's CPC head symbol and arity. For `+` and `*` it uses the
  signature's own `__eo_nil` and `__eo_typeof` (`Cpc/Logos.lean`) to compute the
  nil terminator from the type, as Eunoia does.
- `verification/TelosProofs/Spec.lean`: the definition of `Node.Equiv`.

## Not trusted

The rewriting logic itself is outside the trusted base: every rewrite is a CPC
step checked by Logos's checker, whose soundness Logos proves
(`Certified.equiv`). A bug in any of the following can make telos miss a
rewrite or differ from cvc5, but not return a non-equivalent node:

- the theory strategies (`Telos/Theory/`) and the driver's control flow;
- the generated rule table (`Telos/Rules/Generated.lean`), its generator
  (`scripts/gen-rules.py`) and the matcher (`Telos/Rules/Match.lean`);
- `Node.ofEo` (`Telos/Node/OfEo.lean`), the term order (`Telos/Node/Order.lean`)
  and the printer (`Telos/Node/Print.lean`).

The theorem is about `Node`s. The following turn text into nodes and nodes into
text, and are not covered by it:

- the SMT-LIB front end (`Telos/Frontend.lean`) and Logos's parser, which is
  unverified. A parsing bug can make telos rewrite a different term than the one
  written; the result is still equivalent to the term telos read.
- proof output (`Telos/Proof/`, `Telos/Rules/RuleNames.lean`). A printed proof is
  checked by Logos's checker before it is printed, and is meant to be checked
  again by its reader (Ethos or Logos).

## Tools

- The Lean 4 kernel, compiler and runtime (`leanprover/lean4:v4.34.0`).

## `unsafe` / `@[extern]` / `implemented_by` in this repository

- `Telos/Profile.lean`: the profiling probe `Profile.time cat key f`, whose
  definition is `f ()`, is `implemented_by` an `unsafe` function that also reads
  the clock and records the time in a global table (`unsafeBaseIO`). The
  theorem is about the definition; the compiled rewriter runs the
  implementation, so this is trusted to return `f ()` on every path, which it
  does in four lines. Probes sit in untrusted code only (the checker call
  `applyCmds`, the driver, the matcher and the arithmetic strategy), never in
  the specification files above.

## Axioms

No `sorry` and no declared `axiom`. `verification/TelosProofs/Axioms.lean` fails
the build if `Telos.rewrite_correct` uses any axiom other than:

- `propext`, `Classical.choice` and `Quot.sound`; and
- the auxiliary axioms created by `native_decide` (43 at present). Each asserts
  that a decision procedure, run as compiled code, returned `true`, so they trust
  the **Lean compiler** in addition to the kernel. They come from Logos's proofs,
  which use `native_decide` throughout (577 uses, including its checker core),
  and enter through Logos's checker soundness proof (every CPC rule) and the
  congruence lemmas reused from `Cpc/Proofs/RuleSupport/Cong/`. Trusting them
  was decided on 2026-11-12.
