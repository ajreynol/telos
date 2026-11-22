#!/usr/bin/env python3
"""Regression checks for source accounting and the runtime dependency audit.

The compiler test runs when the pinned Lean/Logos build is available; the
remaining tests need only Python and also run in the hygiene CI job.
"""

import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from lean_inventory import ROOT, category_of, inline_proof_lines, mask_comments

spec = importlib.util.spec_from_file_location("logos_runtime", ROOT / "scripts/logos-runtime.py")
runtime = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runtime)


class InventoryTests(unittest.TestCase):
    def test_comments_strings_and_positions(self):
        text = 'def s := "-- /- \\" -/" -- comment\n/- outer\n /- nested -/\n-/ def x := 1\n'
        masked = mask_comments(text)
        self.assertEqual(len(masked), len(text))
        self.assertIn('"-- /- \\" -/"', masked)
        self.assertNotIn("comment", masked)
        self.assertNotIn("nested", masked)
        self.assertEqual([i for i, c in enumerate(text) if c == "\n"],
                         [i for i, c in enumerate(masked) if c == "\n"])
        self.assertEqual(sum(bool(line.strip()) for line in masked.splitlines()), 2)

    def test_theorems_in_runtime_files(self):
        text = ('namespace Demo\n'
                'def x := "theorem fake : True := by trivial"\n'
                '@[simp] theorem ok : x = x := by\n'
                '  rfl\n'
                'def next := 1\n'
                'private theorem last : next = 1 := rfl')
        self.assertEqual(inline_proof_lines(text), {2, 3, 5})
        self.assertEqual(inline_proof_lines('theorem t : True := by trivial\nend Demo\n'), {0})
        self.assertEqual(inline_proof_lines('@[simp]\ntheorem t : True := by trivial\n@[inline]\ndef d := 1\n'), {0, 1})

    def test_raw_strings_and_quote_characters(self):
        text = '''def quote := '"' -- comment
def raw := r#"a " /- literal -/ -- literal"# -- comment
/- actual comment -/
'''
        masked = mask_comments(text)
        self.assertNotIn("comment", masked)
        self.assertIn('/- literal -/ -- literal', masked)
        self.assertEqual(sum(bool(line.strip()) for line in masked.splitlines()), 2)

    def test_category_boundaries(self):
        self.assertEqual(category_of("verification/TelosProofs/Core/Spec.lean"), "spec")
        self.assertEqual(category_of("Telos/Core/Profile.lean"), "spec")
        self.assertEqual(category_of("Telos/Solver/Model.lean"), "solver")
        self.assertEqual(category_of("verification/TelosProofs/Solver/Model.lean"), "proofs")
        self.assertEqual(category_of("TelosTests/Bool.lean"), "support")
        self.assertIsNone(category_of("NewUnclassified.lean"))

    def test_transitive_spec_dependency_and_cycle(self):
        def row(module, caller, target, callee):
            return dict(module=module, caller=caller, target_module=target,
                        callee=callee, line=1, form="application")
        rows = [row("Telos.Solver.Example", "solve", "Cpc.Logos", "check"),
                row("Cpc.Logos", "check", "Cpc.Logos", "helper"),
                row("Cpc.Logos", "helper", "Cpc.Logos", "check"),
                row("Cpc.Logos", "helper", "Cpc.SmtTyping", "typeof"),
                row("Telos.Core.Node.ToEo", "translate", "Cpc.SmtTyping", "typeof")]
        data = runtime.analyze(rows, {"Cpc.SmtTyping"}, "solver")
        self.assertEqual(data["logos_sites"], 1)
        self.assertEqual(data["spec_boundary_sites"], 1)
        self.assertEqual(data["spec_boundary"][0]["path"], ["solve", "check", "helper", "typeof"])
        self.assertEqual(runtime.analyze(rows, {"Cpc.SmtTyping"}, "all")["logos_sites"], 2)
        self.assertEqual(runtime.analyze(rows[:3], {"Cpc.SmtTyping"}, "solver")["spec_boundary_sites"], 0)

    @unittest.skipUnless(shutil.which("lake") and
                         (ROOT / ".lake/build/lib/lean/Telos/Core/Node/SmtTypeFast.olean").is_file(),
                         "requires the pinned Lean/Logos build")
    def test_compiler_erases_proofs_and_keeps_function_arguments(self):
        with tempfile.TemporaryDirectory(prefix="telos-inventory-") as tmp:
            root = Path(tmp)
            # A separate Main module avoids shadowing the Telos package root
            # in Lean's search path while exercising an audited module name.
            source = root / "Main.lean"
            source.write_text('''import Telos.Core.Node.SmtTypeFast
namespace Telos.AuditFixture
@[noinline] def direct (t : Eo.Term) := Smtm.__smtx_typeof (__eo_to_smt t)
theorem proofOnly (t : Eo.Term) : Smtm.__smtx_typeof (__eo_to_smt t) = Smtm.__smtx_typeof (__eo_to_smt t) := rfl
@[noinline] def higher (ts : List Smtm.SmtTerm) := ts.map Smtm.__smtx_typeof
@[noinline] def implicitDecision (t : Telos.Node) := decide t.WellTyped
@[noinline] def constructorOnly := Eo.Term.Boolean true
end Telos.AuditFixture
''')
            env = os.environ.copy()
            lean_path = subprocess.check_output(["lake", "env", "printenv", "LEAN_PATH"],
                                                cwd=ROOT, text=True).strip()
            env["LEAN_PATH"] = tmp + os.pathsep + lean_path
            compiled = subprocess.run(["lean", "--root=" + tmp, "-o", str(source.with_suffix(".olean")), str(source)],
                                      cwd=ROOT, env=env, capture_output=True, text=True)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            output = subprocess.check_output(
                ["lean", "--run", "scripts/LogosRuntime.lean", "Main"],
                cwd=ROOT, env=env, text=True)
            rows = [json.loads(line) for line in output.splitlines()]
            own = [r for r in rows if r["module"] == "Main"]
            self.assertTrue(own)
            self.assertFalse(any("proofOnly" in r["caller"] for r in own))
            self.assertFalse(any("constructorOnly" in r["caller"] for r in own))
            self.assertTrue(any(r["callee"] == "__eo_to_smt" for r in own))
            self.assertTrue(any("higher" in r["caller"] and r["callee"] == "Smtm.__smtx_typeof" for r in own))
            self.assertTrue(any("implicitDecision" in r["caller"] for r in own))
            self.assertTrue(all(0 <= r["line"] <= len(source.read_text().splitlines()) for r in own))


if __name__ == "__main__":
    unittest.main()
