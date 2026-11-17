#!/usr/bin/env bash
# Fails on proof escape hatches (sorry/admit/axiom) anywhere in the solver, and on
# trusted-code markers (unsafe/@[extern]/implemented_by) that are not listed in
# TRUSTED.md. Textual, so it needs no toolchain. Comments are scanned too.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

mapfile -d '' files < <(find Telos TelosTests verification/TelosProofs Main.lean FuzzMain.lean Telos.lean -name '*.lean' -print0)
status=0

if LC_ALL=C grep -nHE "(^|[^[:alnum:]_'])(sorry|admit|axiom)([^[:alnum:]_']|$)" "${files[@]}"; then
  echo "error: forbidden proof escape hatch (sorry/admit/axiom) found" >&2
  status=1
fi

# Each trusted marker must sit in a file that TRUSTED.md names.
while IFS=: read -r file line _; do
  if ! grep -qF "\`${file}\`" TRUSTED.md; then
    echo "error: ${file}:${line} uses unsafe/@[extern]/implemented_by but is not listed in TRUSTED.md" >&2
    status=1
  fi
done < <(LC_ALL=C grep -nHE "(^|[^[:alnum:]_'])(unsafe|implemented_by)([^[:alnum:]_']|$)|@\[extern" "${files[@]}" || true)

# The specification (TRUSTED.md) builds only on Logos's specification, not on the
# Eunoia programs compiled from Cpc.eo (Cpc.Logos: the rules, the checker,
# __eo_typeof, __eo_nil). Its files import only each other and these modules.
spec_files=(Telos/Node/Kind.lean Telos/Node/TypeNode.lean Telos/Node/Node.lean
  Telos/Node/ToEo.lean verification/TelosProofs/Spec.lean)
spec_imports='^(Telos\.Node\.(Kind|TypeNode|Node|ToEo)|Cpc\.(LogosTerm|SmtEval|SmtSyntax|SmtTyping|SmtTranslate|SmtModel|Spec))$'
while IFS=: read -r file line text; do
  mod=$(sed -E 's/^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+(all[[:space:]]+)?//; s/[[:space:]]+$//' <<<"${text}")
  if ! LC_ALL=C grep -qE "${spec_imports}" <<<"${mod}"; then
    echo "error: ${file}:${line}: specification file imports ${mod}, outside the trusted base (TRUSTED.md)" >&2
    status=1
  fi
done < <(LC_ALL=C grep -nHE '^[[:space:]]*(public[[:space:]]+)?import[[:space:]]' "${spec_files[@]}")

[ "${status}" -eq 0 ] && echo "Hygiene check passed (${#files[@]} Lean files)."
exit "${status}"
