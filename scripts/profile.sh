#!/usr/bin/env bash
# Standard rewriter benchmark: random terms from `telos-fuzz`, timed without
# profiling (wall time), then once with `--profile` (where the time went).
#
# Usage: scripts/profile.sh [COUNT] [DEPTH] [SEED]   (defaults: 3000 4 1)
#
# Builds telos-fuzz first. The profile table goes to standard output; see
# Telos/Core/Profile.lean for what the probes measure.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
count="${1:-3000}"
depth="${2:-4}"
seed="${3:-1}"

lake build telos-fuzz >/dev/null
fuzz=.lake/build/bin/telos-fuzz

wall() {
  local start end
  start=$(date +%s%N)
  "$fuzz" "$seed" "$count" "$depth" "$@" >/dev/null
  end=$(date +%s%N)
  echo "$(( (end - start) / 1000000 ))ms"
}

for mode in bool arith; do
  extra=()
  [ "$mode" = arith ] && extra=(arith)
  echo "== ${mode}: ${count} terms, depth ${depth}, seed ${seed}"
  echo "wall time without profiling (generation and printing included): $(wall "${extra[@]}")"
  "$fuzz" "$seed" "$count" "$depth" "${extra[@]}" --profile 2>&1 >/dev/null
  echo
done
