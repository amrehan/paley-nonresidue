#!/usr/bin/env bash
# Reproduce everything from pinned upstream commits. Any Lean error, missing `#print axioms` line, or axiom
# other than propext / Classical.choice / Quot.sound makes this script fail.
#
#   ./reproduce.sh all     # Alpöge's archive via the community cache (~110 GB disk, ~12 GB RAM, ~30-60 min)
# Env: WORK=<dir> (default ./work). Heavy Lean jobs run one at a time (the archive import alone needs ~12 GB).
#
# Unlike grh-miller there is no separate "conditional" build on zeta-23-lean: the analytic inputs (truncated
# explicit formula and zero counting, uniform in the modulus) come from Alpöge's archive itself.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WORK="${WORK:-$HERE/work}"
RH_REV=f28a764e76a18f68680446bf09682c24d1a8b5c4    # leanprover-community/riemann-hypothesis
STD='depends on axioms: [propext, Classical.choice, Quot.sound]'
MODULES="Paley.PsiBound Paley.Squares Paley.Count Paley.Main Paley.Final Paley.Clique"
mkdir -p "$WORK"
ulimit -n 65536 2>/dev/null || true

# check_log <log> <expected number of #print axioms lines>
check_log() {
  local log=$1 want=$2 got bad
  if grep -E '^[^ ]*:[0-9]+:[0-9]+: error|^error' "$log"; then echo "FAIL: Lean errors in $log"; exit 1; fi
  got=$(grep -c 'depends on axioms' "$log" || true)
  bad=$(grep 'depends on axioms' "$log" | grep -vF "$STD" || true)
  if [ -n "$bad" ]; then echo "FAIL: non-standard axioms:"; echo "$bad"; exit 1; fi
  if [ "$got" -ne "$want" ]; then echo "FAIL: expected $want axiom lines, got $got ($log)"; exit 1; fi
  grep 'depends on axioms' "$log"
}

# The cache downloads fetch hundreds of files in parallel and can drop connections (notably through
# Docker Desktop's network proxy), leaving truncated archives. `lake exe cache get` stops at the first bad
# file, so after a failure we hash every archive against the pinned SHA-256 manifest, delete the bad ones, retry.
cache_get() {
  local i
  for i in $(seq 1 20); do
    lake exe cache get && return 0
    echo "cache get failed (attempt $i/20)"
    if [ -f scripts/ci-cache-get.py ]; then python3 "$HERE/scripts/verify-rh-cache.py" "$PWD" || true; fi
    sleep 10
  done
  return 1
}

all() {
  cd "$WORK"
  [ -d riemann-hypothesis ] || git clone https://github.com/leanprover-community/riemann-hypothesis
  cd riemann-hypothesis && git checkout -q "$RH_REV"
  # the cache restore needs a clean checkout: undo our additions from any previous run first
  git checkout -q -- lakefile.toml && git clean -fdq -- src
  cache_get
  lake build --no-build
  rm -rf src/Paley src/Paley.lean
  cp -R "$HERE/Paley" src/Paley && cp "$HERE/Paley.lean" src/Paley.lean
  mkdir -p src/Unconditional && cp "$HERE/Unconditional/Unconditional.lean" src/Unconditional/
  printf '\n[[lean_lib]]\nname = "Paley"\nroots = ["Paley"]\n' >> lakefile.toml
  echo "== building Paley on Alpöge's archive"
  lake build Paley
  echo "== axioms of the GRH-conditional theorems (scripts/AxiomsConditional.lean)"
  lake env lean "$HERE/scripts/AxiomsConditional.lean" > "$WORK/conditional-axioms.log" 2>&1 \
    || { tail -40 "$WORK/conditional-axioms.log"; echo "FAIL: Lean exited nonzero"; exit 1; }
  check_log "$WORK/conditional-axioms.log" 8
  echo "== compiling Unconditional/Unconditional.lean (imports all of Alpöge's archive)"
  lake env lean src/Unconditional/Unconditional.lean > "$WORK/unconditional.log" 2>&1 \
    || { tail -40 "$WORK/unconditional.log"; echo "FAIL: Lean exited nonzero"; exit 1; }
  check_log "$WORK/unconditional.log" 4
  echo "== independent kernel replay (leanchecker), one module per process"
  for m in $MODULES; do
    lake env leanchecker "$m"
    echo "leanchecker $m: OK"
  done
  echo "== all: OK"
}

case "${1:-}" in
  all|unconditional) all ;;
  *) echo "usage: $0 all"; exit 2 ;;
esac
