#!/usr/bin/env bash
# =============================================================================
#  Reproduce every confirmed defect in this directory, and check that the
#  controls still behave correctly.
#
#  Exits 0 if every theory behaves as recorded, 1 otherwise -- so this doubles
#  as a regression check against a patched build.  Against a build with
#  tamarin-prover PR #915 or #916 applied, the corresponding defects are
#  EXPECTED to stop reproducing and this script is expected to exit 1.
#
#  Usage:  ./run.sh [path-to-tamarin-prover]
# =============================================================================
set -uo pipefail

TAMARIN="${1:-tamarin-prover}"
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
FAILURES=0

if ! command -v "$TAMARIN" >/dev/null 2>&1; then
  echo "error: '$TAMARIN' not found on PATH. Pass the binary path as \$1." >&2
  exit 2
fi

echo "tamarin: $("$TAMARIN" --version 2>/dev/null | head -1)"
echo

summary_of() {
  timeout 300 "$TAMARIN" --prove "$1" 2>/dev/null \
    | sed -n '/^summary of summaries:/,$p' \
    | grep -E '^  [A-Za-z_][A-Za-z0-9_]* \(' || true
}

# expect <file> <description> <regex>...
expect() {
  local file="$1"; shift
  local desc="$1";  shift
  local out ok=1 rx

  printf '%s\n' "── $(basename "$file")"
  printf '   %s\n' "$desc"
  out="$(summary_of "$DIR/$file")"

  if [ -z "$out" ]; then
    printf '   RESULT: no summary produced (parse error or timeout)\n\n'
    FAILURES=$((FAILURES + 1))
    return
  fi

  printf '%s\n' "$out" | sed 's/^/     /'

  for rx in "$@"; do
    if ! printf '%s\n' "$out" | grep -Eq "$rx"; then
      printf '   MISSING: %s\n' "$rx"
      ok=0
    fi
  done

  if [ "$ok" -eq 1 ]; then
    printf '   RESULT: REPRODUCED\n\n'
  else
    printf '   RESULT: NOT reproduced (behaviour changed, or fixed)\n\n'
    FAILURES=$((FAILURES + 1))
  fi
}

echo "============================================================"
echo " 1. last() defeats the safety-formula classifier"
echo "    => unsound induction"
echo "============================================================"
echo

expect 01_last_induction_unsound.spthy \
  "same false lemma: verified WITH induction, falsified WITHOUT" \
  'NoStart_with_induction.*: *verified' \
  'NoStart_without_induction.*: *falsified' \
  'StartReachable.*: *verified'

expect 01b_control_existential_phrasing.spthy \
  "CONTROL: same protocol+lemma, non-safety restriction phrased with a guarded
   existential => correctly falsified. Isolates the mechanism." \
  'NoStart_with_induction.*: *falsified' \
  'NoStart_without_induction.*: *falsified' \
  'StartReachable.*: *verified'

expect 02_last_sources_full_chain.spthy \
  "secrecy of a key sent via Out(k) reported verified; model not vacuous" \
  'bogus_sources.*: *verified' \
  'secrecy.*: *verified' \
  'gen_reachable.*: *verified'

echo "============================================================"
echo " 2. vacuity wellformedness checks are unreachable dead code"
echo "============================================================"
echo

expect 03_vacuous_lemma_typo.spthy \
  "typo'd action fact => lemma is vacuously true, so 'verified' is CORRECT.
   The defect is that no wellformedness warning is emitted: the report is
   clean and the check that would flag the typo never runs." \
  'secrecy_typo.*: *verified' \
  'secrecy_intended.*: *falsified'

echo "============================================================"
if [ "$FAILURES" -eq 0 ]; then
  echo " ALL REPRODUCED"
else
  echo " $FAILURES did NOT reproduce"
fi
echo "============================================================"
echo
echo "Scope check (no shipped case study is affected by 01/02):"
echo "    python3 tools/lastscan.py"
echo "Consistency oracle (produced the negative results in README):"
echo "    python3 tools/consistency_oracle.py"

exit $([ "$FAILURES" -eq 0 ] && echo 0 || echo 1)
