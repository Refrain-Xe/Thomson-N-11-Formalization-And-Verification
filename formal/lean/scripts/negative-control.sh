#!/usr/bin/env bash
# Negative control for step 7 of check.sh: does the statement comparison have teeth?
# Flips the inequality of thomson_eleven_M1 in a scratch copy of the challenge file and expects
# compare_statements.py to FAIL, naming exactly that theorem. Run after check.sh (needs the built
# workspace and logs/Challenge.tsv).
# Adapted from references/thomson-n7-lean/formal/lean/scripts/negative-control.sh.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
LOGS="$ROOT/logs"; mkdir -p "$LOGS"
T="$(mktemp -d)"
sed 's@(155 / 4 : ℝ) ≤ coulombEnergy x := by@coulombEnergy x ≤ (155 / 4 : ℝ) := by@' ComparatorChallenges/ThomsonN11.lean > "$T/ChallengeT.lean"
diff ComparatorChallenges/ThomsonN11.lean "$T/ChallengeT.lean" >/dev/null && { echo "mutation did not apply"; exit 1; }
lake env lean --root="$T" -o "$T/ChallengeT.olean" "$T/ChallengeT.lean" >/dev/null 2>&1 || true
{ echo 'import ChallengeT'; sed -e "s/DUMPMOD/ChallengeT/g" -e "s#OUTFILE#$T/ChallengeT.tsv#" scripts/DumpBody.lean; } > "$T/DumpT.lean"
LP="$(lake env printenv LEAN_PATH)"
lake env env LEAN_PATH="$T:$LP" lean "$T/DumpT.lean"
OUT="$(python3 scripts/compare_statements.py "$LOGS/Challenge.tsv" "$T/ChallengeT.tsv" || true)"
printf '%s\n' "$OUT" | tee "$LOGS/negative-control.log"
if printf '%s\n' "$OUT" | grep -q "mismatches: \['ThomsonN11.thomson_eleven_M1'\]" && printf '%s\n' "$OUT" | grep -q "STATEMENT COMPARISON: FAILED"; then
  echo "NEGATIVE CONTROL OK: the tampered statement was detected (and only that one)"
else
  echo "NEGATIVE CONTROL FAILED: the comparison did not flag the tampered theorem"; exit 1
fi
