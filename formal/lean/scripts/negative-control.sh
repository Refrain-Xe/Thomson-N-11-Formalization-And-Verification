#!/usr/bin/env bash
# Dual negative controls for check.sh:
#   NC1 (statement fidelity): flips the inequality of thomson_eleven_M1 in a scratch copy of the
#       challenge file and expects compare_statements.py to FAIL, naming exactly that theorem.
#   NC2 (kernel certificate soundness): asserts an inflated SDP rational bound in a scratch Lean
#       module using `by decide +kernel` and expects the Lean 4 kernel to REJECT it.
# Run after check.sh (needs the built workspace and logs/Challenge.tsv).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
LOGS="$ROOT/logs"; mkdir -p "$LOGS"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT

sed 's@(155 / 4 : ℝ) ≤ coulombEnergy x := by@coulombEnergy x ≤ (155 / 4 : ℝ) := by@' ComparatorChallenges/ThomsonN11.lean > "$T/ChallengeT.lean"
diff ComparatorChallenges/ThomsonN11.lean "$T/ChallengeT.lean" >/dev/null && { echo "mutation did not apply"; exit 1; }
lake env lean --root="$T" -o "$T/ChallengeT.olean" "$T/ChallengeT.lean" >/dev/null 2>&1 || true
{ echo 'import ChallengeT'; sed -e "s/DUMPMOD/ChallengeT/g" -e "s#OUTFILE#$T/ChallengeT.tsv#" scripts/DumpBody.lean; } > "$T/DumpT.lean"
LP="$(lake env printenv LEAN_PATH)"
lake env env LEAN_PATH="$T:$LP" lean "$T/DumpT.lean"
OUT="$(python3 scripts/compare_statements.py "$LOGS/Challenge.tsv" "$T/ChallengeT.tsv" || true)"
printf '%s\n' "$OUT" | tee "$LOGS/negative-control.log"
if printf '%s\n' "$OUT" | grep -q "mismatches: \['ThomsonN11.thomson_eleven_M1'\]" && printf '%s\n' "$OUT" | grep -q "STATEMENT COMPARISON: FAILED"; then
  echo "NEGATIVE CONTROL 1 OK: the tampered statement was detected (and only that one)"
else
  echo "NEGATIVE CONTROL 1 FAILED: the comparison did not flag the tampered theorem"; exit 1
fi

cat > "$T/TamperedKernelCert.lean" <<'LEAN'
import ThomsonN11.StageB.SdpCertSosData
open ThomsonN11.StageB.PolyKron ThomsonN11.StageB.SdpCertHarmData ThomsonN11.StageB.SdpCertSosData
-- Attempt to inflate bound_num by +100000000000 (40.557 > certified SDP bound) via `decide +kernel`:
theorem bogus_bound :
    (bound_num + 100000000000) * 36 * (S2 + (l1List res_y_int : Int))
      ≤ bound_den * (36 * e_int - (l1Poly3 res_slack_int : Int)) := by decide +kernel
LEAN
if KOUT="$(lake env lean "$T/TamperedKernelCert.lean" 2>&1)"; then
  printf '%s\n' "$KOUT" >> "$LOGS/negative-control.log"
  echo "NEGATIVE CONTROL 2 FAILED: Lean kernel accepted inflated SDP bound!"; exit 1
else
  printf '%s\n' "$KOUT" | tee -a "$LOGS/negative-control.log"
  echo "NEGATIVE CONTROL 2 OK: Lean kernel rejected inflated SDP bound"
fi

# NC3: String-literal "/-" comment-smuggling attempt around a forbidden option must be caught by check.sh Step 3 scanner!
mkdir -p "$T/ScanT"
cat > "$T/ScanT/Smuggled.lean" <<'LEAN'
def openFakeComment : String := "/-"
set_option debug.skipKernelTC true
def closeFakeComment : String := "-/"
LEAN
SCAN_PY="$(awk '/^python3 - <<'\''PY'\''/{flag=1; next} /^PY$/{flag=0} flag' scripts/check.sh)"
if SOUT="$(python3 -c "$SCAN_PY" "$T/ScanT" 2>&1)"; then
  printf '%s\n' "$SOUT" >> "$LOGS/negative-control.log"
  echo "NEGATIVE CONTROL 3 FAILED: string-smuggled forbidden token escaped check.sh scanner!"; exit 1
else
  printf '%s\n' "$SOUT" | tee -a "$LOGS/negative-control.log"
  echo "NEGATIVE CONTROL 3 OK: string-smuggled forbidden token rejected by check.sh scanner"
fi
