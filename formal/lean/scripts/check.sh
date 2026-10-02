#!/usr/bin/env bash
# One-command check of the Thomson N = 11 challenge against plain Mathlib (no Physlib; Comparator and
# a second kernel would be added later, following the N = 7 package).
# Adapted from references/thomson-n7-lean/formal/lean/scripts/check.sh for the N = 11 foundation:
#   - hashes are read from SHA256SUMS.txt (written by scripts/pin_hashes.sh); while that file is absent
#     the hash step is SKIPPED with a notice (allowed during the foundation phase);
#   - the solution preamble identity check is deferred while ThomsonN11/Solution.lean is a placeholder;
#   - the claims.tsv index (paper-to-Lean) is dropped: there is no paper yet.
# Needs: elan (Lean toolchain manager), git, python3, network for the first run (Mathlib + its cache),
# about 14 GB RAM and 10 GB disk.
# Usage: bash scripts/check.sh                (run from anywhere)
#        SKIP_BUILD=1 bash scripts/check.sh   (only the checks that need no build: hashes, preamble, token scan)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
LOGS="$ROOT/logs"; mkdir -p "$LOGS"
CHAL=ComparatorChallenges/ThomsonN11.lean
SOL=ThomsonN11/Solution.lean
SUMS=SHA256SUMS.txt
step() { printf '\n== %s\n' "$*"; }
sha() { python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"; }

step "1. file identity (SHA256SUMS.txt, written by scripts/pin_hashes.sh)"
if [ -f "$SUMS" ]; then
  fail=0
  while read -r h p; do
    [ -n "$h" ] || continue
    if [ "$(sha "$p")" = "$h" ]; then echo "ok  $p"; else echo "HASH MISMATCH: $p"; fail=1; fi
  done < "$SUMS"
  [ "$fail" = 0 ] || exit 1
else
  echo "SKIP: $SUMS not pinned yet (foundation phase). Run scripts/pin_hashes.sh to pin it."
fi

step "2. statement preamble: $SOL must repeat the challenge preamble verbatim"
MARK='/-! ## Challenge statements'
if grep -qF "$MARK" "$SOL"; then
  n="$(grep -nF "$MARK" "$CHAL" | head -1 | cut -d: -f1)"
  diff <(sed -n "1,${n}p" "$CHAL") <(sed -n "1,${n}p" "$SOL") && echo "identical (preamble of $n lines)"
else
  echo "DEFERRED: $SOL is still the placeholder. Once the preamble (up to '$MARK') is copied \
into it, this step diffs the two byte for byte, as in the N = 7 package."
fi

step "3. token scan of $SOL (expect no output between the markers)"
echo "-- begin"
grep -nE 'sorry|native_decide|ofReduceBool|ofReduceNat|trustCompiler|^\s*(private |protected |noncomputable )*(axiom|opaque|unsafe|partial) |set_option|implemented_by|@\[extern|csimp|^\s*(macro|syntax|elab|notation|infix|prefix|postfix|open Lean|initialize|run_cmd)|#eval|#exit' $SOL || true
echo "-- end"

if [ "${SKIP_BUILD:-0}" = "1" ]; then echo; echo "SKIP_BUILD=1: stopping before the build."; exit 0; fi

step "4. toolchain and Mathlib (pinned by lean-toolchain, lakefile.toml, lake-manifest.json)"
cat lean-toolchain
lake exe cache get || echo "cache get failed: continuing, Mathlib will compile from source (hours)"

step "5. lake build (the challenge has 2 expected 'declaration uses sorry' warnings; the solution must have none)"
if [ -x /usr/bin/time ]; then TIME_PRE=(/usr/bin/time -p); else TIME_PRE=(); fi
"${TIME_PRE[@]}" lake build ThomsonN11 ComparatorChallenges 2>&1 | tee "$LOGS/build.log" | tail -25
echo "sorry warnings in $CHAL: $(grep -c "$CHAL.*sorry" "$LOGS/build.log" || true) (expect 2)"
echo "sorry warnings in $SOL:  $(grep -c "$SOL.*sorry" "$LOGS/build.log" || true) (expect 0)"

step "6. axioms of the two theorems (expect propext, Classical.choice, Quot.sound only)"
lake env lean scripts/CheckAxioms.lean | tee "$LOGS/axioms.log"
if grep -E 'sorryAx|ofReduceBool|ofReduceNat|trustCompiler' "$LOGS/axioms.log"; then echo "FORBIDDEN AXIOM"; exit 1; fi

step "7. statement fidelity: every challenge constant has the same type (and value, for definitions) in the solution"
dump() {  # $1 = module, $2 = tag
  { printf 'import %s\n' "$1"; sed -e "s/DUMPMOD/$1/g" -e "s#OUTFILE#$LOGS/$2.tsv#" scripts/DumpBody.lean; } > "$LOGS/Dump$2.lean"
  lake env lean "$LOGS/Dump$2.lean"
}
dump ComparatorChallenges.ThomsonN11 Challenge
cut -f1 "$LOGS/Challenge.tsv" > "$LOGS/Challenge.names"
DUMP_ONLY="$LOGS/Challenge.names" dump ThomsonN11.Solution Solution
python3 scripts/compare_statements.py "$LOGS/Challenge.tsv" "$LOGS/Solution.tsv" | tee "$LOGS/statement.log"

step "DONE: all checks above passed (a failing step stops the script)"
