#!/usr/bin/env bash
# One-command check of the Thomson N = 11 challenge against plain Mathlib (no Physlib; Comparator and
# a second kernel would be added later, following the N = 7 package).
# Adapted from references/thomson-n7-lean/formal/lean/scripts/check.sh for the N = 11 foundation:
#   - hashes are read from SHA256SUMS.txt (written by scripts/pin_hashes.sh); while that file is absent
#     the hash step is SKIPPED with a notice (allowed during the foundation phase);
#   - the solution preamble identity check is deferred while ThomsonN11/Solution.lean is a placeholder;
#   - the claims.tsv index (paper-to-Lean) is dropped: there is no paper yet.
# v2 hardening (every check now exits non-zero on failure instead of just printing):
#   - step 2 preamble diff: explicit PREAMBLE MISMATCH + exit 1 (set -e already caught it, now loudly);
#   - step 3 token scan: any hit in the solution is FATAL (was: printed, never judged);
#   - step 3b (new): repo hygiene -- no __pycache__/*.pyc may be tracked by git;
#   - step 5 build: the /usr/bin/time invocation no longer uses a bash array (latent set -u + empty
#     array bug on macOS's bash 3.2); the build exit code is checked explicitly, and the sorry counts
#     carry verdicts -- binding source-level counts (2 in the challenge, 0 in the solution) plus
#     build-log checks that stay correct across cached rebuilds that re-emit no warnings;
#   - steps 6-7: failures are reported with the log path before exiting.
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
  if diff <(sed -n "1,${n}p" "$CHAL") <(sed -n "1,${n}p" "$SOL"); then
    echo "identical (preamble of $n lines)"
  else
    echo "PREAMBLE MISMATCH: the first $n lines of $SOL differ from $CHAL"; exit 1
  fi
else
  echo "DEFERRED: $SOL is still the placeholder. Once the preamble (up to '$MARK') is copied \
into it, this step diffs the two byte for byte, as in the N = 7 package."
fi

step "3. token scan of $SOL (any hit below is fatal)"
SCAN_RE='sorry|native_decide|ofReduceBool|ofReduceNat|trustCompiler|^\s*(private |protected |noncomputable )*(axiom|opaque|unsafe|partial) |set_option|implemented_by|@\[extern|csimp|^\s*(macro|syntax|elab|notation|infix|prefix|postfix|open Lean|initialize|run_cmd)|#eval|#exit'
if hits="$(grep -nE "$SCAN_RE" "$SOL")"; then
  printf '%s\n' "$hits"
  echo "FORBIDDEN TOKEN(S) in $SOL: see the lines above"; exit 1
else
  echo "no forbidden tokens in $SOL"
fi

step "3b. repo hygiene: no __pycache__/*.pyc tracked by git"
if command -v git >/dev/null 2>&1 && top="$(git rev-parse --show-toplevel 2>/dev/null)"; then
  if tracked="$(git -C "$top" ls-files | grep -E '__pycache__|\.pyc$')"; then
    printf '%s\n' "$tracked"
    echo "TRACKED BYTECODE (already gitignored): fix with: git rm -r --cached <paths above>"; exit 1
  else
    echo "none tracked"
  fi
else
  echo "SKIP: git unavailable or not inside a git work tree"
fi

if [ "${SKIP_BUILD:-0}" = "1" ]; then echo; echo "SKIP_BUILD=1: stopping before the build."; exit 0; fi

step "4. toolchain and Mathlib (pinned by lean-toolchain, lakefile.toml, lake-manifest.json)"
cat lean-toolchain
lake exe cache get || echo "cache get failed: continuing, Mathlib will compile from source (hours)"

step "5. lake build (the challenge has 2 expected 'declaration uses sorry' warnings; the solution must have none)"
rm -f "$LOGS/build.log"
set +e
if [ -x /usr/bin/time ]; then
  /usr/bin/time -p lake build ThomsonN11 ComparatorChallenges >"$LOGS/build.log" 2>&1
else
  lake build ThomsonN11 ComparatorChallenges >"$LOGS/build.log" 2>&1
fi
build_rc=$?
set -e
tail -25 "$LOGS/build.log"
[ "$build_rc" = 0 ] || { echo "LAKE BUILD FAILED (exit $build_rc; see $LOGS/build.log)"; exit 1; }
# Binding source-level counts (deterministic, independent of whether a cached build re-emits warnings):
chal_sorry="$(grep -cE '^[[:space:]]*sorry[[:space:]]*$' "$CHAL")" || true
sol_sorry="$(grep -cE '^[[:space:]]*sorry[[:space:]]*$' "$SOL")" || true
echo "standalone 'sorry' lines in $CHAL: $chal_sorry (expect exactly 2, the two milestone statements)"
echo "standalone 'sorry' lines in $SOL:  $sol_sorry (expect 0)"
[ "$chal_sorry" = 2 ] || { echo "SORRY-COUNT CHECK FAILED: $CHAL has $chal_sorry standalone 'sorry' line(s), expected 2"; exit 1; }
[ "$sol_sorry" = 0 ] || { echo "SORRY-COUNT CHECK FAILED: $SOL has $sol_sorry standalone 'sorry' line(s), expected 0"; exit 1; }
# Build-log level: the solution must never carry a sorry warning; the challenge must carry
# exactly 2 whenever the build actually re-elaborated it (a fully cached build emits none).
chal_warn="$(grep -c "$CHAL.*sorry" "$LOGS/build.log")" || true
sol_warn="$(grep -c "$SOL.*sorry" "$LOGS/build.log")" || true
echo "sorry warnings in $CHAL: $chal_warn (expect 2 on a fresh build, 0 when fully cached)"
echo "sorry warnings in $SOL:  $sol_warn (expect 0)"
[ "$sol_warn" = 0 ] || { echo "SORRY-WARNING CHECK FAILED: the build reported 'sorry' in $SOL"; exit 1; }
if [ "$chal_warn" = 0 ]; then
  echo "note: the build re-emitted no warnings for $CHAL (cached); the source-level count above is the binding check"
else
  [ "$chal_warn" = 2 ] || { echo "SORRY-WARNING CHECK FAILED: $CHAL produced $chal_warn sorry warnings, expected 2"; exit 1; }
fi

step "6. axioms of the two theorems (expect propext, Classical.choice, Quot.sound only)"
if ! lake env lean scripts/CheckAxioms.lean | tee "$LOGS/axioms.log"; then
  echo "AXIOM DUMP FAILED (see $LOGS/axioms.log)"; exit 1
fi
if grep -E 'sorryAx|ofReduceBool|ofReduceNat|trustCompiler' "$LOGS/axioms.log"; then echo "FORBIDDEN AXIOM"; exit 1; fi

step "7. statement fidelity: every challenge constant has the same type (and value, for definitions) in the solution"
dump() {  # $1 = module, $2 = tag
  { printf 'import %s\n' "$1"; sed -e "s/DUMPMOD/$1/g" -e "s#OUTFILE#$LOGS/$2.tsv#" scripts/DumpBody.lean; } > "$LOGS/Dump$2.lean"
  lake env lean "$LOGS/Dump$2.lean" || { echo "DUMP FAILED for module $1"; exit 1; }
}
dump ComparatorChallenges.ThomsonN11 Challenge
cut -f1 "$LOGS/Challenge.tsv" > "$LOGS/Challenge.names"
DUMP_ONLY="$LOGS/Challenge.names" dump ThomsonN11.Solution Solution
if ! python3 scripts/compare_statements.py "$LOGS/Challenge.tsv" "$LOGS/Solution.tsv" | tee "$LOGS/statement.log"; then
  echo "STATEMENT COMPARISON FAILED (see $LOGS/statement.log)"; exit 1
fi

step "DONE: all checks above passed (a failing step stops the script)"
