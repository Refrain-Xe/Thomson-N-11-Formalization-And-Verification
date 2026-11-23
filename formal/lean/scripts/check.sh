#!/usr/bin/env bash
# One-command check of the Thomson N = 11 formal proof package against plain Mathlib.
# Adapted from references/thomson-n7-lean/formal/lean/scripts/check.sh and hardened following
# thomson-n9/formal/lean/scripts/check.sh:
#   1. file identity via SHA256SUMS.txt (plus rejection of tracked-but-unpinned files once pinned),
#   2. byte-for-byte verification of the shared base definitions block (`open Real` .. `norm_sq_cyl`),
#   3. forbidden-token scan of ThomsonN11/Solution.lean plus full comment-stripping soundness scan
#      across all ThomsonN11/*.lean modules and lakefile.toml,
#   3b. repo hygiene (no __pycache__/*.pyc tracked by git),
#   4. toolchain and Mathlib cache check (never runs `lake update`),
#   5. `lake build ThomsonN11 ComparatorChallenges` with binding sorry-count verdicts (2 vs 0),
#   6. strict `#print axioms` whitelist (`propext`, `Classical.choice`, `Quot.sound` only),
#   7. declaration-by-declaration statement fidelity check (`compare_statements.py`, SKIP = empty).
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
    [ -e "$p" ] || { echo "MISSING pinned file: $p"; exit 1; }
    if [ "$(sha "$p")" = "$h" ]; then echo "ok  $p"; else echo "HASH MISMATCH: $p"; fail=1; fi
  done < "$SUMS"
  [ "$fail" = 0 ] || exit 1
  DISK_UNPINNED="$(find .gitignore lakefile.toml lake-manifest.json lean-toolchain \
       ThomsonN11.lean ThomsonN11 ComparatorChallenges scripts \
       -type f ! -name "$SUMS" ! -name '*.pyc' ! -name '.DS_Store' ! -path '*/__pycache__/*' | sed 's#^\./##' | LC_ALL=C sort \
       | grep -v -x -F -f <(sed 's/^[0-9a-f]*  //' "$SUMS") || true)"
  [ -z "$DISK_UNPINNED" ] || { echo "UNPINNED PACKAGE FILES ON DISK (run scripts/pin_hashes.sh): $DISK_UNPINNED"; exit 1; }
  if command -v git >/dev/null 2>&1 && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
    UNPINNED="$(git ls-files . | grep -v -x -F "$SUMS" | grep -v -x -F -f <(sed 's/^[0-9a-f]*  //' "$SUMS") || true)"
    [ -z "$UNPINNED" ] || { echo "TRACKED BUT UNPINNED FILES (run scripts/pin_hashes.sh): $UNPINNED"; exit 1; }
  fi
else
  echo "SKIP: $SUMS not pinned yet. Run scripts/pin_hashes.sh to pin it."
fi

step "2. base definitions block: $SOL must repeat '$CHAL' definitions verbatim"
python3 - "$CHAL" "$SOL" <<'PY'
import pathlib, sys

chal = pathlib.Path(sys.argv[1]).read_text()
sol = pathlib.Path(sys.argv[2]).read_text()
start_mark = "open Real\n\nnamespace ThomsonN11"
end_mark = "\n/-! ## Challenge statements"
i0 = chal.find(start_mark)
i1 = chal.find(end_mark)
if i0 < 0 or i1 < 0 or i1 <= i0:
    print("PREAMBLE MARKERS NOT FOUND IN CHALLENGE")
    sys.exit(1)
block = chal[i0:i1]
if block not in sol:
    print("PREAMBLE MISMATCH: shared base definitions block from Challenge not verbatim in Solution")
    sys.exit(1)
print(f"identical base definitions block ({block.count(chr(10)) + 1} lines)")
PY

step "3. token scan of $SOL and all supporting modules (any soundness-affecting hit is fatal)"
SCAN_RE='sorry|native_decide|ofReduceBool|ofReduceNat|trustCompiler|^\s*(private |protected |noncomputable )*(axiom|opaque|unsafe|partial) |set_option|implemented_by|@\[extern|csimp|^\s*(macro|syntax|elab|notation|infix|prefix|postfix|open Lean|initialize|run_cmd)|#eval|#exit'
if hits="$(grep -nE "$SCAN_RE" "$SOL")"; then
  printf '%s\n' "$hits"
  echo "FORBIDDEN TOKEN(S) in $SOL: see the lines above"; exit 1
else
  echo "no forbidden tokens in $SOL"
fi
python3 - <<'PY'
import pathlib, re, sys

def strip_lean_comments(s: str) -> str:
    out, i, n, depth = [], 0, len(s), 0
    while i < n:
        if depth == 0 and s[i:i+2] == "--":
            while i < n and s[i] != "\n":
                i += 1
        elif s[i:i+2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and s[i:i+2] == "-/":
            depth -= 1
            i += 2
        elif depth == 0 and s[i:i+3] == "'\"'":
            out.append("   ")
            i += 3
        elif depth == 0 and s[i:i+4] == "'\\\"'":
            out.append("    ")
            i += 4
        elif depth == 0 and s[i] == '"':
            out.append('"')
            i += 1
            while i < n and s[i] != '"':
                if s[i] == "\\" and i + 1 < n:
                    out.append("  ")
                    i += 2
                else:
                    out.append("\n" if s[i] == "\n" else " ")
                    i += 1
            if i < n:
                out.append('"')
                i += 1
        else:
            out.append("\n" if (depth > 0 and s[i] == "\n") else (" " if depth > 0 else s[i]))
            i += 1
    return "".join(out)

scan_root = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else pathlib.Path("ThomsonN11")

bad_pat = re.compile(
    r"\b(sorry|native_decide|ofReduceBool|ofReduceNat|trustCompiler|skipKernelTC)\b"
    r"|^\s*(private\s+|protected\s+|noncomputable\s+)*(axiom|opaque|unsafe|partial)\s"
    r"|implemented_by|@\[extern|\bcsimp\b|@\[delab"
    r"|^\s*(macro|syntax|elab|notation|infix|prefix|postfix|local\s+instance|open\s+Lean|initialize|run_cmd)\b"
    r"|#eval|#exit",
    re.MULTILINE,
)
opt_pat = re.compile(r"set_option\s+([A-Za-z0-9_.]+)")
allowed_opts = ("maxHeartbeats", "maxRecDepth", "linter.")

for p in sorted(scan_root.rglob("*.lean")):
    clean = strip_lean_comments(p.read_text())
    m = bad_pat.search(clean)
    if m:
        line = clean[:m.start()].count("\n") + 1
        print(f"FORBIDDEN TOKEN in {p}:{line}: {m.group(0)!r}")
        sys.exit(1)
    for om in opt_pat.finditer(clean):
        opt = om.group(1)
        if not any(opt == a or opt.startswith(a) for a in allowed_opts):
            line = clean[:om.start()].count("\n") + 1
            print(f"FORBIDDEN set_option in {p}:{line}: {opt}")
            sys.exit(1)

lake_txt = pathlib.Path("lakefile.toml").read_text()
if re.search(r"leanOptions|moreLeanArgs|weakLeanArgs", lake_txt):
    print("FORBIDDEN compiler options in lakefile.toml")
    sys.exit(1)
print("all ThomsonN11/*.lean modules and lakefile.toml passed full soundness token scan")
PY

step "3b. repo hygiene: no __pycache__/*.pyc, .DS_Store, .lake/, or logs/ tracked by git"
if command -v git >/dev/null 2>&1 && top="$(git rev-parse --show-toplevel 2>/dev/null)"; then
  if tracked="$(git -C "$top" ls-files | grep -E '__pycache__|\.pyc$|\.DS_Store$|formal/lean/(\.lake|logs)/')"; then
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
chal_sorry="$(grep -cE '^[[:space:]]*sorry[[:space:]]*$' "$CHAL")" || true
sol_sorry="$(grep -cE '^[[:space:]]*sorry[[:space:]]*$' "$SOL")" || true
echo "standalone 'sorry' lines in $CHAL: $chal_sorry (expect exactly 2, the two milestone statements)"
echo "standalone 'sorry' lines in $SOL:  $sol_sorry (expect 0)"
[ "$chal_sorry" = 2 ] || { echo "SORRY-COUNT CHECK FAILED: $CHAL has $chal_sorry standalone 'sorry' line(s), expected 2"; exit 1; }
[ "$sol_sorry" = 0 ] || { echo "SORRY-COUNT CHECK FAILED: $SOL has $sol_sorry standalone 'sorry' line(s), expected 0"; exit 1; }
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

step "6. axioms of challenge theorems (strict whitelist: propext, Classical.choice, Quot.sound only)"
if ! lake env lean scripts/CheckAxioms.lean | tee "$LOGS/axioms.log"; then
  echo "AXIOM DUMP FAILED (see $LOGS/axioms.log)"; exit 1
fi
python3 - "$LOGS/axioms.log" <<'PY'
import re, sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
lines = open(sys.argv[1]).read().splitlines()
ax_lines = [l for l in lines if "depends on axioms:" in l]
if len(ax_lines) < 2:
    print(f"EXPECTED >= 2 '#print axioms' lines, got {len(ax_lines)}")
    sys.exit(1)
for l in ax_lines:
    m = re.search(r"depends on axioms: \[(.*)\]$", l)
    if not m:
        print(f"UNRECOGNIZED AXIOM LINE: {l}")
        sys.exit(1)
    axs = {a.strip() for a in m.group(1).split(",") if a.strip()}
    bad = axs - allowed
    if bad:
        print(f"DISALLOWED AXIOMS {sorted(bad)} in: {l}")
        sys.exit(1)
print(f"strict axiom whitelist OK across {len(ax_lines)} declarations: subset of {sorted(allowed)}")
PY

step "7. statement fidelity: every challenge constant has the same type (and value, for definitions) in the solution"
dump() {  # $1 = module, $2 = tag
  { printf 'import %s\n' "$1"; sed -e "s/DUMPMOD/$1/g" -e "s#OUTFILE#$LOGS/$2.tsv#" scripts/DumpBody.lean; } > "$LOGS/Dump$2.lean"
  lake env lean "$LOGS/Dump$2.lean" || { echo "DUMP FAILED for module $1"; exit 1; }
}
dump ComparatorChallenges.ThomsonN11 Challenge
cut -f1 "$LOGS/Challenge.tsv" > "$LOGS/Challenge.names"
DUMP_ONLY="$LOGS/Challenge.names" dump ThomsonN11.Solution Solution
[ -s "$LOGS/Solution.tsv" ] || { echo "EMPTY Solution.tsv"; exit 1; }
if ! python3 scripts/compare_statements.py "$LOGS/Challenge.tsv" "$LOGS/Solution.tsv" | tee "$LOGS/statement.log"; then
  echo "STATEMENT COMPARISON FAILED (see $LOGS/statement.log)"; exit 1
fi

step "DONE: all checks above passed (a failing step stops the script)"
