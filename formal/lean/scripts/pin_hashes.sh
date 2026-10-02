#!/usr/bin/env bash
# Write SHA256SUMS.txt for the Lake package (format of the N = 7 package's formal/lean/SHA256SUMS.txt:
# "<sha256>  <relative path>", sorted by path). check.sh step 1 verifies these hashes; run this script
# only when the files it covers are meant to be frozen.
# There is no counterpart in references/thomson-n7-lean (its SHA256SUMS.txt was pinned upstream); this
# script exists so that later runs can pin and re-pin the package without hand-editing a hash list.
# Usage: bash scripts/pin_hashes.sh [--check]
#   without --check: (re)write SHA256SUMS.txt
#   with --check:    verify the existing SHA256SUMS.txt, exit 1 on any mismatch
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
SUMS=SHA256SUMS.txt
files() {  # the frozen set: everything in the package except the sums file itself and build noise
  find .gitignore lakefile.toml lake-manifest.json lean-toolchain \
       ThomsonN11.lean ThomsonN11 ComparatorChallenges scripts \
       -type f ! -name "$SUMS" | sed 's#^\./##' | LC_ALL=C sort
}
case "${1:-}" in
  --check)
    [ -f "$SUMS" ] || { echo "nothing pinned: $SUMS absent"; exit 1; }
    fail=0
    while read -r h p; do
      [ -n "$h" ] || continue
      if [ "$(python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$p")" = "$h" ]; then
        echo "ok  $p"
      else
        echo "HASH MISMATCH: $p"; fail=1
      fi
    done < "$SUMS"
    [ "$fail" = 0 ] && echo "all pinned hashes ok" || exit 1
    ;;
  "")
    tmp="$(mktemp)"
    for p in $(files); do
      python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$p" | tr -d '\n' >> "$tmp"
      printf '  %s\n' "$p" >> "$tmp"
    done
    mv "$tmp" "$SUMS"
    echo "wrote $SUMS:"; cat "$SUMS"
    ;;
  *) echo "usage: $0 [--check]"; exit 2 ;;
esac
