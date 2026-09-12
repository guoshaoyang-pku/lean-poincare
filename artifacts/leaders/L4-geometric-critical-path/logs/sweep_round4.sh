#!/usr/bin/env bash
# Round-4 release-wide authored-file sweep: compile every authored .lean file under release/
# individually with the pinned toolchain. Writes a summary line per file.
set -u
ROOT="$(cd "$(dirname "$0")/../release" && pwd)"
TC=/data3/guoshaoyang/workdir/lean_poincare/elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin
OUT="$ROOT/../logs/round4-sweep.log"
: > "$OUT"
FILES=$(cd "$ROOT" && find . -name '*.lean' -not -path './.lake/*' | sed 's|^\./||' | sort)
TOTAL=$(echo "$FILES" | wc -l)
echo "=== ROUND 4 RELEASE-WIDE AUTHORED SWEEP $(date -u +%Y-%m-%dT%H:%M:%SZ) TOTAL=$TOTAL ===" >> "$OUT"
export TC ROOT OUT
compile_one() {
  f="$1"
  if (cd "$ROOT" && timeout 900 "$TC/lake" env lean "$f" > /tmp/sweep_$$.out 2>&1); then
    echo "OK $f"
  else
    echo "FAIL $f"; sed -n '1,20p' /tmp/sweep_$$.out | sed 's/^/    /'
  fi
}
export -f compile_one
echo "$FILES" | xargs -P 8 -I{} bash -c 'compile_one "$@"' _ {} >> "$OUT" 2>&1
FAILS=$(grep -c '^FAIL' "$OUT" || true)
echo "SWEEP_TOTAL=$TOTAL SWEEP_FAIL=$FAILS" >> "$OUT"
echo "SWEEP_DONE" >> "$OUT"
