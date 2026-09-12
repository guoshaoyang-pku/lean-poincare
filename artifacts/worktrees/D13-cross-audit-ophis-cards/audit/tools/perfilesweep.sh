#!/usr/bin/env bash
# Independent per-file compile gate (mirrors the dispatcher's compile_gate semantics:
# every .lean file under release/ must elaborate with `lake env lean` and exit 0).
# usage: perfilesweep.sh <task> [jobs]
set -u
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards
TASK="$1"; JOBS="${2:-48}"
REL="$WT/audit/build/$TASK/release"
OUT="$WT/audit/logs/$TASK-perfile-gate"
mkdir -p "$OUT"
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd "$REL" || { echo "NO BUILD $TASK"; exit 2; }
find . -name '*.lean' -not -path './.lake/*' | sed 's|^\./||' | sort > "$OUT/files.txt"
echo "files=$(wc -l < "$OUT/files.txt") start=$(date -Is)"
sweep() {
  f="$1"
  timeout 900 lake env lean "$f" > "$OUT/$(echo "$f" | tr '/' '_').log" 2>&1
  echo "$? $f"
}
export -f sweep
export OUT
xargs -a "$OUT/files.txt" -P "$JOBS" -I{} bash -c 'sweep "$@"' _ {} > "$OUT/results.txt" 2>&1
echo "nonzero:"
awk '$1 != 0' "$OUT/results.txt" | head -30
echo "total_files=$(wc -l < "$OUT/results.txt") nonzero=$(awk '$1 != 0' "$OUT/results.txt" | wc -l) end=$(date -Is)"
