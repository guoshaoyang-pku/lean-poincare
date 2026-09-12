#!/usr/bin/env bash
# Fresh per-file compile gate for D11-reduced-volume-euclidean, session22.
set -u
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-reduced-volume-euclidean
DIR=release/Poincare/D11/ReducedVolume
OUT=longrun/d11rve-session22
: > "$OUT/gate_exit_codes.txt"
for F in Basic StraightRays Volume Statements All Probe Audit; do
  echo "=== $F ==="
  lake env lean "$DIR/$F.lean" > "$OUT/compile_$F.log" 2>&1
  code=$?
  echo "$F exit $code" | tee -a "$OUT/gate_exit_codes.txt"
  if [ $code -ne 0 ]; then echo "--- FAILURE LOG $F ---"; tail -40 "$OUT/compile_$F.log"; fi
  wc -l < "$OUT/compile_$F.log" | xargs echo "  log lines:"
done
echo "=== gate summary ==="
cat "$OUT/gate_exit_codes.txt"
