#!/bin/bash
# Session 21 fresh independent gate from worktree root
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-reduced-volume-euclidean
D=longrun/d11rve-session21
: > $D/gate_exit_codes.txt
for F in Basic StraightRays Volume Statements All Probe Audit; do
  lake env lean release/Poincare/D11/ReducedVolume/$F.lean > $D/compile_$F.log 2>&1
  echo "$F $?" >> $D/gate_exit_codes.txt
done
echo "=== gate done ==="
cat $D/gate_exit_codes.txt
