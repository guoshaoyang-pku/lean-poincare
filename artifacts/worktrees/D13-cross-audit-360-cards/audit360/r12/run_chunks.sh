#!/bin/bash
# Parallel chunked full-namespace cone runs for the two topology-heavy cards.
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
N=8
for CARD in D12-triangulation-topology D12-surgery-recognition; do
  for K in $(seq 0 $((N-1))); do
    A3R12C_TIMEOUT=5400 python3 "$BASE/audit360/r12/indep_cones_chunk.py" "$CARD" "$K" "$N" \
      > "$BASE/audit360/r12/chunk_${CARD}_${K}.driver.log" 2>&1 &
  done
done
wait
for CARD in D12-triangulation-topology D12-surgery-recognition; do
  python3 "$BASE/audit360/r12/indep_cones_merge.py" "$CARD" "$N"
done
echo "[$(date -Is)] CHUNKS DONE"
