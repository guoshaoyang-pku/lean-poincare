#!/bin/bash
# Wait for the pending round-11 Lean jobs (independent cones / use probes) and then
# regenerate every derived artifact and the two deliverables.  Safe to run detached.
set -u
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
cd "$WT" || exit 1
DEADLINE=$(( $(date +%s) + 5400 ))
while [ "$(date +%s)" -lt "$DEADLINE" ]; do
  RUNNING=$(ps -eo args | grep -c "[i]ndep_cones\.py\|[u]se_probe\.py")
  if [ "$RUNNING" -eq 0 ]; then break; fi
  sleep 60
done
{
  echo "waited until $(date -Is); remaining jobs: $(ps -eo args | grep -c '[i]ndep_cones\.py\|[u]se_probe\.py')"
  python3 audit360/r11/producer_refs.py
  python3 audit360/r11/card8_closures.py
  python3 audit360/r11/claim_consistency.py
  python3 audit360/r11/finalize_round11.py
  python3 audit360/verify_own_hashes.py
  echo "WATCHER DONE $(date -Is)"
} > audit360/r11/wait_and_finalize.log 2>&1
