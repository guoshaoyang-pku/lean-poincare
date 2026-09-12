#!/usr/bin/env bash
# Round-4 closed-form module: read-only axiom audit with a logged exit code.
set -u
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-ricci-to-doubling
REL=$WT/release
LOG=$WT/logs/round4-closedform-audit.log
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd "$REL" || exit 99
{
  echo "=== round-4 closed-form axiom audit $(date -u +%Y-%m-%dT%H:%M:%SZ) ==="
  lake env lean Audit/RicciToDoublingHyperbolicClosedFormAudit.lean
  echo "AUDIT3-EXIT=$?"
} > "$LOG" 2>&1
tail -2 "$LOG"
