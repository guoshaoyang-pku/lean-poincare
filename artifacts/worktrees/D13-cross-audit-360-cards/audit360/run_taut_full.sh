#!/bin/bash
# Round-9b full-namespace Prop-gated assumption-as-conclusion screen.
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
LOG="$BASE/audit360/logs-tautfull"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$LOG"
for CARD in D12-connection-curvature D12-volume-ibp D12-spectral-sobolev D12-semantic-ledger D12-comparison-geodesics D12-geometric-compactness D12-surgery-recognition; do
  cd "$BASE/audit360/pkgs/$CARD" || { echo "MISSING $CARD"; continue; }
  timeout 3600 lake env lean A3TautFull.lean > "$LOG/$CARD.log" 2>&1
  echo "$?" > "$LOG/$CARD.rc"
  echo "[$(date -Is)] $CARD rc=$(cat $LOG/$CARD.rc) $(grep -c A3TAUTFULL-FLAG $LOG/$CARD.log) flags $(grep -o 'checked [0-9]*' $LOG/$CARD.log | tail -1)"
done
