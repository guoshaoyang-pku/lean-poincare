#!/bin/bash
# D13-cross-audit-360-cards round-12 (invocation 9) supplementary screens:
# kernel assumption-as-conclusion (taut) screen and the unused-hypothesis screens,
# re-run for all nine staged packages into audit360/logs-round12/.
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
LOG="$BASE/audit360/logs-round12"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$LOG"

CARDS="D12-connection-curvature D12-volume-ibp D12-spectral-sobolev D12-semantic-ledger D12-comparison-geodesics D12-geometric-compactness D12-surgery-recognition D12-triangulation-topology D12-tensor-maximum-bochner"

for CARD in $CARDS; do
  PKG="$BASE/audit360/pkgs/$CARD"
  cd "$PKG" || { echo "MISSING PKG $CARD"; continue; }
  for F in A3TautScreen A3UnusedHyp A3UnusedHypFull; do
    [ -f "$F.lean" ] || continue
    suf=$(echo "$F" | sed 's/A3TautScreen/tautscreen/; s/A3UnusedHypFull/unusedhypfull/; s/A3UnusedHyp/unusedhyp/')
    { echo "### round12 $F $CARD at $(date -Is)"; } > "$LOG/$CARD.$suf.log" 2>&1
    timeout 3600 lake env lean "$F.lean" >> "$LOG/$CARD.$suf.log" 2>&1
    echo "$?" > "$LOG/$CARD.$suf.rc"
  done
  echo "[$(date -Is)] SCREENS $CARD taut=$(cat $LOG/$CARD.tautscreen.rc 2>/dev/null) unused=$(cat $LOG/$CARD.unusedhyp.rc 2>/dev/null) unusedfull=$(cat $LOG/$CARD.unusedhypfull.rc 2>/dev/null)"
done
echo "[$(date -Is)] ROUND12 SCREENS DONE"
