#!/bin/bash
# Declaration-kind audit: for every card-declared name, ask the kernel for its
# ConstantInfo variant (theorem vs def vs inductive vs ctor vs rec vs axiom).
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
LOG="$BASE/audit360/logs-kind"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$LOG"

CARDS="D12-connection-curvature D12-volume-ibp D12-spectral-sobolev D12-semantic-ledger D12-comparison-geodesics D12-geometric-compactness D12-surgery-recognition"
for CARD in $CARDS; do
  PKG="$BASE/audit360/pkgs/$CARD"
  cd "$PKG" || { echo "MISSING $CARD"; continue; }
  {
    echo "### kind audit card=$CARD at $(date -Is)"
    echo "### sha256: $(sha256sum A3KindAudit.lean | cut -d' ' -f1)"
  } > "$LOG/$CARD.kind.log" 2>&1
  timeout 1800 lake env lean A3KindAudit.lean >> "$LOG/$CARD.kind.log" 2>&1
  echo "$?" > "$LOG/$CARD.kind.rc"
  echo "[$(date -Is)] KIND $CARD rc=$(cat $LOG/$CARD.kind.rc)"
done
echo "[$(date -Is)] KIND AUDIT DONE"
