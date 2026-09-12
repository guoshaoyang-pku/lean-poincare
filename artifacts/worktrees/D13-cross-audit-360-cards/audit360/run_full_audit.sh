#!/bin/bash
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
CARD="$1"
PKG="$BASE/audit360/pkgs/$CARD"
LOG="$BASE/audit360/logs"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd "$PKG" || exit 90
timeout 3600 lake env lean A3FullAudit.lean > "$LOG/$CARD.fullaudit.log" 2>&1
echo "$?" > "$LOG/$CARD.fullaudit.rc"
echo "[$(date -Is)] FULLAUDIT $CARD rc=$(cat $LOG/$CARD.fullaudit.rc)"
