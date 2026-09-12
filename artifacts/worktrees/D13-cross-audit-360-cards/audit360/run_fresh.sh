#!/bin/bash
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
CARD="$1"
PKG="$BASE/audit360/pkgs-fresh/$CARD"
LOG="$BASE/audit360/logs"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd "$PKG" || exit 90
{ echo "### COLD (no .lake/build) rebuild $CARD $(date -Is)"; } > "$LOG/$CARD.fresh.build.log" 2>&1
timeout 5400 lake build >> "$LOG/$CARD.fresh.build.log" 2>&1
echo "$?" > "$LOG/$CARD.fresh.build.rc"
{ echo "### COLD probe $(date -Is)"; } > "$LOG/$CARD.fresh.probe.log" 2>&1
timeout 3600 lake env lean A3Probe.lean >> "$LOG/$CARD.fresh.probe.log" 2>&1
echo "$?" > "$LOG/$CARD.fresh.probe.rc"
echo "[$(date -Is)] COLD DONE $CARD build=$(cat $LOG/$CARD.fresh.build.rc) probe=$(cat $LOG/$CARD.fresh.probe.rc)"
