#!/bin/bash
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
PKG="$BASE/audit360/pkgs/D12-semantic-ledger-snapshot"
LOG="$BASE/audit360/logs-round5"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd "$PKG" || exit 90
{
  echo "### snapshot rebuild audit $(date -Is)"
  echo "### START lake build"
} > "$LOG/D12-semantic-ledger-snapshot.build.log" 2>&1
timeout 5400 lake build >> "$LOG/D12-semantic-ledger-snapshot.build.log" 2>&1
echo "$?" > "$LOG/D12-semantic-ledger-snapshot.build.rc"
{ echo "### START probe $(date -Is)"; } > "$LOG/D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.log" 2>&1
timeout 3600 lake env lean A3Extra/D12RealModuleProbe.lean >> "$LOG/D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.log" 2>&1
echo "$?" > "$LOG/D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.rc"
echo "[$(date -Is)] DONE snapshot build=$(cat $LOG/D12-semantic-ledger-snapshot.build.rc) probe=$(cat $LOG/D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.rc)"
