#!/bin/bash
# D13-cross-audit-360-cards round-6 COLD rebuilds.
# For each card that was never cold-rebuilt (round 1 cold-rebuilt
# D12-connection-curvature and D12-surgery-recognition), copy the staged
# package WITHOUT any .lake/build cache into audit360/pkgs-cold6/<card>,
# re-link the shared pinned mathlib package cache, and rebuild from source +
# re-run the independent per-declaration axiom probe.
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
COLD="$BASE/audit360/pkgs-cold6"
LOG="$BASE/audit360/logs-cold6"
SHARED=/data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$COLD" "$LOG"

CARDS="D12-volume-ibp D12-spectral-sobolev D12-semantic-ledger D12-comparison-geodesics D12-geometric-compactness"

for CARD in $CARDS; do
  SRC="$BASE/audit360/pkgs/$CARD"
  DST="$COLD/$CARD"
  rm -rf "$DST"
  mkdir -p "$DST"
  (cd "$SRC" && tar cf - --exclude=.lake .) | (cd "$DST" && tar xf -)
  mkdir -p "$DST/.lake"
  ln -sfn "$SHARED" "$DST/.lake/packages"
  echo "[$(date -Is)] COLD START $CARD files=$(find "$DST" -name '*.lean' | wc -l) cache=$(test -e "$DST/.lake/build" && echo present || echo absent)"
  cd "$DST" || continue
  {
    echo "### COLD round6 card=$CARD at $(date -Is)"
    echo "### NO .lake/build before build: $(test -e .lake/build && echo FAIL-present || echo confirmed-absent)"
    echo "### probe sha256: $(sha256sum A3Probe.lean | cut -d' ' -f1)"
  } > "$LOG/$CARD.cold.build.log" 2>&1
  timeout 7200 lake build >> "$LOG/$CARD.cold.build.log" 2>&1
  echo "$?" > "$LOG/$CARD.cold.build.rc"
  { echo "### COLD probe $CARD at $(date -Is)"; } > "$LOG/$CARD.cold.probe.log" 2>&1
  timeout 3600 lake env lean A3Probe.lean >> "$LOG/$CARD.cold.probe.log" 2>&1
  echo "$?" > "$LOG/$CARD.cold.probe.rc"
  echo "[$(date -Is)] COLD DONE $CARD build=$(cat "$LOG/$CARD.cold.build.rc") probe=$(cat "$LOG/$CARD.cold.probe.rc")"
done
echo "[$(date -Is)] COLD ROUND6 DONE"
