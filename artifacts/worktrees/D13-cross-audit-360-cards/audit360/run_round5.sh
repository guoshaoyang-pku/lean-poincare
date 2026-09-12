#!/bin/bash
# D13-cross-audit-360-cards round-5 re-verification sweep.
# Rebuilds each available card from the staged source copy, re-runs the generated
# per-declaration axiom probe and the complete-namespace metaprogram audit, plus the
# negative control and the A3 D2/D3 counterexample probe.  Logs to audit360/logs-round5/.
set -u
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
LOG="$BASE/audit360/logs-round5"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$LOG"

CARDS="D12-connection-curvature D12-volume-ibp D12-spectral-sobolev D12-semantic-ledger D12-comparison-geodesics D12-geometric-compactness D12-surgery-recognition"

for CARD in $CARDS; do
  PKG="$BASE/audit360/pkgs/$CARD"
  cd "$PKG" || { echo "MISSING PKG $CARD"; continue; }
  echo "[$(date -Is)] START $CARD"
  {
    echo "### round5 card=$CARD cwd=$PKG at $(date -Is)"
    echo "### lean-toolchain: $(cat lean-toolchain)"
    echo "### mathlib rev: $(python3 -c "import json;print([p.get('rev') for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")"
    echo "### probe sha256: $(sha256sum A3Probe.lean | cut -d' ' -f1)"
    echo "### fullaudit sha256: $(sha256sum A3FullAudit.lean | cut -d' ' -f1)"
  } > "$LOG/$CARD.build.log" 2>&1
  timeout 5400 lake build >> "$LOG/$CARD.build.log" 2>&1
  echo "$?" > "$LOG/$CARD.build.rc"
  {
    echo "### round5 probe $CARD at $(date -Is)"
  } > "$LOG/$CARD.probe.log" 2>&1
  timeout 3600 lake env lean A3Probe.lean >> "$LOG/$CARD.probe.log" 2>&1
  echo "$?" > "$LOG/$CARD.probe.rc"
  if [ -d A3Extra ]; then
    for f in A3Extra/*.lean; do
      [ -e "$f" ] || continue
      b=$(basename "$f" .lean)
      timeout 3600 lake env lean "$f" > "$LOG/$CARD.extra.$b.log" 2>&1
      echo "$?" > "$LOG/$CARD.extra.$b.rc"
    done
  fi
  timeout 3600 lake env lean A3FullAudit.lean > "$LOG/$CARD.fullaudit.log" 2>&1
  echo "$?" > "$LOG/$CARD.fullaudit.rc"
  echo "[$(date -Is)] DONE $CARD build=$(cat $LOG/$CARD.build.rc) probe=$(cat $LOG/$CARD.probe.rc) fullaudit=$(cat $LOG/$CARD.fullaudit.rc)"
done

# negative control: the fail-closed cones predicate must flag sorryAx and native_decide
cd "$BASE/audit360/pkgs/D12-spectral-sobolev" || exit 91
{
  echo "### negative control at $(date -Is)"
  timeout 1800 lake env lean "$BASE/audit360/negcontrol/A3NegativeControl.lean"
  echo "### rc=$?"
} > "$LOG/negative_control.log" 2>&1

# A3 D2/D3 counterexample probe re-run (independent copy of the D6 release)
A3="$BASE/a3d2d3"
cd "$A3" || exit 92
{
  echo "### a3d2d3 build at $(date -Is)"
} > "$LOG/a3d2d3.build.log" 2>&1
timeout 5400 lake build >> "$LOG/a3d2d3.build.log" 2>&1
echo "$?" > "$LOG/a3d2d3.build.rc"
timeout 3600 lake env lean A3D2D3.lean > "$LOG/a3d2d3.probe.log" 2>&1
echo "$?" > "$LOG/a3d2d3.probe.rc"
sha256sum A3D2D3.lean > "$LOG/a3d2d3.probe.sha256"
echo "[$(date -Is)] ROUND3 DONE"
