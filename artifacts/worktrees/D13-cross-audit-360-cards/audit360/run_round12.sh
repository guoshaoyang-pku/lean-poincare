#!/bin/bash
# D13-cross-audit-360-cards round-12 (invocation 9) re-verification sweep.
# Tenth full sweep for the seven original cards and the second for the two late
# cards (triangulation-topology, tensor-maximum-bochner).  Rebuilds the staged
# source copy, re-runs the generated per-declaration axiom probe, the
# complete-namespace metaprogram audit, the declaration-kind screen, the
# negative control, the semantic-ledger snapshot and the A3 D2/D3 counterexample
# probes.  Logs to audit360/logs-round12/.
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
  echo "[$(date -Is)] START $CARD"
  {
    echo "### round12 card=$CARD cwd=$PKG at $(date -Is)"
    echo "### lean-toolchain: $(cat lean-toolchain)"
    echo "### mathlib rev: $(python3 -c "import json;print([p.get('rev') for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])")"
    echo "### probe sha256: $(sha256sum A3Probe.lean | cut -d' ' -f1)"
    echo "### fullaudit sha256: $(sha256sum A3FullAudit.lean | cut -d' ' -f1)"
    echo "### kindaudit sha256: $(sha256sum A3KindAudit.lean | cut -d' ' -f1)"
  } > "$LOG/$CARD.build.log" 2>&1
  timeout 5400 lake build >> "$LOG/$CARD.build.log" 2>&1
  echo "$?" > "$LOG/$CARD.build.rc"
  { echo "### round12 probe $CARD at $(date -Is)"; } > "$LOG/$CARD.probe.log" 2>&1
  timeout 3600 lake env lean A3Probe.lean >> "$LOG/$CARD.probe.log" 2>&1
  echo "$?" > "$LOG/$CARD.probe.rc"
  for XD in A3Extra A3ExtraR3 A3ExtraR5 A3ExtraR6 A3ExtraR7 A3ExtraR8; do
    if [ -d "$XD" ]; then
      for f in "$XD"/*.lean; do
        [ -e "$f" ] || continue
        b=$(basename "$f" .lean)
        timeout 3600 lake env lean "$f" > "$LOG/$CARD.$XD.$b.log" 2>&1
        echo "$?" > "$LOG/$CARD.$XD.$b.rc"
      done
    fi
  done
  timeout 3600 lake env lean A3FullAudit.lean > "$LOG/$CARD.fullaudit.log" 2>&1
  echo "$?" > "$LOG/$CARD.fullaudit.rc"
  timeout 3600 lake env lean A3KindAudit.lean > "$LOG/$CARD.kind.log" 2>&1
  echo "$?" > "$LOG/$CARD.kind.rc"
  echo "[$(date -Is)] DONE $CARD build=$(cat $LOG/$CARD.build.rc) probe=$(cat $LOG/$CARD.probe.rc) fullaudit=$(cat $LOG/$CARD.fullaudit.rc) kind=$(cat $LOG/$CARD.kind.rc)"
done

# negative control: the fail-closed cones predicate must flag sorryAx and native_decide
cd "$BASE/audit360/pkgs/D12-spectral-sobolev" || exit 91
{
  echo "### negative control at $(date -Is)"
  timeout 1800 lake env lean "$BASE/audit360/negcontrol/A3NegativeControl.lean"
  echo "### rc=$?"
} > "$LOG/negative_control.log" 2>&1

# semantic-ledger snapshot rebuild
PKG="$BASE/audit360/pkgs/D12-semantic-ledger-snapshot"
cd "$PKG" || exit 93
{ echo "### snapshot rebuild audit $(date -Is)"; } > "$LOG/D12-semantic-ledger-snapshot.build.log" 2>&1
timeout 5400 lake build >> "$LOG/D12-semantic-ledger-snapshot.build.log" 2>&1
echo "$?" > "$LOG/D12-semantic-ledger-snapshot.build.rc"
{ echo "### START snapshot probe $(date -Is)"; } > "$LOG/D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.log" 2>&1
timeout 3600 lake env lean A3Extra/D12RealModuleProbe.lean >> "$LOG/D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.log" 2>&1
echo "$?" > "$LOG/D12-semantic-ledger-snapshot.extra.D12RealModuleProbe.rc"

# A3 D2/D3 counterexample probe re-run
A3="$BASE/a3d2d3"
cd "$A3" || exit 92
{ echo "### a3d2d3 build at $(date -Is)"; } > "$LOG/a3d2d3.build.log" 2>&1
timeout 5400 lake build >> "$LOG/a3d2d3.build.log" 2>&1
echo "$?" > "$LOG/a3d2d3.build.rc"
timeout 3600 lake env lean A3D2D3.lean > "$LOG/a3d2d3.probe.log" 2>&1
echo "$?" > "$LOG/a3d2d3.probe.rc"
timeout 3600 lake env lean A3D2D3Round3.lean > "$LOG/a3d2d3.round3.log" 2>&1
echo "$?" > "$LOG/a3d2d3.round3.rc"
sha256sum A3D2D3.lean > "$LOG/a3d2d3.probe.sha256"
echo "[$(date -Is)] ROUND12 DONE"
