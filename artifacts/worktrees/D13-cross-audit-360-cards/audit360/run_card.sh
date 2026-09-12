#!/bin/bash
# D13 cross-audit: independent rebuild + generated axiom probe for one staged card.
# usage: run_card.sh <card>
set -u
CARD="$1"
BASE=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
PKG="$BASE/audit360/pkgs/$CARD"
LOG="$BASE/audit360/logs"
mkdir -p "$LOG"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd "$PKG" || exit 90
echo "[$(date -Is)] START $CARD"
{
  echo "### card=$CARD cwd=$PKG"
  echo "### lean-toolchain: $(cat lean-toolchain 2>/dev/null)"
  echo "### hash of lakefile.toml: $(sha256sum lakefile.toml 2>/dev/null | cut -d' ' -f1)"
  echo "### mathlib rev: $(python3 -c "import json;print([p.get('rev') for p in json.load(open('lake-manifest.json'))['packages'] if p['name']=='mathlib'][0])" 2>/dev/null)"
  echo "### START lake build $(date -Is)"
} > "$LOG/$CARD.build.log" 2>&1
timeout 5400 lake build >> "$LOG/$CARD.build.log" 2>&1
BUILD_RC=$?
echo "### lake build exit $BUILD_RC at $(date -Is)" >> "$LOG/$CARD.build.log"
echo "$BUILD_RC" > "$LOG/$CARD.build.rc"
{
  echo "### START probe $(date -Is)"
} > "$LOG/$CARD.probe.log" 2>&1
timeout 3600 lake env lean A3Probe.lean >> "$LOG/$CARD.probe.log" 2>&1
PROBE_RC=$?
echo "### A3Probe exit $PROBE_RC at $(date -Is)" >> "$LOG/$CARD.probe.log"
echo "$PROBE_RC" > "$LOG/$CARD.probe.rc"
# extra probes (card-attributed files outside the release tree, e.g. audit_probes)
if [ -d A3Extra ]; then
  for f in A3Extra/*.lean; do
    [ -e "$f" ] || continue
    b=$(basename "$f" .lean)
    timeout 3600 lake env lean "$f" > "$LOG/$CARD.extra.$b.log" 2>&1
    echo "$?" > "$LOG/$CARD.extra.$b.rc"
  done
fi
echo "[$(date -Is)] DONE $CARD build=$BUILD_RC probe=$PROBE_RC"
