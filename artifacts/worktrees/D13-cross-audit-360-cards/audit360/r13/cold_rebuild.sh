#!/usr/bin/env bash
# A3 round-13 cold rebuild: copy each staged package WITHOUT .lake/build and
# rebuild every local module from source (the shared .lake/packages symlink is
# preserved, so mathlib/deps are reused but every package module is recompiled).
set -u
ROOT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
SRC=$ROOT/audit360/pkgs
DST=$ROOT/audit360/r13/rebuild
LOGS=$ROOT/audit360/r13/logs
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH=$ELAN_HOME/bin:$PATH
mkdir -p "$DST" "$LOGS"
CARDS="D12-connection-curvature D12-volume-ibp D12-spectral-sobolev D12-semantic-ledger D12-comparison-geodesics D12-geometric-compactness D12-surgery-recognition D12-triangulation-topology D12-tensor-maximum-bochner"
build_one() {
  local card="$1"
  local out="$DST/$card"
  rm -rf "$out"
  mkdir -p "$out"
  # copy package sources and config, skipping any build cache
  (cd "$SRC/$card" && tar cf - --exclude='./.lake/build' .) | (cd "$out" && tar xf -)
  echo "=== $card cold rebuild start $(date -Is) ==="
  ( cd "$out" && timeout 3000 lake build ) >"$LOGS/rebuild_$card.log" 2>&1
  echo "rc=$? card=$card end=$(date -Is)" >>"$LOGS/rebuild_$card.log"
  echo "=== $card done rc=$(tail -1 "$LOGS/rebuild_$card.log") ==="
}
pids=()
for c in $CARDS; do
  build_one "$c" &
  pids+=($!)
done
rc=0
for p in "${pids[@]}"; do wait "$p" || rc=1; done
echo "ALL_DONE rc=$rc $(date -Is)"
