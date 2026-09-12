#!/bin/bash
# D13: build the selected adapter probes under the upstream pin
# (Lean v4.32.1 + mathlib 520045ab).  Records one log + exit code per target.
#
# Usage: tools/d13_build_probes.sh Target1 Target2 ...
set -uo pipefail
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-upstream-api-inventory-3602
export ELAN_HOME="$WT/.elan-home"
export ALL_PROXY=socks5h://127.0.0.1:1080
export PATH="/data/home/guoshaoyang/workdir/lean_poincare/elan/bin:$PATH"
mkdir -p "$WT/logs"
cd "$WT/probes" || exit 1
SUMMARY="$WT/logs/build-summary.txt"
for t in "$@"; do
  log="$WT/logs/build-${t//./_}.log"
  start=$(date +%s)
  echo "[build] $t start $(date -Is)" | tee -a "$SUMMARY"
  lake build "$t" >"$log" 2>&1
  code=$?
  end=$(date +%s)
  echo "[build] $t exit=$code seconds=$((end-start)) log=$log" | tee -a "$SUMMARY"
done
