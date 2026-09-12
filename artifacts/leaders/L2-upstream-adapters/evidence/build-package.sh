#!/bin/bash
# Build one upstream Frenzymath package at its own pin, inside this worktree.
# Usage: build-package.sh <package-dir-relative-to-snapshot> <label>
set -u
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L2-upstream-adapters
export MATHLIB_CACHE_DIR="$WT/evidence/mathlib-cache"
SNAP="$WT/third_party/frenzymath/Poincare-Conjecture"
LOG="$WT/evidence/logs"
PKG="$SNAP/$1"
LABEL="$2"
mkdir -p "$MATHLIB_CACHE_DIR" "$LOG"
{ echo "=== $(date -u +%FT%TZ) seed deps for $1 ==="; } >> "$LOG/$LABEL-cache.log"
python3 "$WT/evidence/seed-packages.py" "$PKG" >> "$LOG/$LABEL-cache.log" 2>&1
echo "SEED_EXIT=$?" >> "$LOG/$LABEL-cache.log"
cd "$PKG" || exit 90
{ echo "=== $(date -u +%FT%TZ) lake exe cache get ($1) ==="; } >> "$LOG/$LABEL-cache.log"
lake exe cache get >> "$LOG/$LABEL-cache.log" 2>&1
echo "CACHE_EXIT=$?" >> "$LOG/$LABEL-cache.log"
{ echo "=== $(date -u +%FT%TZ) lake build ($1) ==="; } >> "$LOG/$LABEL-build.log"
lake build >> "$LOG/$LABEL-build.log" 2>&1
echo "BUILD_EXIT=$?" >> "$LOG/$LABEL-build.log"
{ echo "=== $(date -u +%FT%TZ) done $1 ==="; } >> "$LOG/$LABEL-build.log"
