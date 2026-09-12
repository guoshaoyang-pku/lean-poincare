#!/bin/bash
# L2 M2: build upstream Shared package at its own pin (Lean v4.32.1, mathlib 520045a)
set -x
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L2-upstream-adapters
LOG=$WT/evidence/logs
cd "$WT/third_party/frenzymath/Poincare-Conjecture/shared" || exit 90
{ echo "=== $(date -u +%FT%TZ) lake exe cache get (mathlib 520045a) ==="; } >> "$LOG/shared-cache.log"
lake exe cache get >> "$LOG/shared-cache.log" 2>&1
echo "CACHE_EXIT=$?" >> "$LOG/shared-cache.log"
{ echo "=== $(date -u +%FT%TZ) lake build Shared ==="; } >> "$LOG/shared-build.log"
lake build >> "$LOG/shared-build.log" 2>&1
echo "BUILD_EXIT=$?" >> "$LOG/shared-build.log"
