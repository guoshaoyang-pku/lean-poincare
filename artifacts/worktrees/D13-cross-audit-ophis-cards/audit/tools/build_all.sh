#!/usr/bin/env bash
set -u
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards
for t in "$@"; do
  echo "### $(date -Is) BUILD $t"
  bash "$WT/audit/tools/cold_build.sh" "$t" >> "$WT/audit/logs/build_all.log" 2>&1
  echo "### $(date -Is) EXIT $t rc=$?"
done
echo "### $(date -Is) BUILD_ALL_DONE"
