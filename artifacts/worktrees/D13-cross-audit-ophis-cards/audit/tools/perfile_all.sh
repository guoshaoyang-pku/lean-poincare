#!/usr/bin/env bash
set -u
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards
for t in "$@"; do
  echo "### $(date -Is) PERFILE $t"
  bash "$WT/audit/tools/perfilesweep.sh" "$t" 64 2>&1 | tail -6
done
echo "### $(date -Is) PERFILE_ALL_DONE"
