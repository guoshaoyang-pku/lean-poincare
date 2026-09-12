#!/usr/bin/env bash
# Run the SEMREV probe battery on every card whose independent cold build has finished.
# Usage: run_probes.sh <task> [<task> ...]
set -u
REV=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-D13-cross-audit-ophis
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"

run_one() {
  local task="$1" name="$2" rel="$3"
  local dir="$REV/review/build/$task/release"
  [ -d "$dir" ] || { echo "$task $name SKIP no build"; return; }
  [ -f "$REV/review/probes/$task/$rel" ] || { echo "$task $name SKIP no probe"; return; }
  ( cd "$dir" && timeout 3600 lake env lean "$REV/review/probes/$task/$rel" \
      > "$REV/review/logs/$task-$name.log" 2>&1 )
  local rc=$?
  echo "$task $name exit=$rc $(grep -E 'VERDICT|USE_DONE' "$REV/review/logs/$task-$name.log" | tail -1)"
}

for task in "$@"; do
  sub="$REV/review/probes/$task"
  if [ -f "$sub/Census.lean" ]; then run_one "$task" census Census.lean; fi
  if [ -f "$sub/isolated/Census.lean" ]; then run_one "$task" census-isolated isolated/Census.lean; fi
  if [ -f "$sub/NegControl.lean" ]; then run_one "$task" negcontrol NegControl.lean; fi
  if [ -f "$sub/UseProbe.lean" ]; then run_one "$task" useprobe UseProbe.lean; fi
  if [ -f "$sub/Cited.lean" ]; then run_one "$task" cited Cited.lean; fi
done
echo PROBES_DONE
