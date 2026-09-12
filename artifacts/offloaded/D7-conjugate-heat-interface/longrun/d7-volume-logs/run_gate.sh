#!/usr/bin/env bash
# Replicate the harness compile gate: `lake env lean <abs file>` from the worktree root
# for every .lean file, skipping .lake/.git/.dshpkg.
set -u
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
ROOT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-orientability-volume-form
cd "$ROOT"
: > longrun/d7-volume-logs/gate_exit_codes.txt
fail=0
while IFS= read -r f; do
  timeout 1800 lake env lean "$f" > /dev/null 2>&1
  rc=$?
  echo "$f $rc" >> longrun/d7-volume-logs/gate_exit_codes.txt
  if [ "$rc" -ne 0 ]; then fail=$((fail+1)); fi
done < <(find . -name '*.lean' -not -path './.lake/*' -not -path './release/.lake/*' -not -path './.git/*' -not -path './.dshpkg/*' | sort)
echo "total=$(wc -l < longrun/d7-volume-logs/gate_exit_codes.txt) failed=$fail"
