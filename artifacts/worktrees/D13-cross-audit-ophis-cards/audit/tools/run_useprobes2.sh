#!/usr/bin/env bash
set -u
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
for t in "$@"; do
  cd "$WT/audit/build/$t/release" || { echo "NO BUILD $t"; continue; }
  timeout 1800 lake env lean "../../../probes/$t/UseProbe.lean" > "$WT/audit/logs/$t-use-probe.log" 2>&1
  echo "$t use-probe exit=$?"
done
echo USEPROBES_DONE
