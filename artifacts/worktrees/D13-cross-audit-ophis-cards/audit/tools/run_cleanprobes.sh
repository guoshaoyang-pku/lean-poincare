#!/usr/bin/env bash
set -u
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
for t in "$@"; do
  cd "$WT/audit/build/$t/release" || { echo "NO BUILD $t"; continue; }
  timeout 3600 lake env lean "../../../probes/$t/CleanProbe.lean" > "$WT/audit/logs/$t-clean-probe.log" 2>&1
  rc=$?
  echo "$t clean-probe exit=$rc $(grep -c '^D13XDECL' "$WT/audit/logs/$t-clean-probe.log") decls $(grep 'VERDICT' "$WT/audit/logs/$t-clean-probe.log" | tail -1)"
done
echo CLEANPROBES_DONE
