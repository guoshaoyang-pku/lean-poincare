#!/bin/bash
# D13 thirteenth invocation: per-file gate and worktree gate.
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7
LOG=logs/d13_thirteenth_checkpoint
# per-file gate: the authored files (previous 26 + the 2 new ones)
FILES=$( { cat logs/d13_twelfth_final_perfile.txt | sed 's/^[0-9]*://'; \
           echo release/Poincare/D13/HeatKernelBridge/WeakHeatEquation.lean; \
           echo release/Poincare/D7/HeatKernel/WeakStatus.lean; } | sort -u )
: > ${LOG}_perfile.txt
for f in $FILES; do
  timeout 900 lake env lean "$f" > /dev/null 2>&1
  echo "$?:$f" >> ${LOG}_perfile.txt
done
# worktree gate: every .lean file outside .lake and third_party, from the worktree root
: > ${LOG}_gate_raw.txt
find . -name '*.lean' -not -path '*/.lake/*' -not -path './third_party/*' | sort | while read -r f; do
  timeout 900 lake env lean "$f" > /dev/null 2>&1
  echo "$?:$f" >> ${LOG}_gate_raw.txt
done
echo "DONE" >> ${LOG}_gate_raw.txt
