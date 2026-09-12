#!/bin/bash
# D13 thirteenth invocation: worktree-wide gate, 4-way parallel, worktree-root cwd.
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7
find . -name '*.lean' -not -path '*/.lake/*' -not -path './third_party/*' | sort > /tmp/d13_wt_files.txt
cat /tmp/d13_wt_files.txt | xargs -P 4 -I{} bash -c 'timeout 900 lake env lean "{}" > /dev/null 2>&1; echo "$?:{}"' > logs/d13_thirteenth_checkpoint_gate_raw.txt
echo DONE >> logs/d13_thirteenth_checkpoint_gate_raw.txt
