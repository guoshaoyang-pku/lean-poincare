#!/bin/bash
# D13 thirteenth invocation: final per-file gate + semantic transcripts.
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7
# per-file gate: the authored files (previous 28 + WeakFinite.lean)
FILES=$( { awk -F: '{print $2}' logs/d13_thirteenth_checkpoint_perfile.txt; \
           echo release/Poincare/D13/HeatKernelBridge/WeakFinite.lean; } | sort -u )
: > logs/d13_thirteenth_final_perfile.txt
for f in $FILES; do
  timeout 900 lake env lean "$f" > /dev/null 2>&1
  echo "$?:$f" >> logs/d13_thirteenth_final_perfile.txt
done
# semantic transcripts
: > logs/d13_thirteenth_final_semantic_all.out
for f in tmp/d13_semantic_checks_a_predicate.lean tmp/d13_semantic_checks_b_pde.lean \
         tmp/d13_semantic_checks_c_refutation.lean tmp/d13_semantic_checks_d_geometric.lean \
         tmp/d13_semantic_checks_e_d7_repair.lean tmp/d13_semantic_checks_f_symmetry.lean \
         tmp/d13_semantic_checks_g_datarefutation.lean tmp/d13_semantic_checks_h_conjugate.lean \
         tmp/d13_semantic_checks_i_finite.lean tmp/d13_semantic_checks_j_uniqueness.lean \
         tmp/d13_semantic_checks_k_conjugate_uniqueness.lean tmp/d13_semantic_checks_l_scalar_curvature.lean \
         tmp/d13_semantic_checks_m_ergodicity.lean tmp/d13_semantic_checks_n_weak.lean; do
  timeout 900 lake env lean "$f" > /tmp/sem_final.out 2>&1
  echo "$?:$f" >> logs/d13_thirteenth_final_semantic_all.out
done
echo ALLDONE >> logs/d13_thirteenth_final_semantic_all.out
