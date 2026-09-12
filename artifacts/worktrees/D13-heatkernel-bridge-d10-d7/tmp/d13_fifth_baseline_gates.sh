#!/usr/bin/env bash
# D13-heatkernel-bridge-d10-d7: fifth-invocation BASELINE gate suite (frozen fourth-invocation artifact).
set -u
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7
cd "$WT"
SUM=logs/d13_fifth_baseline_summary.txt
: > "$SUM"

echo "== source hashes (baseline) =="
sha256sum release/Poincare/D13/HeatKernelBridge/*.lean release/Poincare/D7/HeatKernel/V1Interface.lean \
  lakefile.toml lake-manifest.json lean-toolchain > logs/d13_fifth_baseline_hashes.txt 2>&1
echo "hashes_recorded=$(wc -l < logs/d13_fifth_baseline_hashes.txt)" >> "$SUM"

echo "== full build (release/) =="
( cd release && lake build ) > logs/d13_fifth_baseline_build.log 2>&1
BE=$?
echo "build_exit=$BE" >> "$SUM"
tail -3 logs/d13_fifth_baseline_build.log >> "$SUM"
echo "axiom_pass_lines=$(grep -c 'D13HeatKernelBridgeAxiomCheck: PASS' logs/d13_fifth_baseline_build.log)" >> "$SUM"

echo "== per-file gate (authored files) =="
: > logs/d13_fifth_baseline_perfile.txt
for f in release/Poincare/D13/HeatKernelBridge/Basic.lean \
         release/Poincare/D13/HeatKernelBridge/EuclideanTransport.lean \
         release/Poincare/D13/HeatKernelBridge/CompactUpgrade.lean \
         release/Poincare/D13/HeatKernelBridge/All.lean \
         release/Poincare/D13/HeatKernelBridge/PredicateSemantics.lean \
         release/Poincare/D13/HeatKernelBridge/PDERepair.lean \
         release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean \
         release/Poincare/D7/HeatKernel/V1Interface.lean; do
  timeout 1800 lake env lean "$f" > /dev/null 2>&1
  echo "$?:$f" >> logs/d13_fifth_baseline_perfile.txt
done
echo "perfile_failures=$(grep -cv '^0:' logs/d13_fifth_baseline_perfile.txt)" >> "$SUM"

echo "== worktree gate =="
find . -name '*.lean' -not -path './.lake/*' -not -path './.git/*' -not -path './.dshpkg/*' \
  -not -path './third_party/*' -print0 | xargs -0 -n1 -P8 \
  sh -c 'timeout 1800 lake env lean "$0" > /dev/null 2>&1; echo "$?:$0"' > logs/d13_fifth_baseline_gate_raw.txt
echo "worktree_total=$(wc -l < logs/d13_fifth_baseline_gate_raw.txt) failures=$(grep -cv '^0:' logs/d13_fifth_baseline_gate_raw.txt)" >> "$SUM"

echo "== forbidden scan =="
python3 input/d5-tools/scan_forbidden.py release/Poincare/D13/HeatKernelBridge > logs/d13_fifth_baseline_forbidden_d13.json 2>&1
echo "forbidden_d13_exit=$?" >> "$SUM"
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/HeatKernel > logs/d13_fifth_baseline_forbidden_d7.json 2>&1
echo "forbidden_d7_exit=$?" >> "$SUM"

echo "== negative control =="
lake env lean negcontrol/NegativeControl.lean > logs/d13_fifth_baseline_negcontrol.out 2>&1
echo "negcontrol_exit=$?" >> "$SUM"

echo "== source integrity (diff vs D12-heat-domain-repair) =="
diff -rq release/Poincare /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-heat-domain-repair/release/Poincare > logs/d13_fifth_baseline_diff.txt 2>&1
echo "diff_exit=$? diff_lines=$(wc -l < logs/d13_fifth_baseline_diff.txt)" >> "$SUM"

echo "== upstream snapshot verification =="
python3 tmp/verify_frenzymath_snapshot.py > logs/d13_fifth_baseline_upstream.out 2>&1
echo "upstream_exit=$?" >> "$SUM"

echo "ALL FIFTH BASELINE GATES DONE"
