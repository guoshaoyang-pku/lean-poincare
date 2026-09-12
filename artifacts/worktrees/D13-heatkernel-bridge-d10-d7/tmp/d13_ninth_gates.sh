#!/usr/bin/env bash
# D13-heatkernel-bridge-d10-d7: eighth-invocation gate suite.
# Usage: bash tmp/d13_ninth_gates.sh <prefix>   e.g. d13_eighth_checkpoint
set -u
PREFIX="${1:?usage: d13_ninth_gates.sh <prefix>}"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-heatkernel-bridge-d10-d7
cd "$WT"
SUM=logs/${PREFIX}_summary.txt
: > "$SUM"
L=logs/${PREFIX}

echo "== source hashes =="
sha256sum release/Poincare/D13/HeatKernelBridge/*.lean \
  release/Poincare/D7/HeatKernel/V1Interface.lean \
  release/Poincare/D7/HeatKernel/FiniteStatus.lean \
  release/Poincare/D7/HeatKernel/StatementStatus.lean \
  release/Poincare/D7/HeatKernel/RepairStatus.lean \
  release/Poincare/D7/HeatKernel/DataStatus.lean \
  release/Poincare/D7/ConjugateHeat/Status.lean \
  lakefile.toml lake-manifest.json lean-toolchain > ${L}_hashes.txt 2>&1
echo "hashes_recorded=$(wc -l < ${L}_hashes.txt)" >> "$SUM"

echo "== semantic check transcripts =="
{
  for f in tmp/d13_semantic_checks_*.lean; do
    echo "### $f"
    lake env lean "$f"
    echo "exit=$?"
  done
} > ${L}_semantic_checks.out 2>&1
echo "semantic_checks_exit=$?" >> "$SUM"
echo "semantic_files=$(grep -c '^### ' ${L}_semantic_checks.out)" >> "$SUM"
echo "semantic_failures=$(grep -c '^exit=[^0]' ${L}_semantic_checks.out)" >> "$SUM"

echo "== full build (release/) =="
( cd release && lake build ) > ${L}_build.log 2>&1
BE=$?
echo "build_exit=$BE" >> "$SUM"
tail -3 ${L}_build.log >> "$SUM"
echo "axiom_pass_lines=$(grep -c 'D13HeatKernelBridgeAxiomCheck: PASS' ${L}_build.log)" >> "$SUM"
grep 'D13HeatKernelBridgeAxiomCheck' ${L}_build.log | tail -1 >> "$SUM"

echo "== per-file gate (authored files) =="
: > ${L}_perfile.txt
for f in release/Poincare/D13/HeatKernelBridge/Basic.lean \
         release/Poincare/D13/HeatKernelBridge/EuclideanTransport.lean \
         release/Poincare/D13/HeatKernelBridge/CompactUpgrade.lean \
         release/Poincare/D13/HeatKernelBridge/All.lean \
         release/Poincare/D13/HeatKernelBridge/PredicateSemantics.lean \
         release/Poincare/D13/HeatKernelBridge/PDERepair.lean \
         release/Poincare/D13/HeatKernelBridge/StatementRefutation.lean \
         release/Poincare/D13/HeatKernelBridge/GeometricRepair.lean \
         release/Poincare/D13/HeatKernelBridge/LaplacianSymmetryRefutation.lean \
         release/Poincare/D13/HeatKernelBridge/DataRefutation.lean \
         release/Poincare/D13/HeatKernelBridge/ConjugateHeatBridge.lean \
         release/Poincare/D13/HeatKernelBridge/AxiomAudit.lean \
         release/Poincare/D13/HeatKernelBridge/FiniteSpaceHeat.lean \
         release/Poincare/D7/HeatKernel/FiniteStatus.lean \
         release/Poincare/D7/HeatKernel/V1Interface.lean \
         release/Poincare/D7/HeatKernel/StatementStatus.lean \
         release/Poincare/D7/HeatKernel/RepairStatus.lean \
         release/Poincare/D7/HeatKernel/DataStatus.lean \
         release/Poincare/D7/ConjugateHeat/Status.lean; do
  if [ -f "$f" ]; then
    timeout 1800 lake env lean "$f" > /dev/null 2>&1
    echo "$?:$f" >> ${L}_perfile.txt
  fi
done
echo "perfile_total=$(wc -l < ${L}_perfile.txt) perfile_failures=$(grep -cv '^0:' ${L}_perfile.txt)" >> "$SUM"

echo "== worktree gate =="
find . -name '*.lean' -not -path './.lake/*' -not -path './.git/*' -not -path './.dshpkg/*' \
  -not -path './third_party/*' -print0 | xargs -0 -n1 -P8 \
  sh -c 'timeout 1800 lake env lean "$0" > /dev/null 2>&1; echo "$?:$0"' > ${L}_gate_raw.txt
echo "worktree_total=$(wc -l < ${L}_gate_raw.txt) failures=$(grep -cv '^0:' ${L}_gate_raw.txt)" >> "$SUM"

echo "== forbidden scan =="
python3 input/d5-tools/scan_forbidden.py release/Poincare/D13/HeatKernelBridge > ${L}_forbidden_d13.json 2>&1
echo "forbidden_d13_exit=$?" >> "$SUM"
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/HeatKernel > ${L}_forbidden_d7.json 2>&1
echo "forbidden_d7_exit=$?" >> "$SUM"
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/ConjugateHeat > ${L}_forbidden_conj.json 2>&1
echo "forbidden_conj_exit=$?" >> "$SUM"

echo "== negative control =="
lake env lean negcontrol/NegativeControl.lean > ${L}_negcontrol.out 2>&1
echo "negcontrol_exit=$?" >> "$SUM"

echo "== source integrity (diff vs D12-heat-domain-repair) =="
diff -rq release/Poincare /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D12-heat-domain-repair/release/Poincare > ${L}_diff.txt 2>&1
echo "diff_exit=$? diff_lines=$(wc -l < ${L}_diff.txt)" >> "$SUM"

echo "== upstream snapshot verification =="
python3 tmp/verify_frenzymath_snapshot.py > ${L}_upstream.out 2>&1
echo "upstream_exit=$?" >> "$SUM"

echo "ALL GATES DONE ($PREFIX)"
