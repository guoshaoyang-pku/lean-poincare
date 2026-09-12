#!/usr/bin/env bash
# D13 integrated kernel audit — final fresh rebuild + full audit replay.
# Runs with cwd = worktree root.  Every command's cwd and exit code is recorded.
set -u
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit
LOGS=$WT/audit-evidence/logs
cd "$WT/release" || exit 99

echo "=== cwd: $(pwd)"
echo "=== toolchain: $(cat lean-toolchain)"
echo "=== mathlib rev: $(python3 -c "import json;print(json.load(open('lake-manifest.json'))['packages'][0]['rev'])")"

# ---- fresh project build directory ------------------------------------------------
if [ -d .lake/build ]; then mv .lake/build .lake/build.pre-d13-final; fi
echo "=== fresh build dir: $(ls -d .lake/build 2>/dev/null || echo 'none (will be created)')"

run() {
  local name="$1"; shift
  local log="$LOGS/$name.log"
  echo "--- CMD[$name] cwd=$(pwd) :: $*" | tee -a "$LOGS/transcript.txt"
  "$@" >"$log" 2>&1
  local rc=$?
  echo "--- EXIT[$name]=$rc" | tee -a "$LOGS/transcript.txt"
  return $rc
}

: > "$LOGS/transcript.txt"
run 10-full-build lake build
run 11-kernel-audit lake env lean Poincare/D13/IntegratedAudit/KernelAudit.lean
run 12-statement-audit lake env lean Poincare/D13/IntegratedAudit/StatementAudit.lean
run 13-usage-probe lake env lean Poincare/D13/IntegratedAudit/UsageProbe.lean
run 14-dependency-probe lake env lean Poincare/D13/IntegratedAudit/DependencyProbe.lean
run 15-nonvacuity-probe lake env lean Poincare/D13/IntegratedAudit/NonvacuityProbe.lean
run 16-self-audit lake build Poincare.D13.IntegratedAudit.SelfAudit
run 16b-full-audit lake env lean Poincare/D13/IntegratedAudit/FullAudit.lean
# negative control: EXPECTED TO FAIL (nonzero exit is the pass condition)
run 17-negcontrol-included lake env lean ../audit-evidence/negcontrol/NegativeControlIncluded.lean
echo "--- NOTE: 17 is expected nonzero; the driver asserts it" | tee -a "$LOGS/transcript.txt"
# literal #print axioms for every new declaration (regenerated from the fresh inventory)
python3 "$WT/audit-evidence/tools/make_print_axioms_probes.py"
for i in 0 1 2 3; do
  run "18-print-axioms-$i" lake env lean "../audit-evidence/probes/PrintAxiomsAll$i.lean"
done
echo "=== done"
