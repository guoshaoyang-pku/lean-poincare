#!/usr/bin/env bash
# SEMREV-L5 repair attempt 2: fresh re-verification of every round-1 reviewer probe.
# Read-only with respect to the release package; writes only under review/logs/.
set -u
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-L5-topology-audit
cd "$WT" || exit 1
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
LEANBIN="$ELAN_HOME/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean"
export LEAN_PATH="$(cat review/evidence/leanpath.txt)"
LOG=review/logs

run() { # run <logname> <cmd...>
  local name="$1"; shift
  "$@" > "$LOG/$name" 2>&1
  echo "EXIT $? $name"
}

run SemRevTypes-repair2.log    "$LEANBIN" -R review review/probes/SemRevTypes.lean
run SemRevAxioms-repair2.log   "$LEANBIN" -R review review/probes/SemRevAxioms.lean
run SemRevShapes-repair2.log   "$LEANBIN" -R review review/probes/SemRevShapes.lean
run SemRevInhabitants-repair2.log "$LEANBIN" -R review review/probes/SemRevInhabitants.lean
run PassA-repair2.log          "$LEANBIN" -R review review/probes/PassA.lean
run PassB-repair2.log          "$LEANBIN" -R review review/probes/PassB.lean
L5=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L5-topology-audit
run L5A3Screen-repair2.log     "$LEANBIN" -R "$L5/release" "$L5/audit-evidence/probes/L5A3Screen.lean"

# fail-closed negative control: expects a NON-zero exit and four named violations
LEAN_PATH=review/negcontrol "$LEANBIN" review/probes/SemRevNegControlAudit.lean \
  > "$LOG/SemRevNegControl-repair2.log" 2>&1
echo "EXIT $? SemRevNegControl-repair2.log (expected non-zero)"

python3 review/tools/forbidden_scan.py > "$LOG/forbidden-replay-repair2.log" 2>&1
echo "EXIT $? forbidden-replay-repair2.log"
python3 review/tools/hash_replay.py > "$LOG/hash-replay-repair2.log" 2>&1
echo "EXIT $? hash-replay-repair2.log"
echo ALL_DONE
