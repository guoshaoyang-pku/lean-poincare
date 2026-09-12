#!/usr/bin/env bash
# SEMREV-L3 round-4 re-verification runner (reviewer instrumentation, not part of the artifact).
# Runs every load-bearing check from a fresh from-source rebuild and records exit codes.
set -u
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
REVIEW="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REVIEW/release" || exit 1
E="$REVIEW/evidence"
: > "$E/r4-runner-summary.txt"

run() { # name expected_exit cmd...
  local name="$1" expect="$2"; shift 2
  local t0 t1 rc
  t0=$(date +%s)
  "$@" > "$E/r4-$name.log" 2>&1
  rc=$?
  t1=$(date +%s)
  printf '%-24s exit=%s expected=%s seconds=%s\n' "$name" "$rc" "$expect" "$((t1-t0))" | tee -a "$E/r4-runner-summary.txt"
  if [ "$expect" != "any" ] && [ "$rc" != "$expect" ]; then
    echo "UNEXPECTED-EXIT $name (got $rc, wanted $expect)" | tee -a "$E/r4-runner-summary.txt"
  fi
}

# --- independent Lean probes against the reviewed package ---
run semrev-audit 0 lake env lean ../probe/SemrevAudit.lean
run semrev-census 0 lake env lean ../probe/SemrevCensus.lean
run domains 0 lake env lean ../probe/SemrevDomains.lean
run semantics 0 lake env lean ../probe/SemrevSemantics.lean
run audit-complete 0 lake env lean ../probe/SemrevAuditComplete.lean
run banach 0 lake env lean ../probe/SemrevBanach.lean
run stageA3 0 lake env lean ../probe/SemrevStageA3.lean
run valdiag 0 lake env lean ../probe/SemrevValDiag3.lean
run synthfail 1 lake env lean ../probe/SemrevSynthFail.lean
run negcontrol-parent 1 lake env lean ../negcontrol/L3NegControl.lean
run negcontrol-reviewer 1 lake env lean ../negcontrol/SemrevNegControl.lean
run consumers 0 lake env lean ../probe/SemrevConsumers.lean
run inhabitants 0 lake env lean ../probe/SemrevInhabitants.lean

# --- per-file gate on the six authored files ---
: > "$E/r4-perfile-gate.log"
for f in Basic UniformBridge ClassicalBridge BanachDeriv Audit All; do
  t0=$(date +%s)
  if lake env lean "Poincare/L3/HeatTimeDeriv/$f.lean" >> "$E/r4-perfile-gate.log" 2>&1; then
    echo "OK Poincare/L3/HeatTimeDeriv/$f.lean" >> "$E/r4-perfile-gate.log"
  else
    echo "FAIL Poincare/L3/HeatTimeDeriv/$f.lean (exit $?)" >> "$E/r4-perfile-gate.log"
  fi
  t1=$(date +%s)
  printf 'perfile-%-16s seconds=%s\n' "$f" "$((t1-t0))" >> "$E/r4-runner-summary.txt"
done
if grep -q '^FAIL' "$E/r4-perfile-gate.log"; then
  echo "perfile-gate FAIL" | tee -a "$E/r4-runner-summary.txt"
else
  echo "perfile-gate PASS 6/6" | tee -a "$E/r4-runner-summary.txt"
fi

# --- independent forbidden-token scan (writes evidence/semrev-forbidden-scan.json) ---
cd "$REVIEW" || exit 1
t0=$(date +%s)
python3 tools/semrev_check.py > "$E/r4-forbidden-scan.log" 2>&1
rc=$?
t1=$(date +%s)
printf 'forbidden-scan exit=%s seconds=%s\n' "$rc" "$((t1-t0))" | tee -a "$E/r4-runner-summary.txt"
cp -f "$E/semrev-forbidden-scan.json" "$E/semrev-forbidden-scan.r4.json"

# --- replay parent's own 356-file per-file gate on the byte-identical staged copy ---
t0=$(date +%s)
python3 tools/l3_check_parent.py --only gate > "$E/r4-parent-perfile-gate.log" 2>&1
rc=$?
t1=$(date +%s)
printf 'parent-perfile-gate exit=%s seconds=%s\n' "$rc" "$((t1-t0))" | tee -a "$E/r4-runner-summary.txt"
cp -f "$REVIEW/audit-evidence/l3-check.json" "$REVIEW/audit-evidence/l3-check.r4.json"

echo "ROUND4-RUNNER-COMPLETE"
