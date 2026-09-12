#!/bin/bash
# Compile the adapter package and run the fail-closed axiom audit.
#
#   1. lake build UpstreamAdapters UpstreamAdaptersPetersen   -> axiom-audit-build.log
#   2. lake env lean <lib>/Audit.lean                          -> axiom-audit.log
#   3. check-axioms.py          (cones within the allowed set, fail closed)
#   4. check-audit-coverage.py  (authored == audited == logged, fail closed)
#
# The build log is kept separate because Lake replays upstream `#print axioms`
# info lines whose axioms the adapter is not responsible for; the audited file
# must contain only this package's own audit records.
#
# Exit code is non-zero if any build step, audit run, cone check or coverage
# check fails.
set -u
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L2-upstream-adapters
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_CACHE_DIR="$WT/evidence/mathlib-cache"
LOG="$WT/evidence/logs"
cd "$WT/adapters" || exit 90
{
  echo "=== $(date -u +%FT%TZ) lake build UpstreamAdapters ==="
  lake build UpstreamAdapters
  echo "BUILD_EXIT=$?"
  echo "=== $(date -u +%FT%TZ) lake build UpstreamAdaptersPetersen ==="
  lake build UpstreamAdaptersPetersen
  echo "PETERSEN_BUILD_EXIT=$?"
} > "$LOG/axiom-audit-build.log" 2>&1
{
  echo "=== $(date -u +%FT%TZ) lake env lean UpstreamAdapters/Audit.lean ==="
  lake env lean UpstreamAdapters/Audit.lean
  echo "AUDIT_LEAN_EXIT=$?"
  echo "=== $(date -u +%FT%TZ) lake env lean UpstreamAdaptersPetersen/Audit.lean ==="
  lake env lean UpstreamAdaptersPetersen/Audit.lean
  echo "PETERSEN_AUDIT_LEAN_EXIT=$?"
} > "$LOG/axiom-audit.log" 2>&1
grep -E 'EXIT=' "$LOG/axiom-audit-build.log" "$LOG/axiom-audit.log"

rc=0
for step in BUILD_EXIT PETERSEN_BUILD_EXIT AUDIT_LEAN_EXIT PETERSEN_AUDIT_LEAN_EXIT; do
  if ! grep -q "^${step}=0$" "$LOG/axiom-audit-build.log" "$LOG/axiom-audit.log"; then
    echo "STEP FAILED: ${step} is not 0"
    rc=1
  fi
done
if [ "$rc" -ne 0 ]; then echo "AXIOM AUDIT ABORTED: build/run step failed"; exit 1; fi

python3 "$WT/evidence/check-axioms.py" "$LOG/axiom-audit.log"
check=$?
echo "CHECK_EXIT=$check"

python3 "$WT/evidence/check-audit-coverage.py" "$WT" "$LOG/axiom-audit.log"
cov=$?
echo "COVERAGE_EXIT=$cov"

if [ "$check" -ne 0 ] || [ "$cov" -ne 0 ]; then
  echo "AXIOM AUDIT FAILED (fail-closed)"
  exit 1
fi
echo "AXIOM AUDIT AND COVERAGE PASSED"
exit 0
