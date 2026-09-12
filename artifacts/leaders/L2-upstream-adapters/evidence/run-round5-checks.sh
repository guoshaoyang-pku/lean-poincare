#!/bin/bash
# Round-5 consolidated verification chain for L2-upstream-adapters.
#
# Runs every fail-closed check of the M2 artifact and the release mirror and
# writes one log.  The release build itself is not re-run here (it takes ~10
# minutes); its completed log is checked for the success marker instead.
set -u
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L2-upstream-adapters
L1=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline
LOG="$WT/evidence/logs/round5-final-verify.log"
SNAP="$WT/third_party/frenzymath/Poincare-Conjecture"

{
  echo "### round-5 verification chain $(date -u +%FT%TZ)"
  echo
  echo "--- [1] adapter build + fail-closed axiom audit + coverage ---"
  bash "$WT/evidence/run-axiom-audit.sh"
  echo "AXIOM_SCRIPT_EXIT=$?"
  echo
  echo "--- [2] authored-file check (adapter contract: 0 forbidden tokens) ---"
  python3 "$WT/evidence/check-authored-files.py" "$WT"
  echo "AUTHORED_EXIT=$?"
  echo
  echo "--- [3] novelty check (no public upstream duplicate) ---"
  python3 "$WT/evidence/check-novelty.py" "$WT"
  echo "NOVELTY_EXIT=$?"
  echo
  echo "--- [4] snapshot source hashes (sources untouched) ---"
  python3 "$WT/evidence/source-hashes.py" "$WT" "$WT/evidence/source-hashes.json"
  echo "SOURCE_HASH_EXIT=$?"
  echo
  echo "--- [5] snapshot integrity ---"
  python3 "$WT/evidence/verify_frenzymath_snapshot.py"
  echo "SNAPSHOT_EXIT=$?"
  echo
  echo "--- [6] sorry ledger (generate + idempotence + quarantine) ---"
  python3 "$WT/evidence/sorry-ledger.py" "$SNAP" "$WT/evidence/sorry-ledger.json" "$WT/evidence/sorry-ledger.md"
  echo "LEDGER_EXIT=$?"
  python3 "$WT/evidence/sorry-ledger.py" --check "$SNAP" "$WT/evidence/sorry-ledger.json"
  echo "LEDGER_CHECK_EXIT=$?"
  python3 "$WT/evidence/sorry-ledger.py" --quarantine "$WT/adapters" "$WT/evidence/sorry-ledger.json"
  echo "QUARANTINE_EXIT=$?"
  echo
  echo "--- [7] release mirror is byte-identical to the L1 integrator manifest ---"
  python3 "$WT/evidence/verify-release-mirror.py" "$WT/release" \
    "$L1/baseline/reconcile/source-hash-drift.json" "$WT/evidence/release-mirror-hashes.json"
  echo "MIRROR_EXIT=$?"
  echo
  echo "--- [8] release mirror forbidden-token classification ---"
  python3 "$WT/evidence/classify-release-forbidden-hits.py" "$WT/release" \
    "$WT/evidence/release-forbidden-classification.json"
  echo "RELEASE_FORBIDDEN_EXIT=$?"
  echo
  echo "--- [9] release build result (recorded, release pin v4.34.0-rc2 / mathlib 7974e751) ---"
  grep -E "Build completed successfully|RELEASE_BUILD_EXIT" "$WT/evidence/logs/round5-release-build.log"
  grep -c "declaration uses 'sorry'" "$WT/evidence/logs/round5-release-build.log" | sed 's/^/release_sorry_warnings=/'
  grep -E "D13FULLVERDICT|D6AUDIT\tVERDICT|D5ReleaseAudit: PASS" "$WT/evidence/logs/round5-release-build.log" | tail -3
  echo
  echo "### end $(date -u +%FT%TZ)"
} 2>&1 | tee "$LOG"
