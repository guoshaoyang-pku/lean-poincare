#!/bin/bash
# Mutation tests for the round-5 fail-closed checkers.
#
# A checker that cannot fail proves nothing.  This script mutates copies (never
# the real artifacts) and asserts that each checker exits non-zero:
#   1. sorry-ledger.py --check        : dropped ledger entry must be detected
#   2. verify-release-mirror.py       : changed and missing mirror file must be detected
#   3. classify-release-forbidden-hits.py : an injected unclassified `sorry` must be detected
set -u
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L2-upstream-adapters
L1=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L1-lean-baseline
SNAP="$WT/third_party/frenzymath/Poincare-Conjecture"
LOG="$WT/evidence/logs/round5-mutation-tests.log"
# note: `mktemp -d` can fail in this sandbox (TMPDIR points outside the
# workspace); use a temp dir inside the worktree and fail loudly if it is not
# usable, so a mutation test can never "detect" a broken setup.
TMP="$WT/evidence/.mutation-tmp"
rm -rf "$TMP"; mkdir -p "$TMP" || exit 99
[ -w "$TMP" ] || { echo "temp dir not writable: $TMP"; exit 99; }
trap 'rm -rf "$TMP"' EXIT

{
  echo "=== round-5 checker mutation tests $(date -u +%FT%TZ) ==="
  echo "temp dir: $TMP"
  echo

  echo "--- 1a. sorry ledger: drop the last entry -> --check must exit 1 ---"
  python3 -c "
import json,sys
d=json.load(open('$WT/evidence/sorry-ledger.json'))
d['entries']=d['entries'][:-1]
json.dump(d,open('$TMP/bad-ledger.json','w'))
"
  python3 "$WT/evidence/sorry-ledger.py" --check "$SNAP" "$TMP/bad-ledger.json"
  rc=$?
  echo "MUTATION_1A_EXIT=$rc (expected non-zero)"
  [ "$rc" -ne 0 ] && echo "MUTATION_1A: DETECTED" || echo "MUTATION_1A: NOT DETECTED (FAIL)"

  echo
  echo "--- 1b. sorry ledger: unmutated ledger -> --check must exit 0 ---"
  python3 "$WT/evidence/sorry-ledger.py" --check "$SNAP" "$WT/evidence/sorry-ledger.json"
  rc=$?
  echo "MUTATION_1B_EXIT=$rc (expected 0)"
  [ "$rc" -eq 0 ] && echo "MUTATION_1B: CLEAN PASS" || echo "MUTATION_1B: UNEXPECTED FAILURE"

  echo
  echo "--- 2a. release mirror: one changed file -> check must exit 1 ---"
  rsync -a --exclude=.lake/ "$WT/release/" "$TMP/mirror/"
  echo "-- injected mutation --" >> "$TMP/mirror/ReleaseCheck.lean"
  python3 "$WT/evidence/verify-release-mirror.py" "$TMP/mirror" \
    "$L1/baseline/reconcile/source-hash-drift.json"
  rc=$?
  echo "MUTATION_2A_EXIT=$rc (expected non-zero)"
  [ "$rc" -ne 0 ] && echo "MUTATION_2A: DETECTED" || echo "MUTATION_2A: NOT DETECTED (FAIL)"

  echo
  echo "--- 2b. release mirror: one missing file -> check must exit 1 ---"
  rm "$TMP/mirror/ReleaseCheck.lean"
  python3 "$WT/evidence/verify-release-mirror.py" "$TMP/mirror" \
    "$L1/baseline/reconcile/source-hash-drift.json"
  rc=$?
  echo "MUTATION_2B_EXIT=$rc (expected non-zero)"
  [ "$rc" -ne 0 ] && echo "MUTATION_2B: DETECTED" || echo "MUTATION_2B: NOT DETECTED (FAIL)"

  echo
  echo "--- 2c. unmutated mirror -> check must exit 0 ---"
  python3 "$WT/evidence/verify-release-mirror.py" "$WT/release" \
    "$L1/baseline/reconcile/source-hash-drift.json"
  rc=$?
  echo "MUTATION_2C_EXIT=$rc (expected 0)"
  [ "$rc" -eq 0 ] && echo "MUTATION_2C: CLEAN PASS" || echo "MUTATION_2C: UNEXPECTED FAILURE"

  echo
  echo "--- 3a. release forbidden scan: injected `sorry` -> classification must exit 1 ---"
  rsync -a --exclude=.lake/ "$WT/release/" "$TMP/forbidden/"
  printf '\ntheorem injectedMutation : True := by sorry\n' >> "$TMP/forbidden/ReleaseCheck.lean"
  python3 "$WT/evidence/classify-release-forbidden-hits.py" "$TMP/forbidden"
  rc=$?
  echo "MUTATION_3A_EXIT=$rc (expected non-zero)"
  [ "$rc" -ne 0 ] && echo "MUTATION_3A: DETECTED" || echo "MUTATION_3A: NOT DETECTED (FAIL)"

  echo
  echo "--- 3b. unmutated release -> classification must exit 0 ---"
  python3 "$WT/evidence/classify-release-forbidden-hits.py" "$WT/release"
  rc=$?
  echo "MUTATION_3B_EXIT=$rc (expected 0)"
  [ "$rc" -eq 0 ] && echo "MUTATION_3B: CLEAN PASS" || echo "MUTATION_3B: UNEXPECTED FAILURE"

  echo
  echo "=== end $(date -u +%FT%TZ) ==="
} > "$LOG" 2>&1

cat "$LOG"
