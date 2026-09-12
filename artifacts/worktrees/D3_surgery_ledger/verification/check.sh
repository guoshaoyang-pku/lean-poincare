#!/usr/bin/env bash
# Reproduce the D3-surgery-ledger verification.
#
# Usage:  bash verification/check.sh
# Exit code 0 means: every Lean file elaborates and the axiom ledger contains no `sorryAx`.
set -u

WORKTREE="/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_surgery_ledger"
ELAN="/data3/guoshaoyang/workdir/lean_poincare/elan"

cd "$WORKTREE" || exit 1
export PATH="$ELAN/bin:$PATH"
export ELAN_HOME="$ELAN"

FILES=(
  Poincare/Longrun/Surgery/Basic.lean
  Poincare/Longrun/Surgery/Chain.lean
  Poincare/Longrun/Surgery/Toy.lean
  Poincare/Longrun/Surgery/Missing.lean
  Poincare/Longrun/Surgery.lean
  Poincare/Longrun/Surgery/Axioms.lean
)

: > verification/compile.log
overall=0
for f in "${FILES[@]}"; do
  {
    echo "===== lake env lean $f ====="
  } >> verification/compile.log
  lake env lean "$f" >> verification/compile.log 2>&1
  rc=$?
  echo "exit code: $rc" >> verification/compile.log
  echo "$f exit=$rc"
  [ "$rc" -eq 0 ] || overall=1
done

lake env lean Poincare/Longrun/Surgery/Axioms.lean > verification/axioms.log 2>&1
rc=$?
echo "axioms exit=$rc"
[ "$rc" -eq 0 ] || overall=1

if grep -q "sorryAx" verification/axioms.log; then
  echo "FAIL: sorryAx found in the axiom ledger"
  overall=1
else
  echo "OK: no sorryAx in the axiom ledger"
fi

# Only Lean's standard axioms may appear.
if grep -vE "does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]" \
    verification/axioms.log | grep -q .; then
  echo "FAIL: unexpected axiom report line"
  grep -vE "does not depend on any axioms|depends on axioms: \[(propext|Classical\.choice|Quot\.sound)(, (propext|Classical\.choice|Quot\.sound))*\]" \
    verification/axioms.log
  overall=1
else
  echo "OK: every report line uses only standard Lean axioms"
fi

exit "$overall"
