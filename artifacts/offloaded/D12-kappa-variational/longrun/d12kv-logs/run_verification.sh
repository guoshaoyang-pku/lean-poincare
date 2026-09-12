#!/usr/bin/env bash
# Verification pipeline for D12-kappa-variational (run from the worktree root).
# Per-file compiles, axiom audit (fail-closed), forbidden-token scan, source hashes,
# full package build.
set -u
WORKTREE="$(pwd)"
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
LOGS="$WORKTREE/longrun/d12kv-logs"
mkdir -p "$LOGS"
cd "$WORKTREE/release"

FILES=(
  Poincare/D12/KappaVariational/GaussianNormalization.lean
  Poincare/D12/KappaVariational/CurvatureEnergy.lean
  Poincare/D12/KappaVariational/Transfer.lean
  Poincare/D12/KappaVariational/Statements.lean
  Poincare/D12/KappaVariational/All.lean
  Poincare/D12/KappaVariational/Audit.lean
)

: > "$LOGS/exit_codes.txt"
for f in "${FILES[@]}"; do
  tag="$(echo "$f" | tr '/' '_')"
  timeout 1800 lake env lean "$f" > "$LOGS/lean_${tag}.out" 2> "$LOGS/lean_${tag}.err"
  code=$?
  echo "$code $f" >> "$LOGS/exit_codes.txt"
done
echo "--- exit codes ---"
cat "$LOGS/exit_codes.txt"

# Axiom audit (fail-closed) on the Audit.lean output
python3 "$LOGS/audit_axioms.py" \
  "$LOGS/lean_Poincare_D12_KappaVariational_Audit.lean.out" \
  "$LOGS/axioms.json"
AUDIT=$?
echo "audit exit: $AUDIT"

# Forbidden-token scan (comment/string-aware)
if [ -f "$WORKTREE/input/d5-tools/scan_forbidden.py" ]; then
  python3 "$WORKTREE/input/d5-tools/scan_forbidden.py" Poincare/D12/KappaVariational > "$LOGS/forbidden_scan.txt" 2>&1
  SCAN=$?
  echo "forbidden scan exit: $SCAN"
  tail -3 "$LOGS/forbidden_scan.txt"
else
  echo "scan_forbidden.py not found; running grep fallback"
  grep -nE "sorry|axiom|admit|unsafe|native_decide|proof_wanted" \
    Poincare/D12/KappaVariational/*.lean > "$LOGS/forbidden_grep_fallback.txt" || true
  wc -l "$LOGS/forbidden_grep_fallback.txt"
fi

# Source hashes
sha256sum Poincare/D12/KappaVariational/*.lean > "$LOGS/source_hashes.txt"
cat "$LOGS/source_hashes.txt"

# Full package build
timeout 3600 lake build > "$LOGS/lake_build.log" 2>&1
echo "lake build exit: $?" | tee "$LOGS/lake_build_exit.txt"
tail -2 "$LOGS/lake_build.log"
