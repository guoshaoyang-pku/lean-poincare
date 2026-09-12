#!/usr/bin/env bash
# Reproduce the D7-perelman-conditional-monotonicity verification transcript.
set -u
ROOT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-perelman-conditional-monotonicity
cd "$ROOT"
LOGS=longrun/d7pcm-logs
mkdir -p "$LOGS"

FILES="BochnerCertificate BochnerGradientEstimate ConjugateHeatCertificate ReducedVolumeInput FMonotonicity WMuMonotonicity Nonvacuity Blockers All"

: > "$LOGS/exit_codes.txt"
for f in $FILES; do
  lake env lean "release/Poincare/D7/Monotonicity/$f.lean" > "$LOGS/lean_$f.out" 2> "$LOGS/lean_$f.err"
  code=$?
  echo "$f $code" >> "$LOGS/exit_codes.txt"
done

# #print axioms output (All.lean contains the full audit)
cp "$LOGS/lean_All.out" "$LOGS/axioms-print.out"

# forbidden-token scan
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Monotonicity \
  > "$LOGS/forbidden-scan.json" 2> "$LOGS/forbidden-scan.err"

# full package build
( cd release && lake build ) > "$LOGS/lake_build.log" 2>&1
echo "lake_build $?" >> "$LOGS/exit_codes.txt"

cat "$LOGS/exit_codes.txt"
