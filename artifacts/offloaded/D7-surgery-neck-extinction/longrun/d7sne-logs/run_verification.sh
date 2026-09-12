#!/usr/bin/env bash
# Reproduce the D7-surgery-neck-extinction verification transcript.
#
# Usage:  bash longrun/d7sne-logs/run_verification.sh
#
# Steps:
#   1. full release package build (produces the oleans consumed by the per-file gate)
#   2. per-file `lake env lean` compile of every authored file (exit 0 required)
#   3. comment/string-aware forbidden-token scan of the authored sources
#   4. `#print axioms` capture (Audit.lean) and cone summary
#   5. source-integrity check against the scaffold worktree
set -u
ROOT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-surgery-neck-extinction
cd "$ROOT"
LOGS=longrun/d7sne-logs
mkdir -p "$LOGS"

export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"

FILES="Basic Times Extinction Statements All Probe Audit"

# 1. full package build
( cd release && lake build ) > "$LOGS/lake_build.log" 2>&1
echo "lake_build $?" > "$LOGS/exit_codes.txt"

# 2. per-file compile gate
for f in $FILES; do
  lake env lean "release/Poincare/D7/SurgeryFlow/$f.lean" \
    > "$LOGS/lean_$f.out" 2> "$LOGS/lean_$f.err"
  code=$?
  echo "$f $code" >> "$LOGS/exit_codes.txt"
done

# 3. forbidden-token scan
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/SurgeryFlow \
  > "$LOGS/forbidden-scan.json" 2> "$LOGS/forbidden-scan.err"

# 4. axiom audit (Audit.lean contains the full #print axioms list)
cp "$LOGS/lean_Audit.out" "$LOGS/axioms-print.out"
python3 "$LOGS/parse_axioms.py" > "$LOGS/axioms.json" 2> "$LOGS/axioms.err"

# 5. source integrity
python3 "$LOGS/source_integrity.py" > "$LOGS/source-integrity.json" \
  2> "$LOGS/source-integrity.err"

cat "$LOGS/exit_codes.txt"
