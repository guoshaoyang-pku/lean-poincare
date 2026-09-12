#!/usr/bin/env bash
# L5-topology-audit — reproducible driver for the independent kernel audit.
# Usage: bash audit-evidence/tools/l5_run_audit.sh   (run from the worktree root)
# Writes logs + a machine-readable summary under audit-evidence/.
set -u
WT="$(cd "$(dirname "$0")/../.." && pwd)"
REL="$WT/release"
EV="$WT/audit-evidence"
PROBES="$EV/probes"
NEG="$EV/negcontrol"
LOGS="$EV/logs"
mkdir -p "$LOGS"

LP="$(cd "$REL" && lake env printenv LEAN_PATH):$PROBES:$NEG"
export LEAN_PATH="$LP"
SUMMARY="$EV/audit-summary.json"
: > "$LOGS/audit-steps.tsv"
step() { # name log exit
  printf '%s\t%s\t%s\n' "$1" "$2" "$3" >> "$LOGS/audit-steps.tsv"
}
# elan resolves the pinned toolchain from release/lean-toolchain, so keep cwd=release and
# use `-R` to declare the module root of the out-of-tree probe directories.
cd "$REL"

# 1. cross-module collision scan of the union release (ilean-based, exact)
python3 "$EV/tools/l5_module_conflicts.py" "$REL" "$EV/collisions.json" \
  > "$LOGS/collisions.log" 2>&1
step module_collisions "$LOGS/collisions.log" "$?"

# 2. detector oleans for the two collision-free passes (root = probes dir)
lean -R "$PROBES" -o "$PROBES/L5DetectorA.olean" "$PROBES/L5DetectorA.lean" \
  > "$LOGS/L5DetectorA-compile.log" 2>&1
step detectorA_compile "$LOGS/L5DetectorA-compile.log" "$?"
lean -R "$PROBES" -o "$PROBES/L5DetectorB.olean" "$PROBES/L5DetectorB.lean" \
  > "$LOGS/L5DetectorB-compile.log" 2>&1
step detectorB_compile "$LOGS/L5DetectorB-compile.log" "$?"

# 3. fresh negative-control module olean (declares the forbidden axiom; never in release/)
lean -R "$NEG" -o "$NEG/L5NegControlFresh.olean" "$NEG/L5NegControlFresh.lean" \
  > "$LOGS/L5NegControlFresh-compile.log" 2>&1
step fresh_negcontrol_compile "$LOGS/L5NegControlFresh-compile.log" "$?"

# 4. positive full-package audits (expected exit 0 each; A carries the lane annotations)
lean -R "$PROBES" "$PROBES/L5AuditPositiveA.lean" > "$LOGS/L5Audit-positiveA.log" 2>&1
step positive_pass_A "$LOGS/L5Audit-positiveA.log" "$?"
lean -R "$PROBES" "$PROBES/L5AuditPositiveB.lean" > "$LOGS/L5Audit-positiveB.log" 2>&1
step positive_pass_B "$LOGS/L5Audit-positiveB.log" "$?"

# 5. negative control A: fresh axiom (expected nonzero)
lean -R "$NEG" "$NEG/L5AuditNegativeFresh.lean" > "$LOGS/L5Audit-negative-fresh.log" 2>&1
step negative_fresh "$LOGS/L5Audit-negative-fresh.log" "$?"

# 6. negative control B: release's own negative-control module (expected nonzero)
lean -R "$NEG" "$NEG/L5AuditNegativeRelease.lean" > "$LOGS/L5Audit-negative-release.log" 2>&1
step negative_release "$LOGS/L5Audit-negative-release.log" "$?"

# 7. forbidden-token scan of every authored .lean file (comments/strings stripped)
python3 "$EV/tools/l5_forbidden_scan.py" "$REL" "$EV/forbidden-scan.json" \
  > "$LOGS/forbidden-scan.log" 2>&1
step forbidden_scan "$LOGS/forbidden-scan.log" "$?"

# 8. source hashes of every .lean file under release/ (excluding .lake)
( cd "$REL" && find . -name '*.lean' -not -path './.lake/*' -print0 \
  | sort -z | xargs -0 sha256sum ) > "$EV/source-hashes.txt" 2> "$LOGS/source-hashes.err"
step source_hashes "$EV/source-hashes.txt" "$?"

# 9. positive-log assertions (fail-closed post-processing of both audit logs)
python3 "$EV/tools/l5_check_audit_log.py" "$LOGS/L5Audit-positiveA.log" \
  "$LOGS/L5Audit-positiveB.log" "$EV/collisions.json" "$SUMMARY" \
  > "$LOGS/audit-assertions.log" 2>&1
step audit_assertions "$LOGS/audit-assertions.log" "$?"

echo "driver done; summary: $SUMMARY"
