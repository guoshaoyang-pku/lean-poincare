#!/usr/bin/env bash
# D7-reduced-length-volume verification transcript.
# Run from the worktree root:
#   bash longrun/d7rlv-logs/run_verification.sh
set -u

export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LOGS="$ROOT/longrun/d7rlv-logs"
mkdir -p "$LOGS"
cd "$ROOT"

FILES=(
  release/Poincare/D7/Reduced/Basic.lean
  release/Poincare/D7/Reduced/Certificate.lean
  release/Poincare/D7/Reduced/Statements.lean
  release/Poincare/D7/Reduced/Gaussian.lean
  release/Poincare/D7/Reduced/Probe.lean
  release/Poincare/D7/Reduced/Audit.lean
  release/Poincare/D7/Reduced/All.lean
)

: > "$LOGS/exit_codes.txt"
for f in "${FILES[@]}"; do
  log="$LOGS/lean_$(echo "$f" | tr '/' '_').log"
  lake env lean "$f" > "$log" 2>&1
  code=$?
  echo "$code $f" >> "$LOGS/exit_codes.txt"
  echo "exit=$code $f"
done

# Forbidden-token scan (comment/string aware) over the authored sources.
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/Reduced \
  > "$LOGS/forbidden-scan.json" 2> "$LOGS/forbidden-scan.err"

# Axiom summary from the Audit log (handles multi-line cones).
python3 - <<'PY' > "$LOGS/axioms.json"
import json, re, collections
text = open("longrun/d7rlv-logs/lean_release_Poincare_D7_Reduced_Audit.lean.log", encoding="utf-8").read()
entries = []
for m in re.finditer(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S):
    name = m.group(1)
    ax = [a.strip() for a in m.group(2).split(",") if a.strip()]
    entries.append({"name": name, "axioms": sorted(ax)})
for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
    entries.append({"name": m.group(1), "axioms": []})
cones = collections.Counter(tuple(e["axioms"]) for e in entries)
standard = {frozenset(), frozenset({"propext"}),
            frozenset({"propext", "Quot.sound"}),
            frozenset({"propext", "Classical.choice", "Quot.sound"})}
nonstandard = [e for e in entries if frozenset(e["axioms"]) not in standard]
print(json.dumps({
  "entries": len(entries),
  "cones": [{"cone": list(c), "count": n} for c, n in
            sorted(cones.items(), key=lambda kv: -kv[1])],
  "nonstandard": nonstandard,
  "declarations": entries,
}, indent=1))
PY

# Full package build.
(cd release && lake build) > "$LOGS/lake_build.log" 2>&1
echo $? > "$LOGS/lake_build_exit.txt"

echo "verification transcript complete"
