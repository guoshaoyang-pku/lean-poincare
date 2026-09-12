#!/usr/bin/env bash
# D7-hamilton-short-time verification transcript.
# Run from the worktree root:
#   bash longrun/d7hs-logs/run_verification.sh
set -u

export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LOGS="$ROOT/longrun/d7hs-logs"
mkdir -p "$LOGS"
cd "$ROOT"

FILES=(
  release/Poincare/D7/ShortTime/Basic.lean
  release/Poincare/D7/ShortTime/ODE.lean
  release/Poincare/D7/ShortTime/MatrixDeriv.lean
  release/Poincare/D7/ShortTime/Gauge.lean
  release/Poincare/D7/ShortTime/Equivalence.lean
  release/Poincare/D7/ShortTime/Statements.lean
  release/Poincare/D7/ShortTime/Example.lean
  release/Poincare/D7/ShortTime/Probe.lean
  release/Poincare/D7/ShortTime/Audit.lean
  release/Poincare/D7/ShortTime.lean
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
python3 input/d5-tools/scan_forbidden.py release/Poincare/D7/ShortTime \
  > "$LOGS/forbidden-scan.json" 2> "$LOGS/forbidden-scan.err"
python3 - <<'PY' > "$LOGS/forbidden-scan-with-umbrella.json"
import json, sys, importlib.util, os
spec = importlib.util.spec_from_file_location("scan", "input/d5-tools/scan_forbidden.py")
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)
matches = mod.scan_file("release/Poincare/D7/ShortTime.lean")
out = {
  "file": "release/Poincare/D7/ShortTime.lean",
  "hard_match_count": sum(1 for m in matches if m["hard"]),
  "matches": matches,
}
print(json.dumps(out, indent=1))
PY

# Axiom summary from the Audit log.
python3 - <<'PY' > "$LOGS/axioms.json"
import json, re, collections
entries = []
for line in open("longrun/d7hs-logs/lean_release_Poincare_D7_ShortTime_Audit.lean.log", encoding="utf-8"):
    m = re.match(r"'(.*)' depends on axioms: \[(.*)\]", line.strip())
    if m:
        name = m.group(1)
        ax = [a.strip() for a in m.group(2).split(",") if a.strip()]
        entries.append({"name": name, "axioms": sorted(ax)})
cones = collections.Counter(tuple(e["axioms"]) for e in entries)
nonstandard = [e for e in entries
               if any(a not in ("propext", "Classical.choice", "Quot.sound") for a in e["axioms"])]
print(json.dumps({
  "entries": len(entries),
  "cones": [{"cone": list(c), "count": n} for c, n in sorted(cones.items(), key=lambda kv: -kv[1])],
  "nonstandard": nonstandard,
  "declarations": entries,
}, indent=1))
PY

echo "verification transcript complete"
