#!/usr/bin/env bash
# D7-riemann-curvature-tensor: consolidated verification transcript.
# Run from the worktree root:  bash longrun/d7-logs-verify/run_verification.sh
set -u
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"

WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-riemann-curvature-tensor
D6=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release
LOG=$WT/longrun/d7-logs-verify
cd "$WT/release" || exit 2

echo "=== environment ==="
date -u +"generated_at=%Y-%m-%dT%H:%M:%SZ"
echo "lean: $(lake env lean --version)"
echo "lake: $(lake --version)"
echo "mathlib_rev: $(git -C /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages/mathlib rev-parse HEAD)"

echo
echo "=== 1. clean D7 build artifacts, then full lake build ==="
rm -rf .lake/build/lib/lean/Poincare/D7 .lake/build/ir/Poincare/D7
( time lake build ) > "$LOG/lake_build_all.log" 2>&1
echo "lake_build_exit=$?"
tail -3 "$LOG/lake_build_all.log"

echo
echo "=== 2. per-file lake env lean ==="
: > "$LOG/exit_codes.txt"
for f in Poincare/D7/Curvature/Basic.lean \
         Poincare/D7/Curvature/Symmetries.lean \
         Poincare/D7/Curvature/Sectional.lean \
         Poincare/D7/Curvature/Example.lean \
         Poincare/D7/Curvature/Blocked.lean \
         Poincare/D7/Curvature/Bridge.lean \
         Poincare/D7/Curvature/Probe.lean \
         Poincare/D7/Curvature/Audit.lean \
         Poincare/D7/Curvature.lean; do
  log="$LOG/lean_$(echo "$f" | tr '/' '_').log"
  lake env lean "$f" > "$log" 2>&1
  echo "$? $f" | tee -a "$LOG/exit_codes.txt"
done

echo
echo "=== 3. #print axioms summary (from the Audit.lean log) ==="
python3 - "$LOG/lean_Poincare_D7_Curvature_Audit.lean.log" <<'PY'
import re, sys
log = open(sys.argv[1]).read()
flat = re.sub(r'\s+', ' ', log)
pat = re.compile(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
res = pat.findall(flat)
from collections import Counter
cones = Counter()
for name, _, axioms in res:
    cone = tuple(sorted(a.strip() for a in axioms.split(',') if a.strip())) if axioms else ()
    cones[cone] += 1
print("print_axioms_entries=%d" % len(res))
for cone, cnt in sorted(cones.items(), key=lambda kv: -kv[1]):
    print("cone_count=%d cone=%s" % (cnt, cone))
allowed = {'propext','Classical.choice','Quot.sound'}
bad = [n for n,_,c in res if c and not set(a.strip() for a in c.split(',')).issubset(allowed)]
print("nonstandard_cones=%s" % (bad if bad else "NONE"))
PY

echo
echo "=== 4. forbidden-token scan ==="
python3 "$WT/input/d5-tools/scan_forbidden.py" Poincare/D7 > "$LOG/forbidden-scan.json" 2> "$LOG/forbidden-scan.stderr"
echo "forbidden_scan_exit=$?"
cat "$LOG/forbidden-scan.json"

echo
echo "=== 5. mathlib curvature probe (pinned checkout) ==="
M=/data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages/mathlib
echo "curvature_files=$(grep -ril curvature "$M/Mathlib" --include='*.lean' | wc -l)"
echo "curvature_lines=$(grep -rin curvature "$M/Mathlib" --include='*.lean' | wc -l)"
grep -rin curvature "$M/Mathlib" --include='*.lean'

echo
echo "=== 6. copied-source integrity (sha256, .lake excluded) ==="
python3 - "$D6" "$WT" <<'PY'
import hashlib, json, os, sys
D6, D7 = sys.argv[1], sys.argv[2]
def sha256(p):
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for c in iter(lambda: fh.read(1<<20), b""):
            h.update(c)
    return h.hexdigest()
checked, changed, missing = 0, [], []
for root, dirs, files in os.walk(D6):
    dirs[:] = [d for d in dirs if d != ".lake"]
    for f in files:
        p = os.path.join(root, f); rel = os.path.relpath(p, D6); q = os.path.join(D7, rel)
        checked += 1
        if not os.path.exists(q): missing.append(rel)
        elif sha256(p) != sha256(q): changed.append(rel)
out = {"schema": "d7-riemann-curvature-tensor/source-integrity-v1",
       "d6_files_checked": checked, "changed": changed, "missing": missing}
print(json.dumps(out, indent=1))
PY
echo "verification_done"
