#!/usr/bin/env bash
# D7-ricci-scalar-curvature: consolidated verification transcript.
# Run from the worktree root:  bash longrun/d7rs-logs/run_verification.sh
set -u
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"

WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-ricci-scalar-curvature
LOG=$WT/longrun/d7rs-logs
mkdir -p "$LOG"
cd "$WT" || exit 2

echo "=== environment ==="
date -u +"generated_at=%Y-%m-%dT%H:%M:%SZ"
echo "lean: $(lake env lean --version)"
echo "lake: $(lake --version)"
echo "mathlib_rev: $(git -C /data3/guoshaoyang/workdir/lean_poincare/poincare-lab/.lake/packages/mathlib rev-parse HEAD)"

echo
echo "=== 1. per-file lake env lean (from the worktree root, harness gate style) ==="
: > "$LOG/exit_codes.txt"
FILES="release/Poincare/D7/RicciScalar/Basic.lean
release/Poincare/D7/RicciScalar/Scalar.lean
release/Poincare/D7/RicciScalar/Product.lean
release/Poincare/D7/RicciScalar/Variation.lean
release/Poincare/D7/RicciScalar/Example.lean
release/Poincare/D7/RicciScalar/Bridge.lean
release/Poincare/D7/RicciScalar/Probe.lean
release/Poincare/D7/RicciScalar/Audit.lean
release/Poincare/D7/RicciScalar.lean"
for f in $FILES; do
  log="$LOG/lean_$(echo "$f" | tr '/' '_').log"
  lake env lean "$f" > "$log" 2>&1
  echo "$? $f" | tee -a "$LOG/exit_codes.txt"
done

echo
echo "=== 2. #print axioms summary (from the Audit.lean log) ==="
python3 - "$LOG/lean_release_Poincare_D7_RicciScalar_Audit.lean.log" <<'PY'
import re, sys, json
from collections import Counter
log = open(sys.argv[1]).read()
flat = re.sub(r'\s+', ' ', log)
pat = re.compile(r"'(.+?)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
res = pat.findall(flat)
cones = Counter()
for name, _, axioms in res:
    cone = tuple(sorted(a.strip() for a in axioms.split(',') if a.strip())) if axioms else ()
    cones[cone] += 1
print("print_axioms_entries=%d" % len(res))
for cone, cnt in sorted(cones.items(), key=lambda kv: -kv[1]):
    print("cone_count=%d cone=%s" % (cnt, cone))
allowed = {'propext','Classical.choice','Quot.sound'}
bad = [n for n,_,c in res if c and not set(a.strip() for a in c.split(',')).issubset(allowed)]
print("nonstandard_axiom_entries=%d" % len(bad))
for n in bad:
    print("  NONSTANDARD %s" % n)
json.dump({"entries": len(res), "cones": [{"count": c, "cone": list(k)} for k, c in
  sorted(cones.items(), key=lambda kv: -kv[1])], "nonstandard": bad},
  open(sys.argv[1].replace('.log','.axioms.json'), 'w'), indent=1)
PY

echo
echo "=== 3. forbidden-token scan (comment/string-aware) ==="
python3 - "$LOG" <<'PY'
import sys, re, glob, os, json
log = sys.argv[1]
files = sorted(glob.glob(os.path.join(log, '..', '..', 'release', 'Poincare', 'D7', 'RicciScalar', '*.lean')))
files.append(os.path.join(log, '..', '..', 'release', 'Poincare', 'D7', 'RicciScalar.lean'))
toks = ['sorry', 'axiom', 'unsafe', 'native_decide', 'proof_wanted']
hits = []
for f in files:
    src = open(f).read()
    # strip block comments, line comments, and string literals
    src = re.sub(r'/-.*?-/', ' ', src, flags=re.S)
    src = re.sub(r'--[^\n]*', ' ', src)
    src = re.sub(r'"(?:[^"\\]|\\.)*"', '""', src)
    for t in toks:
        for m in re.finditer(r'\b' + t + r'\b', src):
            hits.append({"file": os.path.relpath(f), "token": t, "offset": m.start()})
print("files_scanned=%d hard_hits=%d" % (len(files), len(hits)))
for h in hits:
    print("  HIT", h)
json.dump({"files_scanned": len(files), "hits": hits}, open(os.path.join(log, 'forbidden-scan.json'), 'w'), indent=1)
PY

echo
echo "=== 4. result-card file inventory ==="
wc -l release/Poincare/D7/RicciScalar.lean release/Poincare/D7/RicciScalar/*.lean
