#!/bin/bash
# Worktree-wide compile gate replica: `lake env lean <abs path>` for every .lean file,
# cwd = worktree root (the harness dispatch360 procedure).
cd /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-bochner-manifold
out=longrun/logs/gate_replica.json
results="longrun/logs/gate_replica.results.txt"
: > "$results"
fail=0; total=0
while IFS= read -r f; do
  total=$((total+1))
  if timeout 1200 lake env lean "$f" > /dev/null 2>&1; then
    echo "PASS $f" >> "$results"
  else
    echo "FAIL $f" >> "$results"
    fail=$((fail+1))
  fi
done < <(find . -name "*.lean" -not -path "./release/.lake/*" | sort)
python3 - "$total" "$fail" > "$out" << 'PYEOF'
import json, sys
total, fail = int(sys.argv[1]), int(sys.argv[2])
print(json.dumps({"files_checked": total, "failures": fail, "ok": fail == 0}))
PYEOF
echo "TOTAL=$total FAIL=$fail"
