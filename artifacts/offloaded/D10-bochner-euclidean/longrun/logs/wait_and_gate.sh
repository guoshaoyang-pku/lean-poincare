#!/usr/bin/env bash
# Wait until no `lake build` is running inside this worktree, then run the full
# compile-gate replica over every non-.lake .lean file and record the result.
set -u
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-bochner-euclidean
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"

busy() {
  local p cmd cwd
  for p in $(pgrep -x lake 2>/dev/null); do
    cmd=$(tr '\0' ' ' < "/proc/$p/cmdline" 2>/dev/null || true)
    cwd=$(readlink "/proc/$p/cwd" 2>/dev/null || true)
    case "$cmd" in
      *" build"*) case "$cwd" in *D10-bochner-euclidean*) return 0;; esac;;
    esac
  done
  return 1
}

for i in $(seq 1 360); do
  if ! busy; then
    sleep 20
    if ! busy; then break; fi
  fi
  sleep 10
done

echo "=== build log tail ==="
tail -5 "$WT/longrun/logs/D10-full-build.log" 2>/dev/null || true
echo "=== starting full gate replica at $(date -Is) ==="
python3 "$WT/longrun/logs/gate_final.py" > "$WT/longrun/logs/D10-gate-final.log" 2>&1
echo "GATE_FINAL_EXIT=$?"
python3 - <<'EOF'
import json
p = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-bochner-euclidean/longrun/logs/D10-gate-final.json"
d = json.load(open(p))
print("ok =", d["ok"], " files =", len(d["files"]), " elapsed =", d["elapsed"])
for f in d["files"]:
    if f["exit"] != 0:
        print("FAIL", f["exit"], f["file"])
EOF
