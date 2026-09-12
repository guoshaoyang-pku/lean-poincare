#!/usr/bin/env bash
# Assemble the full artifact bundle into the publication staging dir
# (~/workdir/lean-poincare-git) on ophis-gpu. Excludes rebuildable bulk:
# .lake, .git, .elan-home, input/ (regenerable dep copies), L1 pre-rebuild
# backup, L2 mathlib-cache, D9 raw audit logs, and any single file >95M
# (GitHub hard limit 100M).
set -euo pipefail
cd /data3/guoshaoyang/workdir/lean_poincare/longrun
STAGE="$HOME/workdir/lean-poincare-git"
mkdir -p "$STAGE/artifacts/worktrees" "$STAGE/artifacts/offloaded" "$STAGE/artifacts/leaders" "$STAGE/longrun"

echo "=== [1/6] rebuild integrated overlay from verified tasks"
python3 - << 'PYEOF'
import json, os, shutil
q = json.load(open("queue.json"))
base = os.path.expanduser("~/workdir/lean_poincare/longrun")
base = "/data3/guoshaoyang/workdir/lean_poincare/longrun"
ov = os.path.join(base, "integrated_overlay")
n = 0
for t in q["tasks"]:
    if t["status"] != "verified": continue
    n += 1
    wt = os.path.join(base, "worktrees", t["id"])
    for sub in ["release/Poincare", "release/Audit", "longrun/results"]:
        src = os.path.join(wt, sub)
        if not os.path.isdir(src): continue
        src = os.path.realpath(src)
        dst = os.path.join(ov, sub)
        for dirpath, dirnames, filenames in os.walk(src):
            dirnames[:] = [d for d in dirnames if d not in (".lake", ".git") and not (d.startswith("raw") and "Audit/D9/logs" in dirpath)]
            rel = os.path.relpath(dirpath, src)
            for fn in filenames:
                s = os.path.join(dirpath, fn)
                if os.path.getsize(s) > 95 * 1024 * 1024: continue
                d = os.path.join(dst, rel, fn)
                os.makedirs(os.path.dirname(d), exist_ok=True)
                shutil.copy2(s, d)
print("overlay merged from", n, "verified tasks")
PYEOF
rm -rf "$STAGE/release" && rsync -a integrated_overlay/ "$STAGE/"

echo "=== [2/6] runtime snapshots (queue/prompts/state/results/logs)"
mkdir -p "$STAGE/longrun"
cp queue.json "$STAGE/longrun/queue-snapshot.json"
rsync -a prompts/ "$STAGE/longrun/prompts/"
rsync -a --max-size=95M state/ "$STAGE/longrun/state/"
rsync -a results/ "$STAGE/longrun/results/" 2>/dev/null || true
rsync -a logs/ "$STAGE/longrun/logs/"
for w in worktrees/*/; do
  t="$(basename "$w")"; [ "$t" = leaders ] && continue
  rsync -aL "$w/longrun/results/" "$STAGE/longrun/results/" 2>/dev/null || true
done

rm -rf "$STAGE/artifacts"
mkdir -p "$STAGE/artifacts/worktrees" "$STAGE/artifacts/offloaded" "$STAGE/artifacts/leaders"
echo "=== [3/6] active task worktrees (authored content)"
for w in worktrees/*/; do
  t="$(basename "$w")"
  [ "$t" = leaders ] && continue
  if [ -L "${w%/}" ]; then
    # offloaded verified worktree: unique small content only
    mkdir -p "$STAGE/artifacts/offloaded/$t"
    rsync -aL --max-size=95M "$w/longrun/" "$STAGE/artifacts/offloaded/$t/longrun/" 2>/dev/null || true
    cp -L "$w/checkpoint.json" "$STAGE/artifacts/offloaded/$t/checkpoint.json" 2>/dev/null || true
    continue
  fi
  rsync -a --max-size=95M \
    --exclude=.lake/ --exclude=.git/ --exclude=.elan-home/ --exclude=input/ \
    --exclude=raw*/ --exclude=node_modules/ --exclude=third_party/ \
    "$w" "$STAGE/artifacts/worktrees/$t/"
done

echo "=== [4/6] leader workspaces (minus pre-rebuild backup and mathlib cache)"
rsync -a --max-size=95M \
  --exclude=.lake/ --exclude=.git/ --exclude=.elan-home/ \
  --exclude=pre-rebuild/ --exclude=mathlib-cache/ --exclude=node_modules/ --exclude=third_party/ \
  worktrees/leaders/ "$STAGE/artifacts/leaders/"

echo "=== [5/6] record oversized exclusions"
find worktrees state -type f -size +95M \
  -not -path "*/.lake/*" -not -path "*/.git/*" -not -path "*/.elan-home/*" \
  -not -path "*/pre-rebuild/*" -not -path "*/mathlib-cache/*" 2>/dev/null \
  > "$STAGE/artifacts/EXCLUDED-OVERSIZE.txt" || true
wc -l < "$STAGE/artifacts/EXCLUDED-OVERSIZE.txt"

echo "=== [6/6] size report"
du -sh "$STAGE"
du -sh "$STAGE"/* 2>/dev/null | sort -rh | head -8
du -sh "$STAGE"/artifacts/* 2>/dev/null | sort -rh | head -8
echo BUNDLE_DONE
