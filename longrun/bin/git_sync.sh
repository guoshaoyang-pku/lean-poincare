#!/usr/bin/env bash
# Rebuild the integrated repo snapshot from ophis and push to GitHub.
set -euo pipefail
cd "$HOME/Desktop/workdir/poincare-formalization"
test -d lean-poincare-repo/.git
test -z "$(git -C lean-poincare-repo status --porcelain)" || { echo "Refusing to sync over local changes" >&2; exit 1; }
ssh -o BatchMode=yes ophis-gpu 'cd ~/workdir/lean_poincare/longrun && python3 - << "PYEOF"
import json, os, shutil
q = json.load(open("queue.json"))
base = os.path.expanduser("~/workdir/lean_poincare/longrun")
ov = os.path.join(base, "integrated_overlay")
for t in q["tasks"]:
    if t["status"] != "verified": continue
    wt = os.path.join(base, "worktrees", t["id"])
    for sub in ["release/Poincare", "release/Audit", "longrun/results"]:
        src = os.path.join(wt, sub)
        if not os.path.isdir(src): continue
        dst = os.path.join(ov, sub)
        for dirpath, dirnames, filenames in os.walk(src):
            dirnames[:] = [d for d in dirnames if d not in (".lake",".git")]
            rel = os.path.relpath(dirpath, src)
            for fn in filenames:
                s = os.path.join(dirpath, fn)
                d = os.path.join(dst, rel, fn)
                os.makedirs(os.path.dirname(d), exist_ok=True)
                shutil.copy2(s, d)
PYEOF
cd ~/workdir/lean-poincare-git && rsync -a ~/workdir/lean_poincare/longrun/integrated_overlay/ ./'
rsync -az --exclude='.git/' --exclude='.lake/' --exclude='node_modules/' -e ssh ophis-gpu:workdir/lean-poincare-git/ lean-poincare-repo/
cd lean-poincare-repo
git add -A
if ! git diff --cached --quiet; then
  git commit -m "sync: $(date '+%Y-%m-%d %H:%M') integrated compile-checked snapshot"
fi
git push origin main
