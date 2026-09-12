#!/bin/bash
# D13: pre-fetch the pinned transitive dependencies of the upstream packages
# into probes/.lake/packages/<name> as shallow single-commit checkouts.
#
# Revisions are read from the preserved upstream lake-manifest.json (never
# rewritten): the upstream pin is what gets materialised here.
set -uo pipefail
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-upstream-api-inventory-3602
export ALL_PROXY=socks5h://127.0.0.1:1080
MAN="$WT/third_party/frenzymath/Poincare-Conjecture/formalized-sources/DoCarmo/lake-manifest.json"
PKGS="$WT/probes/.lake/packages"
mkdir -p "$PKGS"

python3 - "$MAN" <<'PY' > /tmp/d13-deps.tsv
import json, sys
d = json.load(open(sys.argv[1]))
for p in d.get("packages", []):
    if p.get("name") == "mathlib":
        continue
    url = p.get("url")
    if not url:
        continue
    print(f"{p['name']}\t{url}\t{p['rev']}")
PY

rc=0
while IFS=$'\t' read -r name url rev; do
  dest="$PKGS/$name"
  if [ -d "$dest/.git" ] && [ "$(git -C "$dest" rev-parse HEAD 2>/dev/null)" = "$rev" ]; then
    echo "[dep] $name already at $rev"
    continue
  fi
  rm -rf "$dest"; mkdir -p "$dest"
  git -C "$dest" init -q
  git -C "$dest" remote add origin "$url"
  if git -C "$dest" fetch --depth 1 origin "$rev" >/dev/null 2>&1 \
     && git -C "$dest" checkout -q FETCH_HEAD; then
    echo "[dep] $name $(git -C "$dest" rev-parse HEAD)"
  else
    echo "[dep] $name FAILED ($url @ $rev)"; rc=1
  fi
done < /tmp/d13-deps.tsv
exit $rc
