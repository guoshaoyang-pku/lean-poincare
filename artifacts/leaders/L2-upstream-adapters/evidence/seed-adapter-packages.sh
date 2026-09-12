#!/bin/bash
# Seed the adapter package's .lake/packages from the already-cloned upstream
# dependency checkouts (shared/.lake/packages).  `git clone --shared` uses
# alternates, so this is instant and does not touch the network or the source
# snapshot.  Revisions are taken from the upstream shared/lake-manifest.json.
set -eu
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L2-upstream-adapters
SNAP="$WT/third_party/frenzymath/Poincare-Conjecture"
SRC="$SNAP/shared/.lake/packages"
DEST="$WT/adapters/.lake/packages"
mkdir -p "$DEST"
python3 - "$SNAP/shared/lake-manifest.json" <<'PY' > /tmp/adapter-seed-list.txt
import json, sys
m = json.load(open(sys.argv[1]))
for d in m["packages"]:
    print(d["name"], d["rev"], d["url"])
PY
while read -r name rev url; do
  if [ -d "$DEST/$name/.git" ]; then
    have=$(git -C "$DEST/$name" rev-parse HEAD)
    if [ "$have" = "$rev" ]; then echo "present $name $rev"; continue; fi
  fi
  if [ ! -d "$SRC/$name/.git" ]; then echo "MISSING-LOCAL $name"; exit 1; fi
  rm -rf "$DEST/$name"
  git clone --quiet --shared --no-checkout "$SRC/$name" "$DEST/$name"
  git -C "$DEST/$name" checkout --quiet --detach "$rev"
  git -C "$DEST/$name" remote set-url origin "$url"
  echo "seeded  $name $rev"
done < /tmp/adapter-seed-list.txt
