#!/bin/bash
# D13: fetch the pinned mathlib (rev 520045ab14e26149ee970e2e617ca04b09bde5d6)
# into probes/.lake/packages/mathlib WITHOUT changing any upstream pin.
#
# The upstream packages require mathlib at exactly this rev; this script only
# materialises the checkout that Lake would otherwise clone in full.
set -uo pipefail
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-upstream-api-inventory-3602
export ALL_PROXY=socks5h://127.0.0.1:1080
REV=520045ab14e26149ee970e2e617ca04b09bde5d6
DEST="$WT/probes/.lake/packages/mathlib"

mkdir -p "$WT/probes/.lake/packages"
if [ ! -d "$DEST/.git" ]; then
  rm -rf "$DEST"
  mkdir -p "$DEST"
  git -C "$DEST" init -q
  git -C "$DEST" remote add origin https://github.com/leanprover-community/mathlib4.git
fi
echo "[mathlib] fetching $REV at $(date -Is)"
git -C "$DEST" fetch --depth 1 origin "$REV" || exit 11
git -C "$DEST" checkout -q FETCH_HEAD || exit 12
echo "[mathlib] HEAD=$(git -C "$DEST" rev-parse HEAD)"
test "$(git -C "$DEST" rev-parse HEAD)" = "$REV" || { echo "[mathlib] REV MISMATCH"; exit 13; }
echo "[mathlib] ok at $(date -Is)"
