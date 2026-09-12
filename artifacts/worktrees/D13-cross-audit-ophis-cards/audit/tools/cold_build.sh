#!/usr/bin/env bash
# Cold independent rebuild of one ophis D13 card's release package.
# - fresh build tree copied from the relayed sources (no .lake/build)
# - only the pinned mathlib/dep prebuild is hardlinked in (never the project's own oleans)
# - lake build in the fresh tree, full log
# usage: cold_build.sh <task> [target]
set -u
TASK="$1"; shift || true
TARGET="${*:-}"
WT=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards
BASE=/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release/release
SRC="$WT/audit/ophis/$TASK/release"
DST="$WT/audit/build/$TASK/release"
LOG="$WT/audit/logs/$TASK-cold-build.log"
if [ ! -d "$SRC" ]; then echo "NO_SOURCE $TASK"; exit 2; fi
rm -rf "$WT/audit/build/$TASK"
mkdir -p "$DST"
cp -a "$SRC/." "$DST/"
rm -rf "$DST/.lake/build"
mkdir -p "$DST/.lake"
SHARE="$WT/audit/share/packages"
if [ -d "$SHARE" ]; then
  mkdir -p "$DST/.lake/packages"
  for p in "$SHARE"/*; do
    ln -sfn "$p" "$DST/.lake/packages/$(basename "$p")"
  done
else
  echo "NO_PINNED_PACKAGES"; exit 3
fi
export ELAN_HOME=/data/home/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd "$DST" || exit 4
echo "=== cold build $TASK target='${TARGET:-default}' cwd=$DST start=$(date -Is)"
{
  echo "=== cold build $TASK target='${TARGET:-default}' cwd=$DST start=$(date -Is)"
  echo "=== mathlib rev: $(git -C .lake/packages/mathlib rev-parse HEAD 2>/dev/null)"
  echo "=== source files: $(find . -name '*.lean' -not -path './.lake/*' | wc -l)"
  # shellcheck disable=SC2086
  timeout 7200 lake build $TARGET
  rc=$?
  echo "=== COLD_BUILD_EXIT $rc end=$(date -Is)"
  exit $rc
} > "$LOG" 2>&1
rc=$?
echo "$TASK cold-build exit=$rc log=$LOG"
exit $rc
