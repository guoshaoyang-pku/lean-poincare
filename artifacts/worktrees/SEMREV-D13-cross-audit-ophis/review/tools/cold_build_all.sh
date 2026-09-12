#!/usr/bin/env bash
# Independent cold rebuild of every transported ophis D13 card snapshot.
# Fresh source tree + fresh .lake/build; only the pinned package prebuild (a private copy at
# review/packages, mathlib rev 7974e751...) is linked in.  No card oleans are reused.
set -u
REV=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/SEMREV-D13-cross-audit-ophis
PARENT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$REV/review/logs" "$REV/review/build"

TASKS="${*:-D13-heatkernel-bridge-d10-d7 D13-vankampen-recognition D13-manifold-ibp-volume-form \
D13-deturck-shorttime-producer D13-critical-path-review D13-morgan-tian-adapter-plan \
D13-upstream-adapter-audit D13-topping-ricci-adapter-plan D13-integrated-kernel-audit \
D13-cross-audit-360-cards}"

for task in $TASKS; do
  SRC="$PARENT/audit/ophis/$task/release"
  DST="$REV/review/build/$task/release"
  LOG="$REV/review/logs/$task-cold-build.log"
  if [ ! -d "$SRC" ]; then echo "$task NO_SOURCE"; continue; fi
  rm -rf "$REV/review/build/$task"
  mkdir -p "$DST"
  cp -a "$SRC/." "$DST/"
  rm -rf "$DST/.lake"
  mkdir -p "$DST/.lake/packages"
  for p in "$REV/review/packages"/*; do
    ln -sfn "$p" "$DST/.lake/packages/$(basename "$p")"
  done
  (
    echo "=== INDEPENDENT cold build $task start=$(date -Is)"
    echo "=== mathlib rev: $(git -C "$REV/review/packages/mathlib" rev-parse HEAD)"
    echo "=== source .lean files: $(find "$DST" -name '*.lean' -not -path '*/.lake/*' | wc -l)"
    cd "$DST" && timeout 7200 lake build
    rc=$?
    echo "=== COLD_BUILD_EXIT $rc end=$(date -Is)"
  ) > "$LOG" 2>&1
  rc=$?
  echo "$task cold-build exit=$rc jobs=$(grep -c '^✔' "$LOG") log=$LOG"
done
echo BUILD_ALL_DONE
