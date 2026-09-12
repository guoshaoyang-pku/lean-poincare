#!/usr/bin/env bash
# A3 round-13: cold rebuild the semantic-ledger snapshot package from source
# (keeps the shared .lake/packages symlink, drops the 1.3G local build cache).
set -u
ROOT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-360-cards
SRC=$ROOT/audit360/pkgs/D12-semantic-ledger-snapshot
DST=$ROOT/audit360/r13/rebuild/D12-semantic-ledger-snapshot
LOGS=$ROOT/audit360/r13/logs
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH=$ELAN_HOME/bin:$PATH
rm -rf "$DST"; mkdir -p "$DST"
(cd "$SRC" && tar cf - --exclude='./.lake/build' .) | (cd "$DST" && tar xf -)
echo "=== snapshot cold rebuild start $(date -Is) ==="
( cd "$DST" && timeout 5400 lake build ) >"$LOGS/rebuild_snapshot.log" 2>&1
echo "rc=$? end=$(date -Is)" >>"$LOGS/rebuild_snapshot.log"
tail -2 "$LOGS/rebuild_snapshot.log"
