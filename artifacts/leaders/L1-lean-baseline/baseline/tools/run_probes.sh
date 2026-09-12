#!/bin/bash
# Run one declaration-inventory probe per module, in parallel; resumable.
#
# v2 (continuation invocation, 2026-09-11T23:5x+08:00):
#   * `import Lean.Elab.Command` is now the first line of every generated probe
#     (modules with no imports, e.g. NegControl, ExpectedModules, otherwise
#     cannot use `run_cmd`).
#   * exit status is recorded per probe as <base>.exit instead of appending to a
#     shared exits.txt, so parallel writes cannot race or leave stale skips.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LOGDIR="$ROOT/baseline/logs/probes"
mkdir -p "$LOGDIR"
cd "$ROOT/release"
run_one() {
  local p="$1"
  local base
  base="$(basename "$p" .lean)"
  if [ -f "$LOGDIR/$base.exit" ]; then return 0; fi
  timeout 900 lake env lean "../baseline/audit/probes/$base.lean" > "$LOGDIR/$base.log" 2>&1
  local rc=$?
  printf '%s\n' "$rc" > "$LOGDIR/$base.exit.tmp.$$" && mv "$LOGDIR/$base.exit.tmp.$$" "$LOGDIR/$base.exit"
}
export -f run_one
export LOGDIR
ls "$ROOT"/baseline/audit/probes/[0-9]*.lean | xargs -P "${PROBE_PARALLELISM:-24}" -I{} bash -c 'run_one "$@"' _ {}
echo "RUNNER_DONE"
