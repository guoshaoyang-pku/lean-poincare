#!/usr/bin/env bash
# Keep-alive wrapper for group leaders (小组长) and long-running controller
# sessions. Model-agnostic: LEADER_CMD may be any one-shot agent CLI
# (dsh_fixed.sh, codex exec --model <id>, ...). The session is re-invoked in
# slices; the leader protocol's checkpoint.json + 30-min briefs make restarts
# cheap. Stop by touching state/leaders/$LEADER_ID/LEADER_DONE.
#
# Required env:  LEADER_ID
# Optional env:  LEADER_CMD        (default: repo bin/dsh_fixed.sh --profile headless)
#                LEADER_PROMPT     (default: longrun/prompts/$LEADER_ID.md)
#                LEADER_SLICE_HOURS (default 4), LEADER_MAX_HOURS (default 168)
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
LEADER_ID="${LEADER_ID:?}"
STATE="$ROOT/state/leaders/$LEADER_ID"
WORKSPACE="${LEADER_WORKSPACE:-$ROOT/worktrees/leaders/$LEADER_ID}"
PROMPT="${LEADER_PROMPT:-$ROOT/prompts/$LEADER_ID.md}"
mkdir -p "$STATE" "$WORKSPACE"
exec 9>"$STATE/leader.lock"
flock -n 9 || { echo "leader $LEADER_ID already running"; exit 0; }
export PATH="$HOME/.local/node/bin:$PATH"
export DSH_HOME="${DSH_HOME:-$HOME/.dsh}"
export TMPDIR="$HOME/tmp"; mkdir -p "$TMPDIR"
if [ "${DSH_USE_API_TUNNEL:-0}" = 1 ]; then
  export NODE_OPTIONS="--require $ROOT/bin/api_proxy_preload.js"
fi
started=$(date +%s)
deadline=$((started + ${LEADER_MAX_HOURS:-168} * 3600))
round=0; failures=0
heartbeat() {
  printf '%s\n' "{\"leader\":\"$LEADER_ID\",\"pid\":$$,\"heartbeat\":\"$(date -Is)\",\"round\":$round,\"cmd\":\"${LEADER_CMD:-dsh_fixed headless}\"}" > "$STATE/heartbeat.json.tmp"
  mv "$STATE/heartbeat.json.tmp" "$STATE/heartbeat.json"
}
heartbeat
( while sleep 60; do heartbeat; done ) &
HEARTBEAT_PID=$!
trap 'kill $HEARTBEAT_PID 2>/dev/null || true' EXIT
while [ "$(date +%s)" -lt "$deadline" ]; do
  [ -f "$STATE/LEADER_DONE" ] && { echo "$(date -Is) LEADER_DONE marker; exiting" >> "$STATE/loop.log"; exit 0; }
  round=$((round + 1)); heartbeat
  context="$(cat "$PROMPT" 2>/dev/null)

You are leader $LEADER_ID (session slice $round). Workspace: $WORKSPACE (write only here).
Follow infra/swarm/LEADER-PROTOCOL.md: maintain checkpoint.json, dated research brief every 30 minutes in comms/, and emit child task JSON into comms/outbox/ with explicit id, group_id, deps, lane, acceptance. Resume from checkpoint.json and your latest brief; never restart completed work. Separate proved / conditional / model / statement-only results. This slice is limited to ${LEADER_SLICE_HOURS:-4} hours; save a checkpoint before the end."
  slice=$(( ${LEADER_SLICE_HOURS:-4} * 3600 ))
  remaining=$((deadline - $(date +%s))); [ "$remaining" -lt "$slice" ] && slice=$remaining
  [ "$slice" -gt 0 ] || break
  session_log="$STATE/session-$(date +%s)-$round.log"
  session_start=$(date +%s)
  # shellcheck disable=SC2086
  timeout --signal=TERM --kill-after=30s "${slice}s" ${LEADER_CMD:-$ROOT/../bin/dsh_fixed.sh --profile headless} "$context" > "$session_log" 2>&1
  rc=$?
  printf '%s\n' "{\"leader\":\"$LEADER_ID\",\"ended\":\"$(date -Is)\",\"exit_code\":$rc,\"round\":$round}" > "$STATE/last_run.json"
  if grep -Eq 'QUOTA:|RATE_LIMIT:|Insufficient Balance|Too many requests' "$session_log"; then
    echo "$(date -Is) provider quota/rate-limit; backing off 45m" >> "$STATE/loop.log"
    sleep 2700
    continue
  fi
  session_secs=$(( $(date +%s) - session_start ))
  if [ "$rc" -ne 0 ] && [ "$session_secs" -lt 120 ]; then
    failures=$((failures + 1))
  else
    failures=0
  fi
  if [ "$failures" -ge 8 ]; then
    printf '%s\n' "$(date -Is) eight consecutive fast failures; inspect $STATE before restarting" > "$STATE/PAUSED"
    exit 1
  fi
  sleep $((30 * (failures + 1)))
done
printf '%s\n' "$(date -Is) leader budget exhausted (LEADER_MAX_HOURS); review checkpoint before extending" > "$STATE/PAUSED"
exit 1
