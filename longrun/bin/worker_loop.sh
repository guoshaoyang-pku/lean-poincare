#!/usr/bin/env bash
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
WORK="$ROOT/worktrees/${TASK_ID:?}"
PROMPT="$ROOT/prompts/${PROMPT_FILE:?}"
STATE="$ROOT/state/${TASK_ID}"
mkdir -p "$WORK" "$STATE"
exec 9>"$STATE/worker.lock"
flock -n 9 || exit 0
cd "$WORK" || exit 1
export PATH="$HOME/.local/node/bin:$PATH"
export DSH_HOME="${DSH_HOME:-$HOME/.dsh}"
export TMPDIR="$HOME/tmp"
mkdir -p "$TMPDIR"
if [ "${DSH_USE_API_TUNNEL:-0}" = 1 ]; then
  export NODE_OPTIONS="--require $ROOT/bin/api_proxy_preload.js"
fi
rm -f "$STATE/DONE" "$STATE/PUSHED"
cp "$PROMPT" "$STATE/prompt.md"
started=$(date +%s)
deadline=$((started + ${TASK_MAX_HOURS:-72} * 3600))
round=0
failures=0
heartbeat() {
  printf '%s\n' "{\"task\":\"$TASK_ID\",\"pid\":$$,\"heartbeat\":\"$(date -Is)\",\"model\":\"deepseek-flash\"}" > "$STATE/heartbeat.json.tmp"
  mv "$STATE/heartbeat.json.tmp" "$STATE/heartbeat.json"
}
heartbeat
heartbeat_loop() {
  while sleep 60; do heartbeat; done
}
heartbeat_loop &
HEARTBEAT_PID=$!
trap 'kill "$HEARTBEAT_PID" 2>/dev/null || true' EXIT
while [ "$(date +%s)" -lt "$deadline" ] && [ "$round" -lt "${TASK_MAX_ROUNDS:-24}" ]; do
  round=$((round + 1))
  if [ -f "$STATE/latest.log" ]; then
    mv "$STATE/latest.log" "$STATE/run-$(date +%s)-$round.log"
  fi
  remaining=$((deadline - $(date +%s)))
  slice=14400
  if [ "$remaining" -lt "$slice" ]; then slice=$remaining; fi
  [ "$slice" -gt 0 ] || break
  context="$(cat "$PROMPT")
Continue from existing files and checkpoint.json in this worktree; do not restart completed work. This invocation is limited to four hours. Save a compile-checked checkpoint at least every hour. Report a genuine mathematical blocker rather than claiming completion with a weaker theorem. Only your own longrun/results/$TASK_ID.md can complete this task."
  timeout --signal=TERM --kill-after=30s "${slice}s" "$ROOT/../bin/dsh_fixed.sh" --profile headless "$context" > "$STATE/latest.log" 2>&1
  rc=$?
  printf '%s\n' "{\"task\":\"$TASK_ID\",\"ended\":\"$(date -Is)\",\"exit_code\":$rc,\"round\":$round}" > "$STATE/last_run.json"
  # Fail closed on provider admission/quota failures. Preserve the checkpoint
  # and partial artifacts; do not spend repeated invocations until the host
  # side quota is explicitly restored.
  if grep -Eq 'QUOTA:|RATE_LIMIT:|Insufficient Balance|Too many requests' "$STATE/latest.log"; then
    printf '%s\n' "$(date -Is) provider quota/rate-limit failure; resume from checkpoint after API probe" > "$STATE/PAUSED"
    exit 1
  fi
  if [ "$rc" -eq 0 ]; then
    failures=0
    if python3 - "$WORK/longrun/results/$TASK_ID.md" <<'PY'
import pathlib, re, sys
card = pathlib.Path(sys.argv[1])
text = card.read_text() if card.exists() else ""
sys.exit(0 if re.search(r"^TASK_(DONE|BLOCKED)\b.*$", text.rstrip().split("\n")[-1]) else 1)
PY
    then
      touch "$STATE/DONE"
      exit 0
    fi
  else
    failures=$((failures + 1))
  fi
  if [ "$failures" -ge 8 ]; then
    printf '%s\n' "$(date -Is) eight consecutive runtime failures; inspect logs before restarting" > "$STATE/PAUSED"
    exit 1
  fi
  delay=$((30 * (failures + 1)))
  sleep "$delay"
done
printf '%s\n' "$(date -Is) wall-clock or invocation budget exhausted; review checkpoint before extending" > "$STATE/PAUSED"
exit 1
