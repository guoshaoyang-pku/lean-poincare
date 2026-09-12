#!/usr/bin/env bash
# High-frequency evidence push (ophis-gpu). Commits fleet snapshots to branch
# fleet/ophis-live so the lead can supervise remotely at 10-minute granularity.
#   MODE=quick : longrun runtime snapshot only (queue/state/results/logs/prompts,
#                leader heartbeats+checkpoints+briefs) — cron every 10 min
#   MODE=full  : entire staging tree (release overlay + artifacts) — cron hourly,
#                after build_artifact_bundle.sh
# main stays curated; fleet/ophis-live is append-only evidence stream.
set -euo pipefail
MODE="${1:-quick}"
LONGRUN=/data3/guoshaoyang/workdir/lean_poincare/longrun
STAGE="$HOME/workdir/lean-poincare-git"
PUB="$HOME/workdir/lean-poincare-pub"
LOG="$LONGRUN/logs/auto_push.log"
mkdir -p "$LONGRUN/logs"
if [ ! -d "$PUB/.git" ]; then
  git clone -q git@github.com:guoshaoyang-pku/lean-poincare.git "$PUB" || { echo "$(date -Is) $MODE: CLONE FAILED" >> "$LOG"; exit 1; }
fi
git -C "$PUB" config user.name "guoshaoyang-pku"
git -C "$PUB" config user.email "161094568+guoshaoyang-pku@users.noreply.github.com"
cd "$PUB"
git fetch -q origin main
git checkout -q fleet/ophis-live 2>/dev/null || git checkout -q -b fleet/ophis-live origin/main
git merge -q --ff-only origin/main 2>/dev/null || true
if [ "$MODE" = quick ]; then
  mkdir -p longrun
  cp "$LONGRUN/queue.json" longrun/queue-snapshot.json
  rsync -a --delete --max-size=95M "$LONGRUN/state/" longrun/state/
  rsync -a --delete "$LONGRUN/results/" longrun/results/ 2>/dev/null || true
  rsync -a --delete "$LONGRUN/logs/" longrun/logs/
  rsync -a --delete "$LONGRUN/prompts/" longrun/prompts/
  for w in "$LONGRUN"/worktrees/*/; do
    t="$(basename "$w")"; [ "$t" = leaders ] && continue
    rsync -aL "$w/longrun/results/" longrun/results/ 2>/dev/null || true
  done
  rsync -a --delete --include='*/' --include='heartbeat.json' --include='checkpoint.json' \
    --include='research-brief-*.md' --include='last_run.json' --exclude='*' \
    "$LONGRUN/worktrees/leaders/" longrun/leader-live/ 2>/dev/null || true
else
  rsync -a --delete --exclude='.git/' "$STAGE/" ./
fi
git add -A
if git diff --cached --quiet; then
  echo "$(date -Is) $MODE: no change" >> "$LOG"; exit 0
fi
git commit -q -m "fleet($MODE): evidence snapshot $(date -u +%FT%TZ) [ophis-gpu]"
if git push -q origin fleet/ophis-live; then
  echo "$(date -Is) $MODE: pushed $(git rev-parse --short HEAD)" >> "$LOG"
else
  echo "$(date -Is) $MODE: PUSH FAILED" >> "$LOG"
fi
