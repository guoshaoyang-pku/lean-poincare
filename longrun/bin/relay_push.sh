#!/usr/bin/env bash
# Runs ON a 360-X machine. Pushes finished task artifacts back to ophis-gpu
# through the reverse tunnel (127.0.0.1:10022). Central dispatcher on ophis
# re-runs the compile gate locally, so we deliberately do NOT push gate.json.
set -u
ROOT="$HOME/workdir/lean_poincare/longrun"
SSH_OPT="-p 10022 -o StrictHostKeyChecking=no -o BatchMode=yes -o ConnectTimeout=20"
DST="guoshaoyang@127.0.0.1:workdir/lean_poincare/longrun"
LOG="$ROOT/logs/relay_push.log"
mkdir -p "$ROOT/logs"
exec 9>"$ROOT/relay.lock"
flock -n 9 || exit 0

while true; do
  for d in "$ROOT/state"/*/; do
    t="$(basename "$d")"
    [ -f "$d/DONE" ] || [ -f "$d/PAUSED" ] || continue
    [ -f "$d/PUSHED" ] && continue
    [ -d "$ROOT/worktrees/$t" ] || continue
    echo "$(date -Is) PUSH START $t" >> "$LOG"
    if ! ssh $SSH_OPT guoshaoyang@127.0.0.1 "mkdir -p workdir/lean_poincare/longrun/state/'$t'; cd workdir/lean_poincare/longrun/worktrees && { test -d '$t' || cp -a --reflink=auto D6_weekly_release '$t'; }" >> "$LOG" 2>&1; then
      echo "$(date -Is) PUSH PREPARE_FAIL $t" >> "$LOG"
      continue
    fi
    ok=1
    rsync -az --timeout=600 --exclude='.lake/' --exclude='.git/' -e "ssh $SSH_OPT" \
      "$ROOT/worktrees/$t/" "$DST/worktrees/$t/" >> "$LOG" 2>&1 || ok=0
    if [ "$ok" = 1 ]; then
      rsync -az --timeout=120 -e "ssh $SSH_OPT" \
        "$d/last_run.json" "$d/latest.log" "$DST/state/$t/" >> "$LOG" 2>&1 || { echo "$(date -Is) PUSH EVIDENCE_FAIL $t" >> "$LOG"; continue; }
      marker=DONE
      [ -f "$d/PAUSED" ] && marker=REMOTE_PAUSED
      ssh $SSH_OPT guoshaoyang@127.0.0.1 "mkdir -p workdir/lean_poincare/longrun/state/'$t' && touch workdir/lean_poincare/longrun/state/'$t'/'$marker'" >> "$LOG" 2>&1 \
        && { touch "$d/PUSHED"; echo "$(date -Is) PUSH OK $t" >> "$LOG"; } \
        || echo "$(date -Is) PUSH MARK_FAIL $t" >> "$LOG"
    else
      echo "$(date -Is) PUSH FAIL $t" >> "$LOG"
    fi
  done
  sleep 600
done
