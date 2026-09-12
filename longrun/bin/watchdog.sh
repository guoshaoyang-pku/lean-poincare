#!/usr/bin/env bash
# Dispatcher watchdog. Install via cron (every minute + @reboot):
#   * * * * * /path/to/longrun/bin/watchdog.sh
#   @reboot   /path/to/longrun/bin/watchdog.sh
# dispatcher.lock (flock) makes double-start impossible, so this is safe to
# run while the dispatcher is alive. Logs only when it actually restarts.
set -u
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT" || exit 1
LOG="$ROOT/logs/watchdog.log"
mkdir -p "$ROOT/logs"
if pgrep -f "python3.*bin/dispatch_loop.py" > /dev/null 2>&1; then
  exit 0
fi
echo "$(date -Is) dispatcher not running; starting" >> "$LOG"
setsid nohup python3 bin/dispatch_loop.py >> logs/dispatch.out 2>&1 < /dev/null &
sleep 3
if pgrep -f "python3.*bin/dispatch_loop.py" > /dev/null 2>&1; then
  echo "$(date -Is) dispatcher started ok" >> "$LOG"
else
  echo "$(date -Is) dispatcher FAILED to start; see logs/dispatch.out" >> "$LOG"
fi
