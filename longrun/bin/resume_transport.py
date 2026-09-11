#!/usr/bin/env python3
import argparse
import fcntl
import json
import os
from pathlib import Path
import subprocess
import time

parser = argparse.ArgumentParser()
parser.add_argument("--host", required=True, choices=["ophis-gpu", "360-1", "360-2"])
parser.add_argument("--capacity", type=int, required=True, choices=range(1, 13))
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
with (root / "dispatcher.lock").open("a") as lock:
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError as exc:
        raise SystemExit("REFUSE: another dispatcher/control operation owns dispatcher.lock") from exc
    queue_path = root / "queue.json"
    queue = json.loads(queue_path.read_text())
    for task in queue["tasks"]:
        if task.get("host", args.host) != args.host:
            continue
        state = root / "state" / task["id"]
        marker = state / "PAUSED"
        latest = state / "latest.log"
        if marker.exists() and "eight consecutive runtime failures" in marker.read_text() and latest.exists() and "TRANSPORT:" in latest.read_text(errors="replace"):
            marker.rename(state / f"PAUSED.reviewed-{int(time.time())}")
            task["status"] = "queued"
            task["resumed_after"] = "Transport route verified by supervisor; checkpoints preserved"
            print("RESUME", task["id"])
    queue["max_concurrent"] = args.capacity
    # Keep the host-configured model; never silently switch model during transport recovery.
    configured_model = queue.get("model") or "deepseek-flash"
    queue["model"] = configured_model
    temporary = queue_path.with_suffix(".json.tmp")
    temporary.write_text(json.dumps(queue, indent=2) + "\n")
    temporary.replace(queue_path)
existing = subprocess.run(["pgrep", "-af", "python3 .*bin/dispatch_loop.py"], text=True, capture_output=True)
if any(str(root / "bin/dispatch_loop.py") in line and "pgrep" not in line for line in existing.stdout.splitlines()):
    raise SystemExit("REFUSE: dispatcher already running; do not start a second instance")
with (root / "logs/dispatch_stdout.log").open("ab") as output:
    process = subprocess.Popen(["python3", str(root / "bin/dispatch_loop.py")], cwd=root, env=dict(os.environ, DSH_HOST=args.host), stdin=subprocess.DEVNULL, stdout=output, stderr=output, start_new_session=True)
print("DISPATCHER", process.pid, "CAPACITY", args.capacity)
