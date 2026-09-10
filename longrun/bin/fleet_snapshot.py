#!/usr/bin/env python3
import argparse
import collections
import json
import os
from pathlib import Path
import re
import time

parser = argparse.ArgumentParser()
parser.add_argument("--host", required=True)
parser.add_argument("--output", type=Path)
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
queue = json.loads((root / "queue.json").read_text())
now = time.time()
settings = (Path.home() / ".dsh/settings.yaml").read_text()
model = re.search(r"^\s+model:\s*(\S+)", settings, re.M)
result = {
    "host": args.host,
    "observed_at": time.strftime("%FT%T%z"),
    "model_configured": model.group(1) if model else None,
    "capacity": queue.get("max_concurrent"),
    "queue_counts": dict(collections.Counter(task["status"] for task in queue["tasks"])),
    "load_average": list(os.getloadavg()),
    "tasks": [],
}
for task in queue["tasks"]:
    if task.get("host", args.host) != args.host or task["status"] == "verified":
        continue
    state = root / "state" / task["id"]
    entry = {"id": task["id"], "queue_status": task["status"], "worker_alive": False}
    try:
        heartbeat = json.loads((state / "heartbeat.json").read_text())
        pid = int(heartbeat["pid"])
        entry["worker_alive"] = b"worker_loop.sh" in Path(f"/proc/{pid}/cmdline").read_bytes()
        entry["heartbeat_age_seconds"] = round(now - (state / "heartbeat.json").stat().st_mtime)
    except (OSError, ValueError, KeyError):
        pass
    latest = state / "latest.log"
    if latest.exists():
        with latest.open("rb") as stream:
            stream.seek(max(0, latest.stat().st_size - 4096))
            tail = stream.read().decode(errors="replace")
        entry["latest_log_bytes"] = latest.stat().st_size
        entry["latest_log_age_seconds"] = round(now - latest.stat().st_mtime)
        entry["latest_tail_transport_error"] = "dsh: TRANSPORT:" in tail
    run = state / "last_run.json"
    if run.exists():
        entry["last_run"] = json.loads(run.read_text())
    entry["paused_marker"] = (state / "PAUSED").exists()
    entry["done_marker"] = (state / "DONE").exists()
    entry["d12_source_files"] = len(list((root / "worktrees" / task["id"] / "release/Poincare/D12").rglob("*.lean")))
    result["tasks"].append(entry)
text = json.dumps(result, indent=2) + "\n"
if args.output:
    args.output.write_text(text)
print(json.dumps({key: value for key, value in result.items() if key != "tasks"}))
print("ALIVE", sum(task["worker_alive"] for task in result["tasks"]), "D12_SOURCES", sum(task["d12_source_files"] for task in result["tasks"]))
