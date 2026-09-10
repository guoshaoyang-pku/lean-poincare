#!/usr/bin/env python3
import json
import os
from pathlib import Path
import signal
import subprocess
import time

root = Path(__file__).resolve().parent.parent
queue_path = root / "queue.json"
queue = json.loads(queue_path.read_text())
(root / "logs" / f"queue-before-restart-{int(time.time())}.json").write_text(json.dumps(queue, indent=2))
processes = subprocess.check_output(["ps", "-u", str(os.getuid()), "-o", "pid=,args="], text=True)
for line in processes.splitlines():
    fields = line.strip().split(None, 1)
    if len(fields) != 2:
        continue
    pid, command = int(fields[0]), fields[1]
    if command.startswith(("python3 ", "python ")) and command.endswith(("bin/dispatch_loop.py", "bin/dispatch360.py")):
        try:
            working_directory = Path(f"/proc/{pid}/cwd").resolve()
        except OSError:
            continue
        if str(root) not in command and working_directory not in (root, root.parent):
            continue
        os.kill(pid, signal.SIGTERM)
        print("STOP_DISPATCHER", pid, flush=True)
for task in queue["tasks"]:
    state = root / "state" / task["id"]
    try:
        heartbeat = json.loads((state / "heartbeat.json").read_text())
        pid = int(heartbeat["pid"])
        command = Path(f"/proc/{pid}/cmdline").read_bytes()
        if b"worker_loop.sh" not in command or os.getpgid(pid) != pid:
            continue
        os.killpg(pid, signal.SIGTERM)
        print("STOP_WORKER", task["id"], pid, flush=True)
        if task["status"] == "running":
            (state / "DONE").unlink(missing_ok=True)
    except (OSError, KeyError, ValueError):
        pass
print("STOPPED_OWN_FLEET_ONLY", flush=True)
