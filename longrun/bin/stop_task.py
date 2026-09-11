#!/usr/bin/env python3
import json, os, signal, sys, time
from pathlib import Path
if len(sys.argv) != 2: raise SystemExit("usage: stop_task.py TASK_ID")
root=Path(__file__).resolve().parent.parent; task_id=sys.argv[1]; state=root/"state"/task_id; state.mkdir(parents=True, exist_ok=True)
(state/"TERMINATE_REQUESTED").write_text(json.dumps({"task":task_id,"requested_at":time.strftime("%FT%T%z")})+"\n")
try:
 hb=json.loads((state/"heartbeat.json").read_text()); pid=int(hb["pid"]); os.killpg(os.getpgid(pid), signal.SIGTERM); print(f"STOP_SENT {task_id} {pid}")
except (OSError, ValueError, KeyError): print(f"STOP_MARKED {task_id}")
