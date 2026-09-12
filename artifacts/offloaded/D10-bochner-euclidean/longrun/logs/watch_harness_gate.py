#!/usr/bin/env python3
"""Watch state/D10-bochner-euclidean/gate.json: copy it the instant the harness writes it
(so a failing gate.json, which the dispatcher deletes immediately, is not lost)."""
import os, shutil, time, json

STATE = "/data3/guoshaoyang/workdir/lean_poincare/longrun/state/D10-bochner-euclidean"
GATE = os.path.join(STATE, "gate.json")
SAVE = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-bochner-euclidean/longrun/logs/harness_gate_capture.json"

seen = False
t0 = time.time()
last = None
while time.time() - t0 < 900:
    try:
        st = os.stat(GATE)
        if st.st_size > 0:
            shutil.copy2(GATE, SAVE)
            seen = True
            with open(SAVE) as fh:
                d = json.load(fh)
            fails = [f for f in d.get("files", []) if f.get("exit") != 0]
            print(f"[{time.strftime('%T')}] captured gate.json ok={d.get('ok')} n={len(d.get('files', []))} fails={len(fails)}", flush=True)
            for f in fails[:10]:
                print("  FAIL", f, flush=True)
            # keep watching: the dispatcher may overwrite (or delete) it
    except FileNotFoundError:
        if seen:
            print(f"[{time.strftime('%T')}] gate.json removed by dispatcher (repair queued)", flush=True)
            seen = False
    except Exception as e:
        print("watch error:", e, flush=True)
    time.sleep(0.05)
print("watcher done", flush=True)
