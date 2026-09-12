#!/usr/bin/env python3
"""Exact replica of dispatch360.compile_gate, for local diagnosis only.

Walks the worktree (excluding .lake/.git/.dshpkg), runs `lake env lean <file>`
with cwd = worktree root, and writes the per-file exit codes to
longrun/logs/gate_replica.json.  This never writes state/<task>/gate.json.
"""
import json, os, subprocess, sys, time

WT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-bochner-euclidean"
OUT = os.path.join(WT, "longrun", "logs", "gate_replica.json")

ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data/home/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = os.path.expanduser("~/.local/node/bin") + ":" + ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")

files = []
for dirpath, dirnames, filenames in os.walk(WT):
    dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", ".dshpkg")]
    for fn in filenames:
        if fn.endswith(".lean"):
            files.append(os.path.join(dirpath, fn))
files.sort()

ok = True
detail = []
t0 = time.time()
for f in files:
    t1 = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", f], cwd=WT, env=ENV,
                           capture_output=True, text=True, timeout=1800)
        code = r.returncode
        tail = (r.stdout + r.stderr)[-4000:]
    except subprocess.TimeoutExpired:
        code = "timeout"
        tail = ""
    dt = time.time() - t1
    detail.append({"file": f, "exit": code, "seconds": round(dt, 1)})
    if code != 0:
        ok = False
        print(f"FAIL exit={code} {f}", flush=True)
        print(tail, flush=True)
    else:
        print(f"ok   {dt:6.1f}s {f}", flush=True)
    with open(OUT, "w") as fh:
        json.dump({"ok": ok, "files": detail, "elapsed": round(time.time() - t0, 1)},
                  fh, indent=2)

print(f"DONE ok={ok} n={len(files)} elapsed={round(time.time()-t0,1)}s", flush=True)
