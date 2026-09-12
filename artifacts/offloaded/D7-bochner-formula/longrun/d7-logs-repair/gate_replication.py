#!/usr/bin/env python3
"""Replicate the harness compile_gate exactly (dispatch_loop.compile_gate).

Walks the worktree for *.lean (skipping .lake/.git/.dshpkg), runs
`lake env lean <abs file>` with cwd = worktree root and the supervisor's
ELAN_HOME/PATH, and records exit codes plus captured stderr/stdout.
"""
import json, os, subprocess, time

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-riemann-curvature-tensor"
LOG = os.path.join(WT, "longrun", "d7-logs-repair")
os.makedirs(LOG, exist_ok=True)

ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")

files = []
for dirpath, dirnames, filenames in os.walk(WT):
    dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", ".dshpkg")]
    for fn in filenames:
        if fn.endswith(".lean"):
            files.append(os.path.join(dirpath, fn))
files.sort()

ok = True
detail = []
for f in files:
    rel = os.path.relpath(f, WT)
    try:
        r = subprocess.run(["lake", "env", "lean", f], cwd=WT, env=ENV,
                           capture_output=True, text=True, timeout=1800)
    except subprocess.TimeoutExpired:
        ok = False
        detail.append({"file": f, "exit": "timeout"})
        with open(os.path.join(LOG, rel.replace("/", "_") + ".log"), "w") as fh:
            fh.write("TIMEOUT\n")
        print(f"TIMEOUT {rel}", flush=True)
        continue
    detail.append({"file": f, "exit": r.returncode})
    with open(os.path.join(LOG, rel.replace("/", "_") + ".log"), "w") as fh:
        fh.write("=== exit %d ===\n" % r.returncode)
        fh.write("--- stdout ---\n" + r.stdout)
        fh.write("--- stderr ---\n" + r.stderr)
    if r.returncode != 0:
        ok = False
    print(f"{r.returncode} {rel}", flush=True)

res = {"ok": ok, "files": detail, "checked_at": time.strftime('%FT%T%z')}
with open(os.path.join(LOG, "gate_replication.json"), "w") as fh:
    json.dump(res, fh, indent=2)
print("GATE_OK=%s" % ok)
