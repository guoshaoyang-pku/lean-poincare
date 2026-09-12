#!/usr/bin/env python3
"""Mirror of the harness compile gate (dispatch360.compile_gate) for local checking.

Walks every .lean file under the worktree root (skipping .lake/.git/.dshpkg),
runs `lake env lean <file>` with cwd = worktree root, and reports per-file exit
codes plus wall time.
"""
import json, os, subprocess, sys, time

WT = sys.argv[1] if len(sys.argv) > 1 else os.getcwd()
ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data/home/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")

files = []
for dirpath, dirnames, filenames in os.walk(WT):
    dirnames[:] = [d for d in dirnames if d not in (".lake", ".git", ".dshpkg")]
    for fn in filenames:
        if fn.endswith(".lean"):
            files.append(os.path.join(dirpath, fn))
files.sort()

detail = []
ok = True
t0 = time.time()
for f in files:
    ts = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", f], cwd=WT, env=ENV,
                           capture_output=True, text=True, timeout=1800)
        code = r.returncode
        err = r.stderr
    except subprocess.TimeoutExpired:
        code = "timeout"
        err = ""
    dt = time.time() - ts
    detail.append({"file": f, "exit": code, "seconds": round(dt, 1)})
    if code != 0:
        ok = False
        print(f"FAIL exit={code} ({dt:.0f}s) {f}", flush=True)
        print("----- stderr -----", flush=True)
        print(err[-8000:], flush=True)
        print("------------------", flush=True)
    else:
        print(f"ok   ({dt:6.1f}s) {os.path.relpath(f, WT)}", flush=True)

res = {"ok": ok, "files": detail, "checked_at": time.strftime("%FT%T%z"),
       "total_seconds": round(time.time() - t0, 1)}
with open(os.path.join(WT, "local_gate.json"), "w") as fh:
    json.dump(res, fh, indent=2)
print(f"GATE ok={ok} files={len(files)} total={res['total_seconds']}s", flush=True)
