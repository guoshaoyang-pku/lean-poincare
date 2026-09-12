#!/usr/bin/env python3
"""Faithful replica of longrun/bin/dispatch_loop.py compile_gate, with logging."""
import json, os, subprocess, sys, time

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-gaussian-toolbox"
LOGDIR = "/tmp/d10gate"
os.makedirs(LOGDIR, exist_ok=True)

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

print(f"{len(files)} lean files", flush=True)
ok = True
detail = []
for i, f in enumerate(files):
    t0 = time.time()
    try:
        r = subprocess.run(["lake", "env", "lean", f], cwd=WT, env=ENV,
                           capture_output=True, text=True, timeout=1800)
        rc = r.returncode
        out = r.stdout + r.stderr
    except subprocess.TimeoutExpired:
        rc = "timeout"
        out = "TIMEOUT"
    dt = time.time() - t0
    detail.append({"file": f, "exit": rc, "seconds": round(dt, 1)})
    name = f.replace(WT + "/", "").replace("/", "__")
    with open(os.path.join(LOGDIR, name + ".log"), "w") as fh:
        fh.write(f"exit={rc}\nseconds={dt:.1f}\n")
        fh.write(out)
    if rc != 0:
        ok = False
        print(f"FAIL {f} exit={rc} ({dt:.1f}s)", flush=True)
        print(out[-3000:], flush=True)
    else:
        print(f"ok   {f} ({dt:.1f}s)", flush=True)

res = {"ok": ok, "files": detail, "checked_at": time.strftime('%FT%T%z')}
with open(os.path.join(LOGDIR, "gate_results.json"), "w") as fh:
    json.dump(res, fh, indent=2)
print("GATE_OK" if ok else "GATE_FAIL", flush=True)
