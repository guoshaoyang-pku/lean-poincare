#!/usr/bin/env python3
"""Replicate the harness compile_gate (each file: `lake env lean <file>`, cwd = worktree root)
with a parallel worker pool. Same per-file command and exit-code criterion as the sequential
harness gate; parallelism only removes wall-clock serialisation.
"""
import json, os, subprocess, time
from concurrent.futures import ThreadPoolExecutor

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-levi-civita-smoothness"
LOG = os.path.join(WT, "longrun", "logs", "gate")
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


def check(f):
    rel = os.path.relpath(f, WT)
    try:
        r = subprocess.run(["lake", "env", "lean", f], cwd=WT, env=ENV,
                           capture_output=True, text=True, timeout=1800)
        code = r.returncode
        out = r.stdout
        err = r.stderr
    except subprocess.TimeoutExpired:
        code = "timeout"
        out = ""
        err = "TIMEOUT\n"
    with open(os.path.join(LOG, rel.replace("/", "_") + ".log"), "w") as fh:
        fh.write("=== exit %s ===\n" % code)
        fh.write("--- stdout ---\n" + out)
        fh.write("--- stderr ---\n" + err)
    print("%s %s" % (code, rel), flush=True)
    return {"file": f, "exit": code}


with ThreadPoolExecutor(max_workers=12) as ex:
    detail = list(ex.map(check, files))

ok = all(d["exit"] == 0 for d in detail)
res = {"ok": ok, "files": detail, "checked_at": time.strftime('%FT%T%z')}
with open(os.path.join(LOG, "gate_replication.json"), "w") as fh:
    json.dump(res, fh, indent=2)
print("GATE_OK=%s" % ok)
