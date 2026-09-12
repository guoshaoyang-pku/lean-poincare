#!/usr/bin/env python3
"""SEMREV-L5 independent per-file elaboration replay.

Runs `lean <file>` (no -o: elaborates, writes nothing) for every authored .lean file
of the L5 union release, with the reviewer's LEAN_PATH.  Independent of the L5
per-file checker (own implementation, own worker pool).
"""
import concurrent.futures as cf
import json
import os
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
L5 = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L5-topology-audit"
REL = os.path.join(L5, "release")
LEANBIN = "/data3/guoshaoyang/workdir/lean_poincare/elan/toolchains/leanprover--lean4---v4.34.0-rc2/bin/lean"
LEANPATH = open(os.path.join(ROOT, "evidence", "leanpath.txt")).read().strip()
WORKERS = 12


def files():
    out = []
    for root, dirs, fs in os.walk(REL):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in fs:
            if f.endswith(".lean"):
                out.append(os.path.join(root, f))
    return sorted(out)


def check(p):
    t0 = time.time()
    try:
        r = subprocess.run(
            [LEANBIN, "-R", REL, p],
            cwd=REL,
            env={**os.environ, "LEAN_PATH": LEANPATH},
            capture_output=True,
            text=True,
            timeout=1800,
        )
        return (p, r.returncode, time.time() - t0, r.stdout[-4000:], r.stderr[-4000:])
    except subprocess.TimeoutExpired:
        return (p, 124, time.time() - t0, "", "timeout")


def main():
    fs = files()
    print(f"per-file elaboration replay: {len(fs)} files, {WORKERS} workers", flush=True)
    t0 = time.time()
    results = []
    with cf.ThreadPoolExecutor(max_workers=WORKERS) as ex:
        for i, r in enumerate(ex.map(check, fs)):
            results.append(r)
            if (i + 1) % 50 == 0:
                print(f"  {i+1}/{len(fs)} done ({time.time()-t0:.0f}s)", flush=True)
    bad = [r for r in results if r[1] != 0]
    out = {
        "files": len(fs),
        "failures": len(bad),
        "wall_seconds": round(time.time() - t0, 1),
        "lean_path_entries": len(LEANPATH.split(":")),
        "failed_files": [
            {"file": os.path.relpath(p, REL), "exit": c, "stderr": e[-1500:]} for p, c, _t, _o, e in bad
        ],
    }
    os.makedirs(os.path.join(ROOT, "logs"), exist_ok=True)
    with open(os.path.join(ROOT, "logs", "perfile-replay.json"), "w") as f:
        json.dump(out, f, indent=1)
    with open(os.path.join(ROOT, "logs", "perfile-replay.full.txt"), "w") as f:
        for p, c, t, o, e in results:
            f.write(f"=== {os.path.relpath(p, REL)} exit={c} {t:.1f}s\n")
            if c != 0:
                f.write(o + "\n" + e + "\n")
    print(json.dumps({k: v for k, v in out.items() if k != "failed_files"}, indent=1))
    if bad:
        print("FAILED:", [os.path.relpath(p, REL) for p, _c, _t, _o, _e in bad])
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
