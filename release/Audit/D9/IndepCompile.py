#!/usr/bin/env python3
"""D9 independent gate 1: recompile every authored .lean file under release/ (excl .lake).

Runs `lake env lean <file>` from cwd=release/ with a process pool, records per-file
exit code / wall time / output tail, and verifies sources were not mutated.
Writes logs to release/Audit/D9/logs/d9b/compile.json.
"""
import concurrent.futures as cf
import hashlib
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release"
RELEASE = os.path.join(ROOT, "release")
OUTDIR = os.path.join(RELEASE, "Audit", "D9", "logs", "d9b")
RAW = os.path.join(OUTDIR, "raw")
ELAN = "/data/home/guoshaoyang/workdir/lean_poincare/elan"
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=f"{ELAN}/bin:" + os.environ["PATH"])


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def leans(root):
    out = []
    for dp, dn, fn in os.walk(root):
        dn[:] = [d for d in dn if d not in (".lake", ".git")]
        for f in fn:
            if f.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(dp, f), root))
    return sorted(out)


def run_one(f):
    rel = f
    log_name = f.replace("/", "__") + ".log"
    log_path = os.path.join(RAW, log_name)
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ lake env lean {rel}\n# cwd: {RELEASE}\n"
                  f"# date: {datetime.now(timezone.utc).isoformat()}\n")
        log.flush()
        p = subprocess.run(["lake", "env", "lean", rel], cwd=RELEASE,
                           stdout=log, stderr=subprocess.STDOUT, env=ENV)
    dt = round(time.time() - t0, 2)
    with open(log_path, errors="replace") as fh:
        lines = fh.readlines()
    return {
        "file": rel,
        "exit_code": p.returncode,
        "duration_s": dt,
        "log": os.path.relpath(log_path, ROOT),
        "output_lines": len(lines),
        "tail": "".join(lines[-15:]),
    }


def main():
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    tag = sys.argv[2] if len(sys.argv) > 2 else ""
    global RAW
    RAW = os.path.join(OUTDIR, "raw" + tag)
    os.makedirs(RAW, exist_ok=True)
    files = leans(RELEASE)
    before = {f: sha(os.path.join(RELEASE, f)) for f in files}
    t_all = time.time()
    records = []
    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        futs = {ex.submit(run_one, f): f for f in files}
        for fut in cf.as_completed(futs):
            rec = fut.result()
            records.append(rec)
            print(f"[{rec['exit_code']}] {rec['file']} ({rec['duration_s']}s)", flush=True)
    records.sort(key=lambda r: r["file"])
    after = {f: sha(os.path.join(RELEASE, f)) for f in files}
    result = {
        "schema": "d9-adversarial-audit/indep-per-file-compile-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "cwd": RELEASE,
        "command": "lake env lean <file>",
        "workers": workers,
        "toolchain": open(os.path.join(RELEASE, "lean-toolchain")).read().strip(),
        "files_checked": len(files),
        "failures": [r["file"] for r in records if r["exit_code"] != 0],
        "non_lean_mutations": [f for f in files if before[f] != after[f]],
        "files": records,
        "total_duration_s": round(time.time() - t_all, 1),
    }
    out = os.path.join(OUTDIR, "compile%s.json" % tag)
    with open(out, "w") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps({k: result[k] for k in
                      ["files_checked", "failures", "non_lean_mutations", "total_duration_s"]}, indent=1))
    print("wrote", out)
    return 1 if result["failures"] else 0


if __name__ == "__main__":
    sys.exit(main())
