#!/usr/bin/env python3
"""D9 audit, independent gate 1 re-run: `lake env lean` on every authored .lean file
under release/ (excluding .lake and .git).

This is the *post-hoc verifier*'s own runner (separate implementation from
IndepCompile.py) used to confirm the predecessor audit's compile table.
Records per-file exit code, wall time, log tail, and source hash before/after.
Writes release/Audit/D9/logs/verify/compile.json.
"""
import concurrent.futures as cf
import hashlib
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
RELEASE = os.path.join(ROOT, "release")
OUTDIR = os.path.join(RELEASE, "Audit", "D9", "logs", "verify")
RAW = os.path.join(OUTDIR, "raw")
ELAN = os.environ.get("ELAN_HOME", "/data/home/guoshaoyang/workdir/lean_poincare/elan")
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


def run_one(rel):
    log_path = os.path.join(RAW, rel.replace("/", "__") + ".log")
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ lake env lean {rel}\n# cwd: {RELEASE}\n"
                  f"# date: {datetime.now(timezone.utc).isoformat()}\n")
        log.flush()
        p = subprocess.run(["lake", "env", "lean", rel], cwd=RELEASE,
                           stdout=log, stderr=subprocess.STDOUT, env=ENV,
                           timeout=3600)
    dt = round(time.time() - t0, 2)
    with open(log_path, errors="replace") as fh:
        lines = fh.readlines()
    return {"file": rel, "exit_code": p.returncode, "duration_s": dt,
            "log": os.path.relpath(log_path, ROOT), "output_lines": len(lines),
            "tail": "".join(lines[-20:])}


def main():
    workers = int(sys.argv[1]) if len(sys.argv) > 1 else 16
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
        "schema": "d9-adversarial-audit/verify-per-file-compile-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "cwd": RELEASE,
        "command": "lake env lean <file>",
        "workers": workers,
        "toolchain": open(os.path.join(RELEASE, "lean-toolchain")).read().strip(),
        "files_checked": len(files),
        "failures": [r["file"] for r in records if r["exit_code"] != 0],
        "source_mutations": [f for f in files if before[f] != after[f]],
        "files": records,
        "total_duration_s": round(time.time() - t_all, 1),
    }
    os.makedirs(OUTDIR, exist_ok=True)
    out = os.path.join(OUTDIR, "compile.json")
    with open(out, "w") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps({k: result[k] for k in
                      ["files_checked", "failures", "source_mutations",
                       "total_duration_s"]}, indent=1))
    print("wrote", out)
    return 1 if result["failures"] else 0


if __name__ == "__main__":
    sys.exit(main())
