#!/usr/bin/env python3
"""D9: recompile every authored .lean file under a root with `lake env lean`.

Records per-file exit code, wall time and log path; writes JSON to stdout/outfile.
"""
import hashlib
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release"
RELEASE = os.path.join(ROOT, "release")
LOGS = os.path.join(RELEASE, "Audit", "D9", "logs", "perfile")
ELAN = os.path.join("/data/home/guoshaoyang/workdir/lean_poincare", "elan")
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


def main():
    prefix = sys.argv[1] if len(sys.argv) > 1 else ""
    os.makedirs(LOGS, exist_ok=True)
    files = [f for f in leans(RELEASE) if f.startswith(prefix)]
    hashes_before = {f: sha(os.path.join(RELEASE, f)) for f in files}
    records = []
    t_all = time.time()
    for f in files:
        log_name = f.replace("/", "__") + ".log"
        log_path = os.path.join(LOGS, log_name)
        t0 = time.time()
        with open(log_path, "w") as log:
            log.write(f"$ lake env lean {f}\n# cwd: {RELEASE}\n"
                      f"# date: {datetime.now(timezone.utc).isoformat()}\n")
            log.flush()
            p = subprocess.run(["lake", "env", "lean", f], cwd=RELEASE,
                               stdout=log, stderr=subprocess.STDOUT, env=ENV)
        dt = round(time.time() - t0, 2)
        tail = "".join(open(log_path, errors="replace").readlines()[-12:])
        rec = {"file": f, "exit_code": p.returncode, "duration_s": dt,
               "log": os.path.relpath(log_path, ROOT), "tail": tail}
        records.append(rec)
        print(f"[{p.returncode}] {f} ({dt}s)", flush=True)
    hashes_after = {f: sha(os.path.join(RELEASE, f)) for f in files}
    result = {
        "schema": "d9-adversarial-audit/per-file-compile-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "cwd": RELEASE,
        "command": "lake env lean <file>",
        "toolchain": open(os.path.join(RELEASE, "lean-toolchain")).read().strip(),
        "files_checked": len(files),
        "failures": [r["file"] for r in records if r["exit_code"] != 0],
        "non_lean_mutations": [f for f in files if hashes_before[f] != hashes_after[f]],
        "files": records,
        "total_duration_s": round(time.time() - t_all, 1),
    }
    out = os.path.join(RELEASE, "Audit", "D9", "logs",
                       "perfile_compile%s.json" % (("_" + prefix.replace("/", "_")) if prefix else ""))
    json.dump(result, open(out, "w"), indent=1)
    print(json.dumps({k: result[k] for k in
                      ["files_checked", "failures", "non_lean_mutations", "total_duration_s"]}, indent=1))
    print("wrote", out)
    return 1 if result["failures"] else 0


if __name__ == "__main__":
    sys.exit(main())
