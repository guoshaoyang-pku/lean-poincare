#!/usr/bin/env python3
"""Replicate the dispatcher compile gate's per-file stage, independently of the
dispatcher's (cached) gate.json.

Stage 1: `lake build` in release/  (recorded separately in
         review/logs/repair-lake-build.log, EXIT=0, 8946 jobs).
Stage 2: `lake env lean <file>` for every authored .lean file under release/,
         exactly as longrun/bin/dispatch_loop.py:check_file does.

Output: review/logs/gate-replication.json (summary + per-file exits).
This script only reads the release package and writes under review/.
"""
import concurrent.futures
import json
import os
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent          # worktree root
PACKAGE = ROOT / "release"
OUT = ROOT / "review/logs/gate-replication.json"

ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = (str(Path.home() / ".local/node/bin") + ":"
               + ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", ""))
ENV.setdefault("TMPDIR", str(Path.home() / "tmp"))


def source_files():
    files = []
    for directory, directories, names in os.walk(PACKAGE):
        directories[:] = sorted(d for d in directories if d not in (".lake", ".git"))
        files.extend(Path(directory) / n for n in sorted(names)
                     if n.endswith(".lean") and not n.startswith("._"))
    files.sort()
    return files


def check_file(path):
    relative = str(path.relative_to(PACKAGE))
    try:
        checked = subprocess.run(["lake", "env", "lean", relative],
                                 cwd=PACKAGE, env=ENV, capture_output=True,
                                 text=True, timeout=900)
        diagnostic = checked.stdout + checked.stderr
        return {"file": relative, "exit": checked.returncode,
                "diagnostic": diagnostic[-4000:] if checked.returncode else ""}
    except subprocess.TimeoutExpired:
        return {"file": relative, "exit": "timeout", "diagnostic": ""}


def main():
    files = source_files()
    started = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(check_file, files))
    failures = [item for item in results if item["exit"] != 0]
    summary = {
        "gate_stage": "per-file `lake env lean` (dispatch_loop.compile_gate replica)",
        "cwd": str(PACKAGE),
        "files": len(files),
        "failures": len(failures),
        "wall_seconds": round(time.time() - started, 1),
        "exit_histogram": {str(code): sum(1 for i in results if i["exit"] == code)
                           for code in sorted({i["exit"] for i in results}, key=str)},
        "failed": [{"file": i["file"], "diagnostic": i["diagnostic"][-800:]}
                   for i in failures],
        "checked_at": time.strftime("%FT%T%z"),
    }
    OUT.write_text(json.dumps({"summary": summary, "results": results}, indent=1) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
