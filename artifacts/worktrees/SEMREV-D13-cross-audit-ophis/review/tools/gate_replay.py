#!/usr/bin/env python3
"""Independent replication of the dispatcher compile gate for this worktree.

The dispatcher caches its gate result in longrun/state/<task>/gate.json keyed by
the release package's source hash.  The recorded entry (checked_at
2026-09-12T00:38:12+0800) failed for an *environmental* reason: the transported
release/.lake/packages was an empty directory, so `lake build` tried to clone
mathlib from the (blocked) network and failed.  That cache entry can only be
invalidated from outside the session sandbox, which is not permitted.  This
script therefore replays both gate stages exactly as
longrun/bin/dispatch_loop.py:compile_gate does, from inside the worktree:

  stage 1: `lake build` in release/                     -> review/logs/gate-replay-build.log
  stage 2: `lake env lean <relative>` for every authored .lean file under
           release/ (same file walk, same cwd, same env, 4 workers)
  plus:    re-compute the source fingerprint with the dispatcher's own
           algorithm and compare it with the cached gate.json entry.

It only reads release/ and writes under review/.
"""
import concurrent.futures
import hashlib
import json
import os
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent          # worktree root
PACKAGE = ROOT / "release"
STATE_GATE = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/state/"
                  "SEMREV-D13-cross-audit-ophis/gate.json")
LOG_DIR = ROOT / "review/logs"
BUILD_LOG = LOG_DIR / "gate-replay-build.log"
OUT = LOG_DIR / "gate-replication.json"

ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = (str(Path.home() / ".local/node/bin") + ":"
               + ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", ""))
ENV.setdefault("TMPDIR", str(Path.home() / "tmp"))


def source_hash(package):
    """Byte-for-byte copy of dispatch_loop.source_hash (v2 gate)."""
    digest = hashlib.sha256()
    files = []
    for directory, directories, names in os.walk(package):
        directories[:] = sorted(name for name in directories
                                if name not in (".lake", ".git"))
        files.extend(Path(directory) / name for name in sorted(names)
                     if name.endswith(".lean") and not name.startswith("._"))
    files.sort()
    for path in files + [package / name for name in
                         ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
                         if (package / name).exists()]:
        digest.update(str(path.relative_to(package)).encode())
        digest.update(path.read_bytes())
    return digest.hexdigest(), files


def check_file(path):
    relative = str(path.relative_to(PACKAGE))
    try:
        checked = subprocess.run(["lake", "env", "lean", relative],
                                 cwd=PACKAGE, env=ENV, capture_output=True,
                                 text=True, timeout=900)
        diagnostic = checked.stdout + checked.stderr
        return {"file": relative, "exit": checked.returncode,
                "diagnostic": diagnostic[-12000:] if checked.returncode else ""}
    except subprocess.TimeoutExpired:
        return {"file": relative, "exit": "timeout", "diagnostic": ""}


def main():
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    fingerprint_before, files = source_hash(PACKAGE)

    started = time.time()
    with BUILD_LOG.open("w") as output:
        build = subprocess.run(["lake", "build"], cwd=PACKAGE, env=ENV,
                               stdout=output, stderr=subprocess.STDOUT,
                               timeout=3600)
    build_seconds = round(time.time() - started, 1)

    started = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        results = list(executor.map(check_file, files))
    files_seconds = round(time.time() - started, 1)

    fingerprint_after, _ = source_hash(PACKAGE)

    cached = json.loads(STATE_GATE.read_text()) if STATE_GATE.exists() else {}
    failures = [item for item in results if item["exit"] != 0]
    summary = {
        "gate_replica_of": "longrun/bin/dispatch_loop.py:compile_gate (GATE_VERSION 2)",
        "cwd": str(PACKAGE),
        "fingerprint_before": fingerprint_before,
        "fingerprint_after": fingerprint_after,
        "sources_stable": fingerprint_before == fingerprint_after,
        "dispatcher_cached_gate": {
            "source_sha256": cached.get("source_sha256"),
            "fingerprint_matches_now": cached.get("source_sha256") == fingerprint_before,
            "ok": cached.get("ok"),
            "build_exit": cached.get("build_exit"),
            "error": cached.get("error"),
            "checked_at": cached.get("checked_at"),
            "note": ("cached failure records the pre-repair transport state "
                     "(empty .lake/packages); it is keyed to this same unchanged "
                     "fingerprint, so the dispatcher would return it without "
                     "re-running the build"),
        },
        "build": {
            "exit": build.returncode,
            "wall_seconds": build_seconds,
            "log": str(BUILD_LOG.relative_to(ROOT)),
            "log_tail": BUILD_LOG.read_text(errors="replace")[-400:],
        },
        "per_file": {
            "files": len(files),
            "failures": len(failures),
            "wall_seconds": files_seconds,
            "exit_histogram": {str(code): sum(1 for i in results if i["exit"] == code)
                               for code in sorted({i["exit"] for i in results}, key=str)},
            "failed": [{"file": i["file"], "diagnostic": i["diagnostic"][-800:]}
                       for i in failures],
        },
        "checked_at": time.strftime("%FT%T%z"),
    }
    summary["gate_ok_replicated"] = (
        build.returncode == 0 and not failures
        and fingerprint_before == fingerprint_after)
    OUT.write_text(json.dumps({"summary": summary, "results": results}, indent=1) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
