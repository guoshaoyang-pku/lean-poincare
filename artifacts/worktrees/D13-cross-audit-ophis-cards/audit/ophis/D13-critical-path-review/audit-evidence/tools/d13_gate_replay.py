#!/usr/bin/env python3
"""D13-critical-path-review — local replay of the dispatcher compile gate.

Mirrors `compile_gate` in longrun/bin/dispatch_loop.py byte-for-byte in its file
discovery, hashing and per-file elaboration, so that the result recorded here predicts
the dispatcher's next `state/D13-critical-path-review/gate.json`:

  * package        = <worktree>/release           (NOT the worktree root)
  * fingerprint    = sha256 over every .lean file under the package (skipping .lake/.git
                     and `._*`) plus lakefile.toml / lake-manifest.json / lean-toolchain
  * build          = `lake build` in the package, must exit 0
  * per-file check = `lake env lean <relative>` in the package, exit 0 required for ALL
  * verdict        = ok iff every file exits 0 and the source fingerprint is unchanged

The intentional negative-control root is deliberately OUTSIDE the package (it must fail
elaboration); see tools/d13_cp_audit.py step 04.

Usage: python3 audit-evidence/tools/d13_gate_replay.py
Writes: audit-evidence/gate-replay.json  (and gate-replay.log)
"""
import concurrent.futures
import hashlib
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PACKAGE = os.path.join(WT, "release")
EVID = os.path.join(WT, "audit-evidence")


def source_hash(package):
    """Byte-identical copy of dispatch_loop.source_hash (Path objects, Path sort order).

    The sort order matters: `Path` ordering is by parts, so `Poincare/D12/X.lean`
    precedes `Poincare/D12/X/...`, whereas a plain string sort would not.
    """
    package = Path(package)
    digest = hashlib.sha256()
    files = []
    for directory, directories, names in os.walk(package):
        directories[:] = sorted(name for name in directories if name not in (".lake", ".git"))
        files.extend(Path(directory) / name for name in sorted(names)
                     if name.endswith(".lean") and not name.startswith("._"))
    files.sort()
    for path in files + [package / name for name in
                         ("lakefile.toml", "lake-manifest.json", "lean-toolchain")
                         if (package / name).exists()]:
        digest.update(str(path.relative_to(package)).encode())
        digest.update(path.read_bytes())
    return digest.hexdigest(), files


def main():
    fingerprint, files = source_hash(PACKAGE)
    started = time.time()
    result = {
        "task_id": "D13-critical-path-review",
        "replay_of": "longrun/bin/dispatch_loop.py::compile_gate",
        "generated_utc": datetime.now(timezone.utc).isoformat(),
        "package": PACKAGE,
        "source_sha256": fingerprint,
        "lean_files": len(files),
        "ok": False,
        "files": [],
    }
    build = subprocess.run(["lake", "build"], cwd=PACKAGE,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=3600)
    result["build_exit"] = build.returncode
    result["build_tail"] = build.stdout.decode(errors="replace")[-2000:]
    if build.returncode != 0:
        result["error"] = "Package build failed"
        with open(os.path.join(EVID, "gate-replay.json"), "w") as handle:
            json.dump(result, handle, indent=1)
        return 1

    def check_file(path):
        relative = str(path.relative_to(PACKAGE))
        try:
            checked = subprocess.run(["lake", "env", "lean", relative], cwd=PACKAGE,
                                     capture_output=True, text=True, timeout=900)
            diagnostic = checked.stdout + checked.stderr
            return {"file": relative, "exit": checked.returncode,
                    "diagnostic": diagnostic[-12000:] if checked.returncode else ""}
        except subprocess.TimeoutExpired:
            return {"file": relative, "exit": "timeout", "diagnostic": ""}

    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
        result["files"] = list(executor.map(check_file, files))
    result["ok"] = all(item["exit"] == 0 for item in result["files"])
    if source_hash(PACKAGE)[0] != fingerprint:
        result["ok"] = False
        result["error"] = "Sources changed while replay was running"
    result["elapsed_seconds"] = round(time.time() - started, 1)
    bad = [item for item in result["files"] if item["exit"] != 0]
    result["nonzero_exits"] = len(bad)
    with open(os.path.join(EVID, "gate-replay.json"), "w") as handle:
        json.dump(result, handle, indent=1)
    with open(os.path.join(EVID, "gate-replay.log"), "w") as handle:
        handle.write(f"# package: {PACKAGE}\n# source_sha256: {fingerprint}\n")
        handle.write(f"# files: {len(files)}  build_exit: {build.returncode}  "
                     f"ok: {result['ok']}  elapsed: {result['elapsed_seconds']}s\n")
        for item in bad:
            handle.write(f"NONZERO {item['file']} exit={item['exit']}\n")
            handle.write(item["diagnostic"] + "\n")
    print(json.dumps({"ok": result["ok"], "files": len(files),
                      "build_exit": build.returncode,
                      "nonzero_exits": [(b["file"], b["exit"]) for b in bad],
                      "source_sha256": fingerprint,
                      "elapsed_seconds": result["elapsed_seconds"]}, indent=1))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
