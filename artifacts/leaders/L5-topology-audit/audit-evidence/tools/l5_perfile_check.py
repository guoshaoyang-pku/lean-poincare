#!/usr/bin/env python3
"""L5 topology audit — authored-file compile gate.

Re-elaborates every `.lean` file under `release/` (excluding `.lake`) with the pinned
toolchain (`lake env lean`, cwd = release/) and records the exit code and wall time.
This is the per-file counterpart of `lake build`: `lake build` only covers modules reachable
from `defaultTargets`, so root modules such as `ReleaseClaims.lean` / `D6LedgerProbe.lean`
are not covered by it and only appear here.

Usage: python3 l5_perfile_check.py <release-root> <out-json> [workers]
"""
import concurrent.futures as cf
import json
import pathlib
import subprocess
import sys
import time


def main() -> int:
    rel = pathlib.Path(sys.argv[1]).resolve()
    out = pathlib.Path(sys.argv[2]).resolve()
    workers = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    files = sorted(p for p in rel.rglob("*.lean") if ".lake" not in p.parts)

    def check(p: pathlib.Path):
        t0 = time.time()
        r = subprocess.run(
            ["lake", "env", "lean", str(p.relative_to(rel))],
            cwd=rel, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        return {
            "file": "./" + str(p.relative_to(rel)),
            "exit": r.returncode,
            "seconds": round(time.time() - t0, 2),
            "output_tail": "\n".join(r.stdout.splitlines()[-4:]) if r.returncode else "",
        }

    t0 = time.time()
    results = []
    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        for res in ex.map(check, files):
            results.append(res)
            if res["exit"] != 0:
                print("FAIL", res["file"], res["exit"])
    bad = [r for r in results if r["exit"] != 0]
    summary = {
        "release_root": str(rel),
        "workers": workers,
        "files": len(results),
        "failures": len(bad),
        "failed_files": bad,
        "wall_seconds": round(time.time() - t0, 1),
        "results": results,
    }
    out.write_text(json.dumps(summary, indent=1) + "\n")
    print(f"files={len(results)} failures={len(bad)} wall={summary['wall_seconds']}s")
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
