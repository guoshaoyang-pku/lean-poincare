#!/usr/bin/env python3
"""L3-analytic-critical-path authored-file checks.

Subcommands (default: all):

  scan   comment/string-aware forbidden-token scan + sha256 of authored files
  gate   per-file `lake env lean` sweep of every .lean file under release/ (dispatcher-gate replay)
  build  `lake build` in release/ (full package)

Writes JSON evidence to audit-evidence/l3-check.json and logs to audit-evidence/logs/.
Exit code is 0 only when every enabled check passes.
"""

import argparse
import concurrent.futures
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

WORKTREE = Path(__file__).resolve().parent.parent
RELEASE = WORKTREE / "release"
EVIDENCE = WORKTREE / "audit-evidence"
LOGS = EVIDENCE / "logs"
AUTHORED_GLOB = "Poincare/L3/**/*.lean"
FORBIDDEN = ["sorry", "axiom", "admit", "unsafe", "native_decide", "proof_wanted"]

ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def strip_lean(text: str):
    """Remove nested block comments and line comments and string/char literals.

    Returns the code with comments replaced by spaces (so tokens cannot be
    smuggled inside comments and no forbidden token hides in a docstring).
    """
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        two = text[i : i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                i += 2
                continue
            if two == "-/":
                depth -= 1
                i += 2
                continue
            out.append(" " if text[i] != "\n" else "\n")
            i += 1
            continue
        if two == "/-":
            depth = 1
            out.append("  ")
            i += 2
            continue
        if two == "--":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if text[i] == '"':
            out.append('"')
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    out.append("  ")
                    i += 2
                    continue
                out.append(" " if text[i] != "\n" else "\n")
                i += 1
            if i < n:
                out.append('"')
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def run_scan():
    files = sorted(RELEASE.glob(AUTHORED_GLOB))
    records = []
    violations = []
    for path in files:
        code = strip_lean(path.read_text(encoding="utf-8"))
        hits = []
        for tok in FORBIDDEN:
            for m in re.finditer(r"(?<![A-Za-z0-9_'.])" + re.escape(tok) + r"(?![A-Za-z0-9_'])", code):
                line = code[: m.start()].count("\n") + 1
                hits.append({"token": tok, "line": line})
        rec = {
            "path": str(path.relative_to(RELEASE)),
            "sha256": sha256(path),
            "lines": path.read_text(encoding="utf-8").count("\n") + 1,
            "forbidden": hits,
        }
        records.append(rec)
        if hits:
            violations.append(rec)
    authored_ok = not violations
    return {
        "check": "authored-forbidden-scan",
        "ok": authored_ok,
        "authored_files": records,
        "violations": violations,
        "forbidden_tokens": FORBIDDEN,
    }


def run_build():
    log = LOGS / "lake-build.log"
    t0 = time.time()
    with open(log, "w") as fh:
        p = subprocess.run(["lake", "build"], cwd=RELEASE, env=ENV, stdout=fh, stderr=subprocess.STDOUT)
    return {"check": "lake-build", "ok": p.returncode == 0, "exit": p.returncode,
            "seconds": round(time.time() - t0, 1), "log": str(log.relative_to(WORKTREE))}


def run_gate(files=None, workers=8):
    if files is None:
        files = sorted(
            p for p in RELEASE.rglob("*.lean")
            if ".lake" not in p.parts
        )
    rel = [str(p.relative_to(RELEASE)) for p in files]

    def one(r):
        p = subprocess.run(["lake", "env", "lean", r], cwd=RELEASE, env=ENV,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        return r, p.returncode, (p.stdout or "")[-4000:]

    results = []
    t0 = time.time()
    with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
        for r, rc, out in ex.map(one, rel):
            results.append({"file": r, "exit": rc, "tail": out if rc != 0 else ""})
    failures = [r for r in results if r["exit"] != 0]
    return {
        "check": "per-file-gate",
        "ok": not failures,
        "files_checked": len(results),
        "failures": failures,
        "seconds": round(time.time() - t0, 1),
        "toolchain": (RELEASE / "lean-toolchain").read_text().strip(),
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--only", choices=["scan", "gate", "build"], default=None)
    ap.add_argument("--workers", type=int, default=8)
    ap.add_argument("--no-gate", action="store_true")
    args = ap.parse_args()

    LOGS.mkdir(parents=True, exist_ok=True)
    checks = []
    if args.only in (None, "scan"):
        checks.append(run_scan())
    if args.only in (None, "build"):
        checks.append(run_build())
    if args.only in (None, "gate") and not args.no_gate:
        checks.append(run_gate(workers=args.workers))

    pins = {
        "lean-toolchain": sha256(RELEASE / "lean-toolchain"),
        "lake-manifest.json": sha256(RELEASE / "lake-manifest.json"),
        "lakefile.toml": sha256(RELEASE / "lakefile.toml"),
    }
    manifest = {
        "task": "L3-analytic-critical-path",
        "generated": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "cwd": str(RELEASE),
        "pins": pins,
        "checks": checks,
        "ok": all(c["ok"] for c in checks),
    }
    out = EVIDENCE / "l3-check.json"
    out.write_text(json.dumps(manifest, indent=1) + "\n")
    print(json.dumps({c["check"]: c["ok"] for c in checks}))
    print(f"wrote {out}")
    sys.exit(0 if manifest["ok"] else 1)


if __name__ == "__main__":
    main()
