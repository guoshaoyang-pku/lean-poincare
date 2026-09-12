#!/usr/bin/env python3
"""SEMREV-L5 independent forbidden-token scan of the union release.

Own lexer: strips nested block comments, line comments and string literals, then
counts whole-word tokens.  Deliberately independent of L5's l5_forbidden_scan.py.
"""
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
L5 = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L5-topology-audit"
REL = os.path.join(L5, "release")

TOKENS = ["sorry", "admit", "axiom", "unsafe", "native_decide", "proof_wanted", "sorryAx"]


def strip_lean(src: str) -> str:
    out = []
    i = 0
    n = len(src)
    depth = 0  # block comment depth
    while i < n:
        c = src[i]
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                i += 2
            elif src.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if c == "\n":
                    out.append("\n")
                i += 1
            continue
        if src.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        if c == '"':
            i += 1
            while i < n:
                if src[i] == "\\":
                    i += 2
                    continue
                if src[i] == '"':
                    i += 1
                    break
                if src[i] == "\n":
                    out.append("\n")
                i += 1
            out.append('""')
            continue
        out.append(c)
        i += 1
    return "".join(out)


def main():
    hits = []
    files = []
    for root, dirs, fs in os.walk(REL):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for f in fs:
            if f.endswith(".lean"):
                files.append(os.path.join(root, f))
    files.sort()
    per_token = {t: 0 for t in TOKENS}
    for p in files:
        src = open(p, encoding="utf-8").read()
        clean = strip_lean(src)
        rel = "./" + os.path.relpath(p, REL)
        for t in TOKENS:
            for m in re.finditer(rf"(?<![A-Za-z0-9_']){re.escape(t)}(?![A-Za-z0-9_'])" if t != "sorryAx" else r"sorryAx", clean):
                line = clean.count("\n", 0, m.start()) + 1
                per_token[t] += 1
                hits.append({"file": rel, "line": line, "token": t})
    report = {"files": len(files), "per_token": per_token, "hits": hits}
    with open(os.path.join(ROOT, "evidence", "forbidden-scan-replay.json"), "w") as f:
        json.dump(report, f, indent=1)
    print(json.dumps({"files": len(files), "per_token": per_token}, indent=1))
    for h in hits:
        print(f"{h['file']}:{h['line']}: {h['token']}")


if __name__ == "__main__":
    main()
