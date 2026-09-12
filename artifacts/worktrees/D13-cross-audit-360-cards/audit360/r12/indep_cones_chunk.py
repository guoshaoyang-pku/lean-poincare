#!/usr/bin/env python3
"""Chunked full-namespace independent cone run (round-12 wall-clock rescue).

Renders `A3ExtraR12/IndepConesChunk.lean` for one (card, chunk k of N) pair and runs
it.  The Lean file enumerates every constant under `Poincare.D12` in environment order
and keeps those with `index % N == k`; because cones are computed per root, the union of
the N chunks is exactly the full-namespace cone table (only the cross-root memo sharing
is lost).  Chunks can run in parallel; `indep_cones_merge.py` combines them.

Usage: python3 audit360/r12/indep_cones_chunk.py <card> <k> <N>
Env: A3R12C_TIMEOUT (default 10800)
"""
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(os.path.dirname(HERE))
PKGS = os.path.join(WT, "audit360", "pkgs")
TEMPLATE = os.path.join(HERE, "IndepConesChunkTemplate.lean")
CONE = re.compile(r"A3R12CONE\|([^|]+)\|([^|]*)\|(\d+)")
ENV = dict(os.environ)
ENV["ELAN_HOME"] = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV["PATH"] = ENV["ELAN_HOME"] + "/bin:" + ENV.get("PATH", "")


def main():
    card, k, n = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    pkg = os.path.join(PKGS, card)
    imports = [l.rstrip("\n") for l in open(os.path.join(pkg, "A3FullAudit.lean"),
                                            encoding="utf-8") if l.startswith("import ")]
    tpl = open(TEMPLATE, encoding="utf-8").read().replace("NCHUNK", str(n)).replace("KCHUNK", str(k))
    src = "\n".join(imports) + "\n\n" + tpl
    outdir = os.path.join(pkg, "A3ExtraR12")
    os.makedirs(outdir, exist_ok=True)
    fname = f"IndepConesChunk_{k}.lean"
    path = os.path.join(outdir, fname)
    open(path, "w", encoding="utf-8").write(src)
    sha = hashlib.sha256(src.encode()).hexdigest()
    log = os.path.join(HERE, f"indep_cones_chunk_{card}_{k}of{n}.log")
    rc = None
    with open(log, "w", encoding="utf-8") as fh:
        try:
            proc = subprocess.run(["lake", "env", "lean", f"A3ExtraR12/{fname}"],
                                  cwd=pkg, stdout=fh, stderr=subprocess.STDOUT, env=ENV,
                                  timeout=int(os.environ.get("A3R12C_TIMEOUT", "10800")))
            rc = proc.returncode
        except subprocess.TimeoutExpired:
            rc = -99
    text = open(log, errors="replace").read()
    cones = {}
    for m in CONE.finditer(text):
        cones[m.group(1)] = {"axioms": [a for a in m.group(2).split(",") if a], "visited": 0}
    total = re.search(r"A3R12 TOTAL (\d+) declarations, memo size (\d+)", text)
    out = {"card": card, "chunk": k, "nchunks": n, "rc": rc, "lean_sha256": sha,
           "lean_file": os.path.relpath(path, WT),
           "selftest_pass": "A3R12 SELFTEST PASS" in text,
           "pass": "A3R12 PASS" in text,
           "declarations": int(total.group(1)) if total else None,
           "memo_size": int(total.group(2)) if total else None,
           "cones": cones}
    with open(os.path.join(HERE, f"indep_cones_chunk_{card}_{k}of{n}.json"), "w",
              encoding="utf-8") as fh:
        json.dump(out, fh, indent=1, sort_keys=True)
    print(f"{card} chunk {k}/{n}: rc={rc} pass={out['pass']} decls={out['declarations']} "
          f"cones={len(cones)} memo={out['memo_size']}")
    return 0 if out["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
