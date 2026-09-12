#!/usr/bin/env python3
"""Independent drift check of the round-8 sweep against round 7.

The round-8 summary compares whole log files modulo `###` headers and lake job
counters.  This script uses a *different* method: it extracts only the semantic
payload of each log (the `A3Probe`-generated `depends on axioms` lines, the
`A3FULL` counts/verdict, the `A3KIND` counts, and the extra probes' declaration
lines), normalizes and sorts it, and hashes it.  Hashes must agree between
rounds 7 and 8.

Output: audit360/drift_check_round8.json
"""
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
CARDS = ["D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
         "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
         "D12-surgery-recognition"]
SUFFIXES = ["probe", "fullaudit", "kind", "extraR3.ClosureUse", "extraR5.ClosureUseNonempty",
            "extraR6.ClosureUseNoninvariant", "extraR6.CurvatureNonzero",
            "extraR3.F1Validation", "extraR3.PhantomParams", "extraR3.HypRemoval"]
PATTERNS = [
    re.compile(r"depends on axioms: \[(.*)\]"),
    re.compile(r"A3FULL: \d+ declarations audited"),
    re.compile(r"A3FULL: PASS"),
    re.compile(r"A3KIND: .*"),
    re.compile(r"A3KIND-[A-Z]+: .*"),
    re.compile(r"A3UNUSED: .*"),
    re.compile(r"A3R[0-9A-Z]*\..*"),
]


def payload(path):
    if not os.path.exists(path):
        return None
    out = []
    for line in open(path, errors="replace"):
        for p in PATTERNS:
            if p.search(line):
                out.append(re.sub(r"\s+", " ", line.strip()))
                break
    out.sort()
    return hashlib.sha256("\n".join(out).encode()).hexdigest(), len(out)


def main():
    res = {"schema": "a3-drift-check-v1", "round": 8, "cards": {}, "drift": []}
    for card in CARDS:
        entry = {}
        for suf in SUFFIXES:
            a = payload(os.path.join(HERE, "logs-round7", f"{card}.{suf}.log"))
            b = payload(os.path.join(HERE, "logs-round8", f"{card}.{suf}.log"))
            if a is None and b is None:
                continue
            same = a is not None and b is not None and a[0] == b[0]
            entry[suf] = {"round7_sha": a[0] if a else None, "lines": a[1] if a else None,
                          "round8_sha": b[0] if b else None, "identical": same}
            if not same:
                res["drift"].append(f"{card}:{suf}")
        res["cards"][card] = entry
    res["verdict"] = ("PASS: normalized semantic payloads identical in all compared logs"
                      if not res["drift"] else "DRIFT: " + ", ".join(res["drift"]))
    json.dump(res, open(os.path.join(HERE, "drift_check_round8.json"), "w"), indent=1)
    n = sum(len(v) for v in res["cards"].values())
    print(json.dumps({"logs_compared": n, "drift": res["drift"], "verdict": res["verdict"]}, indent=1))
    return 1 if res["drift"] else 0


if __name__ == "__main__":
    sys.exit(main())
