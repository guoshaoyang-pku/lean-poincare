#!/usr/bin/env python3
"""Independent drift check of the round-12 sweep against round 11 (all nine cards).

The round-12 summary compares whole log files modulo `###` headers and lake job
counters.  This script uses a *different* method: it extracts only the semantic
payload of each log (the `depends on axioms` rows, the `A3FULL` counts/verdicts,
the `A3KIND` rows and summaries, the `A3UNUSED`/`A3R*` audit lines), normalizes,
sorts and hashes it.  Hashes must agree between round 11 and round 12.

Output: audit360/r12/drift_check_round12.json
"""
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
AUD = os.path.dirname(HERE)
CARDS = ["D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
         "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
         "D12-surgery-recognition", "D12-triangulation-topology",
         "D12-tensor-maximum-bochner"]
SUFFIXES = ["probe", "fullaudit", "kind"]
PATTERNS = [
    re.compile(r"depends on axioms: \[(.*)\]"),
    re.compile(r"A3FULL: \d+ declarations audited"),
    re.compile(r"A3FULL: PASS"),
    re.compile(r"A3KIND: .*"),
    re.compile(r"A3KIND-[A-Z]+: .*"),
    re.compile(r"A3UNUSED: .*"),
    re.compile(r"A3UNUSED-FLAG: .*"),
    re.compile(r"A3TAUT: .*"),
    re.compile(r"A3TAUT-FLAG: .*"),
]
SCREEN_BASELINE = {
    "D12-connection-curvature": "logs-round3", "D12-volume-ibp": "logs-round3",
    "D12-spectral-sobolev": "logs-round3", "D12-semantic-ledger": "logs-round3",
    "D12-comparison-geodesics": "logs-round3", "D12-geometric-compactness": "logs-round3",
    "D12-surgery-recognition": "logs-round3",
    "D12-triangulation-topology": "logs-round11", "D12-tensor-maximum-bochner": "logs-round11",
}


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
    res = {"schema": "a3-drift-check-v1", "round": 12, "compared_to": 11,
           "cards": {}, "drift": []}
    for card in CARDS:
        entry = {}
        for suf in SUFFIXES:
            a = payload(os.path.join(AUD, "logs-round12", f"{card}.{suf}.log"))
            b = payload(os.path.join(AUD, "logs-round11", f"{card}.{suf}.log"))
            if a is None or b is None:
                entry[suf] = {"r12": a, "r11": b, "identical": None}
                continue
            same = a[0] == b[0]
            entry[suf] = {"r12_sha": a[0][:16], "r11_sha": b[0][:16], "lines": a[1],
                          "identical": same}
            if not same:
                res["drift"].append(f"{card}.{suf}: {a[0][:12]} != {b[0][:12]}")
        res["cards"][card] = entry
    # supplementary screens (taut / unused-hypothesis) against their nearest baseline
    res["screens"] = {}
    for card in CARDS:
        base = SCREEN_BASELINE[card]
        entry = {}
        for suf in ("tautscreen", "unusedhyp", "unusedhypfull"):
            a = payload(os.path.join(AUD, "logs-round12", f"{card}.{suf}.log"))
            b = payload(os.path.join(AUD, base, f"{card}.{suf}.log"))
            if a is None:
                entry[suf] = {"r12": None}
            elif b is None:
                entry[suf] = {"r12_sha": a[0][:16], "lines": a[1], "baseline": None}
            else:
                entry[suf] = {"r12_sha": a[0][:16], "baseline_sha": b[0][:16], "lines": a[1],
                              "baseline": base, "identical": a[0] == b[0]}
                if a[0] != b[0]:
                    res["drift"].append(f"screen {card}.{suf}: differs from {base}")
        res["screens"][card] = entry

    res["verdict"] = "PASS" if not res["drift"] else "DRIFT"
    json.dump(res, open(os.path.join(HERE, "drift_check_round12.json"), "w",
                        encoding="utf-8"), indent=1, sort_keys=True)
    n = sum(1 for c in CARDS for s in SUFFIXES if res["cards"][c][s].get("identical"))
    print(f"payload-identical logs: {n}/{len(CARDS) * len(SUFFIXES)}")
    print("drift:", res["drift"])
    print("verdict:", res["verdict"])
    return 0 if not res["drift"] else 1


if __name__ == "__main__":
    sys.exit(main())
