#!/usr/bin/env python3
"""Round-5 close-out: compare the round-5 sweep outputs with round 4 byte-for-byte
(ignoring `###` header lines, which carry timestamps), and emit round5_summary.json.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
LOGS = os.path.join(HERE, "logs-round5")
PREV = os.path.join(HERE, "logs-round4")
CARDS = [
    "D12-connection-curvature",
    "D12-volume-ibp",
    "D12-spectral-sobolev",
    "D12-semantic-ledger",
    "D12-comparison-geodesics",
    "D12-geometric-compactness",
    "D12-surgery-recognition",
]


COUNTER = re.compile(r"\[\d+/\d+\]")


def strip_headers(path):
    """Drop `###` header lines (timestamps) and lake's `[k/N]` job counters."""
    out = []
    with open(path, errors="replace") as f:
        for line in f:
            if line.startswith("###"):
                continue
            out.append(COUNTER.sub("[k/N]", line))
    return "".join(out)


def main():
    summary = {"round": 5, "generated_by": "audit360/round5_summary.py"}
    cards = {}
    for card in CARDS:
        entry = {}
        for suffix in ("build", "probe", "fullaudit"):
            p5 = os.path.join(LOGS, f"{card}.{suffix}.log")
            p4 = os.path.join(PREV, f"{card}.{suffix}.log")
            rc5 = open(os.path.join(LOGS, f"{card}.{suffix}.rc")).read().strip()
            entry[f"{suffix}_rc"] = int(rc5)
            entry[f"{suffix}_identical_to_round4"] = (
                os.path.exists(p4) and strip_headers(p5) == strip_headers(p4)
            )
            if suffix == "probe":
                entry["probe_cone_lines"] = sum(
                    1 for l in open(p5) if re.match(r"^Poincare\.", l)
                )
            if suffix == "fullaudit":
                entry["fullaudit_declarations"] = None
                for l in open(p5):
                    m = re.search(r"A3FULL: (\d+) declarations", l)
                    if m:
                        entry["fullaudit_declarations"] = int(m.group(1))
                    if "A3FULL: PASS" in l:
                        entry["fullaudit_verdict"] = "PASS"
        cards[card] = entry
    summary["cards"] = cards
    summary["total_cones"] = sum(c.get("probe_cone_lines", 0) for c in cards.values())
    summary["total_declarations"] = sum(
        (c.get("fullaudit_declarations") or 0) for c in cards.values()
    )
    summary["all_rc_zero"] = all(
        c["build_rc"] == 0 and c["probe_rc"] == 0 and c["fullaudit_rc"] == 0
        for c in cards.values()
    )
    summary["all_identical_to_round4"] = all(
        c["build_identical_to_round4"]
        and c["probe_identical_to_round4"]
        and c["fullaudit_identical_to_round4"]
        for c in cards.values()
    )
    with open(os.path.join(HERE, "round5_summary.json"), "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
