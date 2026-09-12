#!/usr/bin/env python3
"""Round-8 (invocation 7) close-out: compare the round-10 sweep outputs with round 7
byte-for-byte (ignoring `###` header lines and lake's `[k/N]` job counters) and
emit audit360/round10_summary.json.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
LOGS = os.path.join(HERE, "logs-round10")
PREV = os.path.join(HERE, "logs-round8")
KINDPREV = os.path.join(HERE, "logs-round8")
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
    out = []
    with open(path, errors="replace") as f:
        for line in f:
            if line.startswith("###"):
                continue
            out.append(COUNTER.sub("[k/N]", line))
    return "".join(out)


def rc(name):
    p = os.path.join(LOGS, name + ".rc")
    if not os.path.exists(p):
        return None
    return int(open(p).read().strip().split("=")[-1])


def main():
    summary = {"round": 10, "invocation": 7,
               "generated_by": "audit360/round10_summary.py",
               "logs": "audit360/logs-round10", "compared_to": "audit360/logs-round8"}
    cards = {}
    for card in CARDS:
        entry = {}
        for suffix in ("build", "probe", "fullaudit", "kind"):
            p6 = os.path.join(LOGS, f"{card}.{suffix}.log")
            p5 = os.path.join(PREV, f"{card}.{suffix}.log")
            if suffix == "kind":
                p5 = os.path.join(KINDPREV, f"{card}.kind.log")
            entry[f"{suffix}_rc"] = rc(f"{card}.{suffix}")
            entry[f"{suffix}_identical_to_round8"] = (
                os.path.exists(p5) and os.path.exists(p6)
                and strip_headers(p6) == strip_headers(p5)
            )
            if suffix == "probe":
                entry["probe_cone_lines"] = sum(
                    1 for l in open(p6) if re.match(r"^Poincare\.", l))
            if suffix == "fullaudit":
                entry["fullaudit_declarations"] = None
                for l in open(p6):
                    m = re.search(r"A3FULL: (\d+) declarations", l)
                    if m:
                        entry["fullaudit_declarations"] = int(m.group(1))
                    if "A3FULL: PASS" in l:
                        entry["fullaudit_verdict"] = "PASS"
        # extras present in this sweep
        extras = {}
        for fn in sorted(os.listdir(LOGS)):
            if fn.startswith(card + ".extra") and fn.endswith(".rc"):
                extras[fn[len(card) + 1:-3]] = int(open(os.path.join(LOGS, fn)).read().strip().split("=")[-1])
        entry["extras_rc"] = extras
        cards[card] = entry
    summary["cards"] = cards
    summary["total_cones"] = sum(c.get("probe_cone_lines", 0) for c in cards.values())
    summary["total_declarations"] = sum(
        (c.get("fullaudit_declarations") or 0) for c in cards.values())
    summary["all_core_rc_zero"] = all(
        c["build_rc"] == 0 and c["probe_rc"] == 0 and c["fullaudit_rc"] == 0
        and c["kind_rc"] == 0 for c in cards.values())
    summary["all_core_identical_to_round8"] = all(
        c["build_identical_to_round8"] and c["probe_identical_to_round8"]
        and c["fullaudit_identical_to_round8"] and c["kind_identical_to_round8"]
        for c in cards.values())
    summary["negative_control"] = open(os.path.join(LOGS, "negative_control.log")).read()
    summary["snapshot_build_rc"] = rc("D12-semantic-ledger-snapshot.build")
    summary["snapshot_probe_rc"] = rc("D12-semantic-ledger-snapshot.extra.D12RealModuleProbe")
    summary["a3d2d3_build_rc"] = rc("a3d2d3.build")
    summary["a3d2d3_probe_rc"] = rc("a3d2d3.probe")
    summary["a3d2d3_round3_rc"] = rc("a3d2d3.round3")
    with open(os.path.join(HERE, "round10_summary.json"), "w") as f:
        json.dump(summary, f, indent=1)
    print(json.dumps(summary, indent=1))


if __name__ == "__main__":
    main()
