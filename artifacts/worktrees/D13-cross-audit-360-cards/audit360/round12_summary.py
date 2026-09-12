#!/usr/bin/env python3
"""Round-12 (invocation 9) close-out: compare the round-12 sweep outputs with round 11
byte-for-byte (ignoring `###` header lines and lake's `[k/N]` job counters) and emit
audit360/round12_summary.json.

The seven original cards have a round-11 log set (logs-round11).  The two late cards
(triangulation-topology, tensor-maximum-bochner) were audited in round 11 from ad-hoc
logs under audit360/r11/; their round-12 numbers are recorded and cross-checked against
the round-11 counts instead of a byte diff.
"""
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
LOGS = os.path.join(HERE, "logs-round12")
PREV = os.path.join(HERE, "logs-round11")
CARDS7 = [
    "D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
    "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
    "D12-surgery-recognition",
]
CARDS_LATE = ["D12-triangulation-topology", "D12-tensor-maximum-bochner"]
# round-11 recorded counts for the late cards
R11_LATE = {
    "D12-triangulation-topology": {"probe": 194, "fullaudit": 537, "kind": 194},
    "D12-tensor-maximum-bochner": {"probe": 20, "fullaudit": 335, "kind": 20},
}
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


def counts(card):
    out = {}
    p = os.path.join(LOGS, card + ".probe.log")
    if os.path.exists(p):
        out["probe"] = len(re.findall(r"depends on axioms", open(p, errors="replace").read()))
    p = os.path.join(LOGS, card + ".fullaudit.log")
    if os.path.exists(p):
        m = re.search(r"A3FULL: (\d+) declarations", open(p, errors="replace").read())
        out["fullaudit"] = int(m.group(1)) if m else None
        out["fullaudit_pass"] = "A3FULL: PASS" in open(p, errors="replace").read()
    p = os.path.join(LOGS, card + ".kind.log")
    if os.path.exists(p):
        out["kind"] = len([l for l in open(p, errors="replace") if l.startswith("A3KIND\t")])
    return out


def main():
    summary = {"round": 12, "invocation": 9, "generated_by": "audit360/round12_summary.py",
               "logs": "audit360/logs-round12", "compared_to": "audit360/logs-round11"}
    cards = {}
    identical_all = True
    for card in CARDS7:
        entry = {"rc": {s: rc(card + "." + s) for s in ("build", "probe", "fullaudit", "kind")},
                 "counts": counts(card)}
        byte = {}
        for suffix in ("build", "probe", "fullaudit", "kind"):
            a = os.path.join(LOGS, f"{card}.{suffix}.log")
            b = os.path.join(PREV, f"{card}.{suffix}.log")
            if os.path.exists(a) and os.path.exists(b):
                byte[suffix] = strip_headers(a) == strip_headers(b)
            else:
                byte[suffix] = None
        entry["byte_identical_to_round11"] = byte
        entry["identical"] = all(v is True for v in byte.values())
        if not entry["identical"]:
            identical_all = False
        cards[card] = entry
    for card in CARDS_LATE:
        entry = {"rc": {s: rc(card + "." + s) for s in ("build", "probe", "fullaudit", "kind")},
                 "counts": counts(card), "round11_counts": R11_LATE[card]}
        c = entry["counts"]
        entry["counts_match_round11"] = (
            c.get("probe") == R11_LATE[card]["probe"]
            and c.get("fullaudit") == R11_LATE[card]["fullaudit"]
            and c.get("kind") == R11_LATE[card]["kind"])
        if not entry["counts_match_round11"]:
            identical_all = False
        cards[card] = entry
    summary["cards"] = cards
    summary["all_seven_byte_identical"] = all(cards[c]["identical"] for c in CARDS7)
    summary["late_cards_counts_match"] = all(cards[c]["counts_match_round11"] for c in CARDS_LATE)
    summary["verdict"] = "PASS" if identical_all else "DRIFT"
    json.dump(summary, open(os.path.join(HERE, "round12_summary.json"), "w", encoding="utf-8"),
              indent=1, sort_keys=True)
    print(json.dumps({k: v for k, v in summary.items() if k != "cards"}, indent=1))
    for c, e in cards.items():
        print(c, e.get("identical", e.get("counts_match_round11")), e["rc"], e["counts"])
    return 0 if identical_all else 1


if __name__ == "__main__":
    raise SystemExit(main())
