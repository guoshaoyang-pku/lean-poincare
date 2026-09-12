#!/usr/bin/env python3
"""Merge the fourth-invocation payload into longrun/results/L1-lean-baseline.json.

Usage: python3 baseline/fourth/update_card_json.py [payload.json]

Existing top-level keys keep their position (values replaced); new keys are
appended.  Inside "acceptance", "blockers" and "evidence_files" the payload's
sub-keys are merged without dropping the prior invocation's entries.
"""
import json
import os
import sys

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PAYLOAD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(WT, "baseline/fourth/card-payload.json")
CARD = os.path.join(WT, "longrun/results/L1-lean-baseline.json")

with open(CARD) as f:
    card = json.load(f)
with open(PAYLOAD) as f:
    payload = json.load(f)

for key, value in payload.items():
    if key in ("acceptance", "blockers", "evidence_files", "pins", "findings") and isinstance(value, dict) \
            and isinstance(card.get(key), dict):
        card[key].update(value)
    elif key == "findings_append" and isinstance(value, list):
        existing = card.setdefault("findings", [])
        if isinstance(existing, list):
            existing.extend(value)
        else:
            card["findings"] = value
    else:
        card[key] = value

card.pop("findings_append", None)
with open(CARD, "w") as f:
    json.dump(card, f, indent=1)
    f.write("\n")
print("card json updated; keys:", len(card))
