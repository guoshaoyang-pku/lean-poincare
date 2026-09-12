#!/usr/bin/env python3
"""Merge the fourth-invocation payload into checkpoint.json (idempotent).

Usage: python3 baseline/fourth/update_checkpoint.py [baseline/fourth/checkpoint-payload.json]

Reads WT/checkpoint.json, replaces the top-level status/phase/updated_at and the
"fourth_invocation" object (and "named_blockers"/"result_card" when the payload
provides them), then writes back with the same key order: existing keys keep their
position, new keys are appended.  Never touches anything else.
"""
import json
import os
import sys

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PAYLOAD = sys.argv[1] if len(sys.argv) > 1 else os.path.join(WT, "baseline/fourth/checkpoint-payload.json")

with open(os.path.join(WT, "checkpoint.json")) as f:
    ck = json.load(f)
with open(PAYLOAD) as f:
    payload = json.load(f)

for key in ("status", "phase", "updated_at"):
    if key in payload:
        ck[key] = payload[key]
if "fourth_invocation" in payload:
    ck["fourth_invocation"] = payload["fourth_invocation"]
for key in ("named_blockers", "result_card", "compile_checks", "findings", "next_step"):
    if key in payload:
        ck[key] = payload[key]
if "source_state_update" in payload:
    ck.setdefault("source_state", {}).update(payload["source_state_update"])

with open(os.path.join(WT, "checkpoint.json"), "w") as f:
    json.dump(ck, f, indent=1)
    f.write("\n")
print("checkpoint.json updated; keys:", len(ck))
