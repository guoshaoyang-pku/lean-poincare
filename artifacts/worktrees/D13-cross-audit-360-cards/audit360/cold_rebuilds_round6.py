#!/usr/bin/env python3
"""Collect the round-6 cold-rebuild evidence into one artifact."""
import hashlib
import json
import os
import re

HERE = os.path.dirname(os.path.abspath(__file__))
LOGS = os.path.join(HERE, "logs-cold6")
CARDS = ["D12-volume-ibp", "D12-spectral-sobolev", "D12-semantic-ledger",
         "D12-comparison-geodesics", "D12-geometric-compactness"]


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


out = {"round": 6, "invocation": 5, "logs": "audit360/logs-cold6",
       "method": ("copy the staged package WITHOUT .lake/build into "
                  "audit360/pkgs-cold6/<card>, re-link the shared pinned mathlib "
                  "package cache, lake build from source, then lake env lean A3Probe.lean"),
       "cards": {}}
for card in CARDS:
    b = os.path.join(LOGS, card + ".cold.build.log")
    p = os.path.join(LOGS, card + ".cold.probe.log")
    cones = sum(1 for l in open(p, errors="replace") if re.match(r"^Poincare\.", l))
    viol = sum(1 for l in open(p, errors="replace") if "unapproved" in l.lower())
    out["cards"][card] = {
        "build_rc": int(open(os.path.join(LOGS, card + ".cold.build.rc")).read().strip()),
        "probe_rc": int(open(os.path.join(LOGS, card + ".cold.probe.rc")).read().strip()),
        "probe_declarations": cones,
        "probe_unapproved_markers": viol,
        "cache_absent_before_build": "confirmed-absent" in open(b, errors="replace").read(),
        "build_log_sha256": sha(b),
        "probe_log_sha256": sha(p),
    }
with open(os.path.join(HERE, "cold_rebuilds_round6.json"), "w") as f:
    json.dump(out, f, indent=1)
print(json.dumps(out, indent=1))
