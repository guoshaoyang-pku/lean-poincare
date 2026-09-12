#!/usr/bin/env python3
"""Round-9b aggregation of the full-namespace Prop-gated assumption-as-conclusion screen.

Reads `audit360/logs-tautfull/<card>.{log,rc}` produced by `run_taut_full.sh`.
Each package screens every constant in its own `Poincare.D12` namespace (1104 in
total across the seven packages, the same environment as `A3FullAudit`), with the
criterion restricted to Prop-valued conclusions.

Fail-closed: rc 1 if any run is nonzero, the control is not flagged, or any
declaration is flagged.

Output: audit360/taut_screen_full_round9.json
"""
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LOGS = os.path.join(HERE, "logs-tautfull")
OUT = os.path.join(HERE, "taut_screen_full_round9.json")
CARDS = ["D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
         "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
         "D12-surgery-recognition"]


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    result = {"schema": "a3-taut-screen-full-v1", "round": 9, "cards": {},
              "flags": [], "problems": []}
    total = prop = 0
    for card in CARDS:
        logp = os.path.join(LOGS, card + ".log")
        rcp = os.path.join(LOGS, card + ".rc")
        rc = int(open(rcp).read().strip().split("=")[-1]) if os.path.exists(rcp) else None
        text = open(logp, errors="replace").read() if os.path.exists(logp) else ""
        m = re.search(r"^A3TAUTFULL: checked (\d+) constants, (\d+) with proof values, "
                      r"flags (\d+)$", text, re.M)
        flags = re.findall(r"^A3TAUTFULL-FLAG: (\S+) \[(.*)\]$", text, re.M)
        entry = {
            "rc": rc,
            "checked_constants": int(m.group(1)) if m else None,
            "proof_valued_constants": int(m.group(2)) if m else None,
            "flags": int(m.group(3)) if m else None,
            "control_flagged": "A3TAUTFULL-CONTROL-FLAGGED" in text,
            "log": "audit360/logs-tautfull/%s.log" % card,
            "log_sha256": sha(logp) if os.path.exists(logp) else None,
            "flag_names": [n for n, _ in flags],
        }
        if entry["rc"] != 0 or not entry["control_flagged"] or entry["flags"]:
            result["problems"].append(card)
        total += entry["checked_constants"] or 0
        prop += entry["proof_valued_constants"] or 0
        result["flags"] += [{"card": card, "name": n, "reasons": r} for n, r in flags]
        result["cards"][card] = entry
    result["total_constants_checked"] = total
    result["total_proof_valued"] = prop
    result["verdict"] = (
        "PASS: all 7 packages rc 0; the injected assumption-as-conclusion control is flagged "
        "in every package; 0 of the %d full-namespace constants (same enumeration as the "
        "1103-declaration axiom audit) has a hypothesis definitionally equal to its "
        "conclusion, a conclusion definitionally True, or an assumption as its proof."
        % total if not result["problems"] else
        "FAIL-CLOSED: " + ", ".join(result["problems"]))
    json.dump(result, open(OUT, "w"), indent=1)
    print(json.dumps({k: v for k, v in result.items() if k != "cards"}, indent=1))
    for card, e in result["cards"].items():
        print(f'{card:28s} rc={e["rc"]} checked={e["checked_constants"]} '
              f'proof-valued={e["proof_valued_constants"]} flags={e["flags"]} '
              f'control={e["control_flagged"]}')
    return 1 if result["problems"] else 0


if __name__ == "__main__":
    sys.exit(main())
