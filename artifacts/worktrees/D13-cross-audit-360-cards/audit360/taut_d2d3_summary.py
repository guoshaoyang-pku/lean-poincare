#!/usr/bin/env python3
"""Round-9c summary of the kernel assumption-as-conclusion screen over the D2/D3/D6
environment (`a3d2d3/A3TautD2D3.lean`).

The screen is the same kernel criterion used for the seven D12 packages, run over
the D2/D3/D6 release environment (roots `Poincare`, `Audit`, `Ledger`; 1307
constants).  It flags declarations whose hypothesis is definitionally the
conclusion, whose conclusion is definitionally `True`, or whose proof body is an
assumption whose type is the flagged conclusion binder.

Output: audit360/taut_screen_d2d3_round9.json
"""
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
PKG = os.path.join(WT, "a3d2d3")
LOG = os.path.join(PKG, "A3TautD2D3.log")
RC = os.path.join(PKG, "A3TautD2D3.rc")
LEAN = os.path.join(PKG, "A3TautD2D3.lean")
OUT = os.path.join(HERE, "taut_screen_d2d3_round9.json")

VERDICTS = {
    "Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold": {
        "classification": "CONFIRMS prior finding A3-D2D3-8",
        "detail": ("proof is `fun _h hrec => hrec`: the interface hypothesis "
                   "`_h : CompactThreeManifold M` is unused and the recognition "
                   "hypothesis `hrec` is definitionally the Stage6 target "
                   "(`Poincare.Stage6.poincareConjectureTopologicalThree M` is an alias "
                   "of `Nonempty (M ≃ₜ SphereThree)`).  Zero mathematical content beyond "
                   "restating the hypothesis; already recorded as trivial in round 3."),
    },
    "Poincare.Longrun.Topology.stage6Target_of_sphereRecognition": {
        "classification": "NEW FINDING A3-D2D3-9 (definitional restatement)",
        "detail": ("`(h : Nonempty (M ≃ₜ SphereThree)) : "
                   "Poincare.Stage6.poincareConjectureTopologicalThree M := h`: the "
                   "hypothesis type is definitionally the conclusion, so the theorem is a "
                   "restatement of the missing Poincare statement, not a bridge that "
                   "reduces it.  The producer docstring is honest about this ('its "
                   "hypothesis is exactly the missing Poincare theorem'), but the "
                   "declaration is absent from the A3 finding list: the round-3 "
                   "unused-binder screen could not catch it because the hypothesis IS the "
                   "proof body.  Only the assumption-as-conclusion criterion detects it.  "
                   "It must not be counted as progress on the Stage6 target."),
    },
}


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    text = open(LOG, errors="replace").read()
    rc = int(open(RC).read().strip().split("=")[-1])
    flags = re.findall(r"^A3TAUTD2D3-FLAG: (\S+) \[(.*)\]$", text, re.M)
    m = re.search(r"^A3TAUTD2D3: checked (\d+) constants, (\d+) with proof values, "
                  r"flags (\d+)$", text, re.M)
    unknown = [n for n, _ in flags if n not in VERDICTS]
    out = {
        "schema": "a3-taut-screen-d2d3-v1",
        "round": 9,
        "source": "a3d2d3/A3TautD2D3.lean",
        "source_sha256": sha(LEAN),
        "log": "a3d2d3/A3TautD2D3.log",
        "log_sha256": sha(LOG),
        "rc": rc,
        "checked_constants": int(m.group(1)) if m else None,
        "proof_valued_constants": int(m.group(2)) if m else None,
        "flag_count": int(m.group(3)) if m else None,
        "control_flagged": "A3TAUTD2D3-CONTROL-FLAGGED" in text,
        "flags": [
            {"name": n, "reasons": [r.strip() for r in rs.split(",")],
             **VERDICTS.get(n, {"classification": "UNCLASSIFIED", "detail": ""})}
            for n, rs in flags],
        "unclassified": unknown,
        "verdict": (
            "PASS (screen): control flagged; 2 true positives on real D2/D3 code, both "
            "classified.  One confirms the known A3-D2D3-8 tautology, the other is the new "
            "finding A3-D2D3-9 (`stage6Target_of_sphereRecognition`, a definitional "
            "restatement of the missing Poincare statement).  Neither is a soundness bug; "
            "both are zero-content conditional restatements that must not be counted as "
            "progress on the Stage6 target."
            if not unknown and "A3TAUTD2D3-CONTROL-FLAGGED" in text and rc == 0
            else "FAIL-CLOSED: control missing or unclassified flag"),
    }
    json.dump(out, open(OUT, "w"), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k != "flags"}, indent=1))
    for f in out["flags"]:
        print("-", f["name"], f["classification"], f["reasons"])
    return 0 if (not unknown and out["control_flagged"] and rc == 0) else 1


if __name__ == "__main__":
    sys.exit(main())
