#!/usr/bin/env python3
"""Round-9c fold-in: D2/D3 kernel tautology screen and finding A3-D2D3-9."""
import datetime
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES_JSON = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")
RES_MD = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.md")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def h(name):
    return sha(os.path.join(HERE, name))


d = json.load(open(RES_JSON))
d2 = json.load(open(os.path.join(HERE, "taut_screen_d2d3_round9.json")))
now = datetime.datetime.now().isoformat(timespec="seconds")

d["generated_at"] = now
d["elapsed_hours"] = 1.35
d["cumulative_task_hours"] = 4.3

d["round9_artifacts"]["../a3d2d3/A3TautD2D3.lean"] = sha(os.path.join(WT, "a3d2d3", "A3TautD2D3.lean"))
d["round9_artifacts"]["taut_d2d3_summary.py"] = h("taut_d2d3_summary.py")
d["round9_artifacts"]["taut_screen_d2d3_round9.json"] = h("taut_screen_d2d3_round9.json")

d["kernel_tautology_screen_round9"]["d2d3_environment"] = {
    "artifact": "audit360/taut_screen_d2d3_round9.json",
    "sha256": h("taut_screen_d2d3_round9.json"),
    "source": "a3d2d3/A3TautD2D3.lean",
    "source_sha256": d2["source_sha256"],
    "log_sha256": d2["log_sha256"],
    "scope": ("D2/D3/D6 release environment (roots Poincare, Audit, Ledger): 1307 "
              "constants, 1179 with proof values"),
    "checked_constants": d2["checked_constants"],
    "proof_valued_constants": d2["proof_valued_constants"],
    "flag_count": d2["flag_count"],
    "control_flagged": d2["control_flagged"],
    "flags": d2["flags"],
    "verdict": d2["verdict"],
}

# A3 finding list: append the new item and refresh status
if isinstance(d.get("a3_d2d3_search"), dict):
    d["a3_d2d3_search"]["round9_kernel_screen"] = {
        "artifact": "audit360/taut_screen_d2d3_round9.json",
        "result": ("the new assumption-as-conclusion screen independently reproduces "
                   "A3-D2D3-8 and adds A3-D2D3-9"),
        "A3-D2D3-9": d2["flags"][1] if len(d2["flags"]) > 1 else None,
    }
d.setdefault("findings", [])
d["findings"].append({
    "id": "A3-D2D3-9",
    "round": 9,
    "class": "zero-content conditional restatement (not a soundness bug)",
    "declaration": "Poincare.Longrun.Topology.stage6Target_of_sphereRecognition",
    "evidence": ("a3d2d3/A3TautD2D3.lean rc 0: kernel-checked flags "
                 "hypothesis-eq-conclusion:h AND proof-is-hypothesis:h; the hypothesis type "
                 "`Nonempty (M ≃ₜ SphereThree)` is definitionally "
                 "`Poincare.Stage6.poincareConjectureTopologicalThree M`"),
    "why_new": ("the round-3 unused-binder screen cannot catch it (the hypothesis is the "
                "proof body, hence 'used'); only the assumption-as-conclusion criterion "
                "detects the restatement"),
    "consequence": ("must not be counted as progress on the Stage6 target; the producer "
                    "docstring already says its hypothesis is exactly the missing Poincare "
                    "statement"),
})

d["verdict"] = d["verdict"].rstrip() + (
    "  Round 9c (same invocation): the same kernel criterion run over the 1307-constant "
    "D2/D3/D6 environment flags exactly two declarations, both zero-content restatements — "
    "it independently reproduces the known A3-D2D3-8 tautology and finds a new one, "
    "A3-D2D3-9 (`stage6Target_of_sphereRecognition`), which the unused-binder screen could "
    "not catch.")

json.dump(d, open(RES_JSON, "w"), indent=1)
print("JSON updated")

# ---------------- markdown --------------------------------------------------
text = open(RES_MD).read()
anchor = "### 17.2 Full-namespace Prop-gated screen"
if anchor not in text:
    raise SystemExit("md anchor missing")
if "### 17.3 " in text:
    text = text[:text.find("\n### 17.3 ")]
section = f"""

### 17.3 Same criterion on the D2/D3/D6 environment — new finding A3-D2D3-9

`a3d2d3/A3TautD2D3.lean` (sha256 `{d2['source_sha256']}`, rc 0) runs the identical kernel
criterion over the D2/D3/D6 release environment (`import ReleaseCheck`; roots `Poincare`,
`Audit`, `Ledger`; the same namespace set as `A3UnusedHypD6.lean`): **1307 constants
checked, 1179 with proof values, 2 flags**, control flagged.  The two flags are:

| declaration | reasons | classification |
|---|---|---|
| `Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold` | `hypothesis-eq-conclusion:hrec`, `proof-is-hypothesis:hrec` | **confirms A3-D2D3-8** — proof is `fun _h hrec => hrec`, the interface hypothesis `_h` is unused, zero content beyond restating the recognition hypothesis |
| `Poincare.Longrun.Topology.stage6Target_of_sphereRecognition` | `hypothesis-eq-conclusion:h`, `proof-is-hypothesis:h` | **new finding A3-D2D3-9** — `(h : Nonempty (M ≃ₜ SphereThree)) : poincareConjectureTopologicalThree M := h`; the hypothesis type is definitionally the conclusion, so it is a restatement of the missing Poincaré statement, not a reduction of it |

`stage6Target_of_sphereRecognition` was **not** in the prior A3 finding list: the round-3
unused-binder screen cannot flag it because the hypothesis is the proof body (hence "used"),
and the string-based vacuity screen only compares hypotheses with the conclusion
syntactically.  The producer docstring is honest ("its hypothesis is exactly the missing
Poincaré theorem"), but the declaration must not be counted as progress on the Stage6
target.  Neither flag is a soundness bug; both are zero-content conditional restatements,
which is exactly the failure mode the task instruction "no assumption equivalent to the
conclusion" targets.
"""
open(RES_MD, "w").write(text.rstrip("\n") + "\n" + section.strip("\n") + "\n")
print("MD updated; sha256:", sha(RES_MD))
