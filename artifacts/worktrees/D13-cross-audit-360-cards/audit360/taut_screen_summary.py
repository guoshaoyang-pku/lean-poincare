#!/usr/bin/env python3
"""Round-9 aggregation/classification of the kernel assumption-as-conclusion screen.

Reads `audit360/logs-taut/<card>.{log,rc}` produced by `run_taut_screen.sh` and
`audit360/kind_screen.json`, and classifies every `A3TAUT-FLAG`:

  * the positive control `A3TautScreen.a3TautCtl` must be flagged in every package
    (with both `hypothesis-eq-conclusion` and `proof-is-hypothesis`);
  * a flag on a `theorem` (proof-producing declaration) is a *defect candidate*
    that must be reviewed by hand;
  * a flag on a `def`/`inductive` is the expected over-firing of the criterion on
    data/type declarations whose result type coincides with a binder type.

Fail-closed: rc 1 if the control is missing in any package, if a screen run has
nonzero rc, or if any theorem-level flag is not classified.

Output: audit360/taut_screen_round9.json
"""
import hashlib
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LOGS = os.path.join(HERE, "logs-taut")
KINDS = os.path.join(HERE, "kind_screen.json")
OUT = os.path.join(HERE, "taut_screen_round9.json")
CARDS = ["D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
         "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
         "D12-surgery-recognition"]
CONTROL = "A3TautScreen.a3TautCtl"

# Manual verdicts for theorem-level flags (none expected outside the control).
THEOREM_VERDICTS = {}


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def main():
    kind_of = {}
    for card, entry in json.load(open(KINDS))["cards"].items():
        for row in entry.get("non_proof_entries", []):
            kind_of[row["name"]] = f'{row["kind"]}:{row["result"]}'

    result = {"schema": "a3-taut-screen-v1", "round": 9, "cards": {},
              "flags": [], "unclassified_theorem_flags": [], "control_missing": []}
    total_checked = 0
    for card in CARDS:
        logp = os.path.join(LOGS, card + ".log")
        rcp = os.path.join(LOGS, card + ".rc")
        rc = int(open(rcp).read().strip().split("=")[-1]) if os.path.exists(rcp) else None
        text = open(logp, errors="replace").read() if os.path.exists(logp) else ""
        flags = re.findall(r"^A3TAUT-FLAG: (\S+) \[(.*)\]$", text, re.M)
        m = re.search(r"^A3TAUT: checked (\d+), flags (\d+)$", text, re.M)
        checked = int(m.group(1)) if m else None
        total_checked += checked or 0
        entry = {"rc": rc, "checked": checked,
                 "flag_count": int(m.group(2)) if m else None,
                 "control_flagged": any(n == CONTROL for n, _ in flags),
                 "log_sha256": sha(logp) if os.path.exists(logp) else None,
                 "flags": []}
        if not entry["control_flagged"]:
            result["control_missing"].append(card)
        for name, reasons in flags:
            rlist = [r.strip() for r in reasons.split(",")]
            kind = kind_of.get(name, "theorem:PropResult")
            row = {"card": card, "name": name, "reasons": rlist, "kernel_kind": kind,
                   "is_control": name == CONTROL}
            if name == CONTROL:
                row["verdict"] = "POSITIVE CONTROL — flagged as required"
            elif not kind.startswith("theorem"):
                row["verdict"] = ("FALSE-POSITIVE (data/type declaration: its result type "
                                  "coincides with a binder type; no proof content)")
            else:
                v = THEOREM_VERDICTS.get(name)
                if v is None:
                    result["unclassified_theorem_flags"].append(row)
                    row["verdict"] = "UNCLASSIFIED"
                else:
                    row.update(v)
            entry["flags"].append(row["verdict"])
            result["flags"].append(row)
        result["cards"][card] = entry

    result["total_checked_including_controls"] = total_checked
    result["control_flagged_in_all_packages"] = not result["control_missing"]
    result["non_control_flags"] = [f for f in result["flags"] if not f["is_control"]]
    result["verdict"] = (
        "PASS: the kernel screen flags the injected assumption-as-conclusion control in all "
        "7 packages; every non-control flag is on a data/type definition whose result type "
        "coincides with one of its binder types; no theorem in the audited set has a "
        "hypothesis definitionally equal to its conclusion and no proof is an assumption."
        if result["control_flagged_in_all_packages"]
        and not result["unclassified_theorem_flags"]
        else "FAIL-CLOSED: control missing or theorem-level flag unclassified")
    json.dump(result, open(OUT, "w"), indent=1)
    print(json.dumps({k: v for k, v in result.items() if k not in ("flags", "cards")}, indent=1))
    for card, e in result["cards"].items():
        print(f'{card:28s} rc={e["rc"]} checked={e["checked"]} flags={e["flag_count"]} '
              f'control={e["control_flagged"]}')
    return 0 if (result["control_flagged_in_all_packages"]
                 and not result["unclassified_theorem_flags"]
                 and all(e["rc"] == 0 for e in result["cards"].values())) else 1


if __name__ == "__main__":
    sys.exit(main())
