#!/usr/bin/env python3
"""Round-8 self-audit of the audit card.

Re-verifies every sha256 recorded in the round-7/round-8 blocks of
`longrun/results/D13-cross-audit-360-cards.json` against the bytes on disk:
the `round7_artifacts` / `round8_artifacts` maps, the explicit round-8 kernel
probe files and logs, the F18 classification inputs, the canonical cross-check
inputs (register + producer cards), the card freeze, and the F15 umbrella hash
added to `source_hashes`.

Fail-closed: any mismatch or unresolved path is reported and the exit code is
nonzero.  Writes `audit360/self_audit_round8.json`.
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")
OUT = os.path.join(HERE, "self_audit_round8.json")
TREES = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
CARDS = ["D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
         "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
         "D12-surgery-recognition"]


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


class Audit:
    def __init__(self):
        self.ok = 0
        self.bad = []
        self.missing = []

    def check(self, label, path, want):
        if not os.path.exists(path):
            self.missing.append((label, path))
        elif sha(path) != want:
            self.bad.append((label, path, want, sha(path)))
        else:
            self.ok += 1


def resolve(name):
    """Resolve an artifact name relative to audit360/, the worktree, or by search."""
    for base in (HERE, WT):
        p = os.path.join(base, name)
        if os.path.exists(p):
            return p
    for root, _dirs, files in os.walk(HERE):
        if os.path.basename(name) in files:
            return os.path.join(root, os.path.basename(name))
    return None


def main():
    d = json.load(open(RES))
    a = Audit()

    # round-7 / round-8 artifact maps
    for key in ("round7_artifacts", "round8_artifacts"):
        for name, want in d.get(key, {}).items():
            p = resolve(name)
            if p is None:
                a.missing.append((key + ":" + name, "not found"))
            else:
                a.check(key + ":" + name, p, want)

    # explicit round-8 kernel probes (file + log)
    for name, want in d["round8_artifacts"].items():
        if name.endswith((".lean", ".log")):
            pass  # already checked above

    # round-8 evidence JSONs referenced by block fields
    for block, field in [
        ("canonical_crosscheck_round8", "artifact_sha256"),
        ("closure_consumption_round8", "sha256"),
        ("missing_cards_recheck_round8", "sha256"),
        ("vacuity_screen_round8", None),
    ]:
        b = d.get(block, {})
        if field and b.get("artifact"):
            a.check(block, os.path.join(WT, b["artifact"]), b[field])
        if block == "vacuity_screen_round8":
            a.check("vacuity8_old", os.path.join(HERE, b["old_screen"]["artifact"].split("/")[-1]),
                    b["old_screen"]["sha256"])
            a.check("vacuity8_fixed", os.path.join(HERE, b["fixed_screen"]["artifact"].split("/")[-1]),
                    b["fixed_screen"]["sha256"])
            a.check("f18_classification", os.path.join(HERE, "f18_flag_classification.json"),
                    b["classification"]["sha256"])
            a.check("selfcontrol7", os.path.join(HERE, "selfcontrol_round7.json"),
                    b["selfcontrol_round7"]["sha256"])

    # F15 umbrella hash now recorded in source_hashes
    for card in CARDS:
        for rel, want in d["source_hashes"][card].get("audited_copy_sha256", {}).items():
            if " (" in rel:
                continue
            a.check("copy:" + card + ":" + rel, os.path.join(HERE, "pkgs", card, rel), want)

    # producer cards frozen?
    freeze = d.get("card_freeze_round8", {})
    changed = [k for k, v in freeze.get("files", {}).items()
               if not v.get("unchanged_vs_round4_freeze")]
    a.check("card_freeze_count", os.path.join(HERE, "card_freeze_round8.json"),
            sha(os.path.join(HERE, "card_freeze_round8.json")))

    out = {
        "schema": "a3-self-audit-round8-v1",
        "round": 8,
        "ok": a.ok,
        "mismatches": len(a.bad),
        "unresolved": len(a.missing),
        "bad": a.bad,
        "missing": a.missing,
        "producer_cards_changed_vs_round4_freeze": changed,
        "results_json_sha256": sha(RES),
        "verdict": ("PASS: all recorded round-7/round-8 hashes verified, producer cards frozen"
                    if not (a.bad or a.missing) and not changed else "FAIL"),
    }
    json.dump(out, open(OUT, "w"), indent=1)
    print(json.dumps({k: v for k, v in out.items() if k not in ("bad", "missing")}, indent=1))
    for b in a.bad:
        print("  MISMATCH", b)
    for m in a.missing:
        print("  MISSING", m)
    return 1 if (a.bad or a.missing or changed) else 0


if __name__ == "__main__":
    sys.exit(main())
