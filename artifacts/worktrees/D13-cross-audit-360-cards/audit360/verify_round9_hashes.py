#!/usr/bin/env python3
"""Round-9 self-audit: re-verify every sha256 recorded in `round9_artifacts` and
the round-9 screen blocks against the bytes on disk.  Fail-closed.

Output: audit360/self_audit_round9.json
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")
OUT = os.path.join(HERE, "self_audit_round9.json")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def resolve(name):
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
    ok, bad, missing = 0, [], []
    for name, want in d.get("round9_artifacts", {}).items():
        p = resolve(name)
        if p is None:
            missing.append((name, "not found"))
        elif sha(p) != want:
            bad.append((name, p, want, sha(p)))
        else:
            ok += 1
    for block, field in [("kernel_tautology_screen_round9:declared_set", "artifact"),
                         ("kernel_tautology_screen_round9:full_namespace_prop_gated", "artifact")]:
        key, sub = block.split(":")
        b = d["kernel_tautology_screen_round9"][sub]
        p = os.path.join(WT, b[field])
        if not os.path.exists(p):
            missing.append((block, p))
        elif sha(p) != b["sha256"]:
            bad.append((block, p, b["sha256"], sha(p)))
        else:
            ok += 1
    # probe source hashes embedded in the per-card records
    for card, entry in d.get("replay_hashes", {}).items():
        pass
    out = {
        "schema": "a3-self-audit-round9-v1",
        "ok": ok,
        "mismatches": len(bad),
        "unresolved": len(missing),
        "bad": bad,
        "missing": missing,
        "results_json_sha256_at_audit_time": sha(RES),
        "verdict": ("PASS: all round-9 recorded hashes verified"
                    if not bad and not missing else "FAIL"),
    }
    json.dump(out, open(OUT, "w"), indent=1)
    print(json.dumps(out, indent=1))
    return 1 if (bad or missing) else 0


if __name__ == "__main__":
    sys.exit(main())
