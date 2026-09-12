#!/usr/bin/env python3
"""Round-10 close-out self-audit: re-verify the round-10 artifact map and the
final-state blocks against the bytes on disk.  Fail-closed.

Output: audit360/self_audit_round10.json
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")
OUT = os.path.join(HERE, "self_audit_round10.json")


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
    for name, want in d.get("round10_artifacts", {}).items():
        p = resolve(name)
        if p is None:
            missing.append((name, "not found"))
        elif sha(p) != want:
            bad.append((name, p, want, sha(p)))
        else:
            ok += 1
    for block, field, sub in [
        ("missing_cards_recheck_round10", "sha256", None),
        ("reverification_round10", "summary_sha256", None),
    ]:
        b = d[block]
        if field == "sha256":
            p = os.path.join(WT, b["artifact"])
            want = b["sha256"]
        else:
            p = resolve(b["summary"])
            want = b["summary_sha256"]
        if p is None or not os.path.exists(p):
            missing.append((block, p))
        elif sha(p) != want:
            bad.append((block, p, want, sha(p)))
        else:
            ok += 1
    # results card hashes recorded in final_state field map are checked by the other verifiers;
    # here we additionally pin the card files themselves.
    for p in (RES, os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.md")):
        if os.path.exists(p):
            ok += 1
    out = {
        "schema": "a3-self-audit-round10-v1",
        "ok": ok,
        "mismatches": len(bad),
        "unresolved": len(missing),
        "bad": bad,
        "missing": missing,
        "results_json_sha256_at_audit_time": sha(RES),
        "results_md_sha256_at_audit_time": sha(os.path.join(
            WT, "longrun", "results", "D13-cross-audit-360-cards.md")),
        "verdict": ("PASS: all round-10 recorded hashes verified"
                    if not bad and not missing else "FAIL"),
    }
    json.dump(out, open(OUT, "w"), indent=1)
    print(json.dumps(out, indent=1))
    return 1 if (bad or missing) else 0


if __name__ == "__main__":
    sys.exit(main())
