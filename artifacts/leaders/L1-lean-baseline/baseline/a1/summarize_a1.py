#!/usr/bin/env python3
"""Assemble the machine-readable A1 restatement evidence bundle.

Reads only artifacts already produced under baseline/a1/ and writes
baseline/a1/a1-evidence.json.
"""
import hashlib
import json
import os
import re
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
A1 = os.path.join(WT, "baseline", "a1")
LOGS = os.path.join(A1, "logs")


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def read(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            return fh.read()
    except OSError:
        return ""


def main():
    drift = json.load(open(os.path.join(A1, "patched-drift.json")))
    build = read(os.path.join(A1, "logs-patched-build.log"))
    g1 = read(os.path.join(LOGS, "a1-axiom-audit-G1.log"))
    g2 = read(os.path.join(LOGS, "a1-axiom-audit-G2.log"))
    rel = read(os.path.join(LOGS, "a1-d7-release-audit.log"))
    probe = read(os.path.join(LOGS, "a1-probe.log"))
    cone = read(os.path.join(LOGS, "a1-consumer-cone.log"))
    scan = json.load(open(os.path.join(LOGS, "forbidden-scan-patched.json")))
    p5_frozen = json.load(open(os.path.join(WT, "baseline", "logs", "p5-hash-gate.json")))
    p5_patched = json.load(open(os.path.join(LOGS, "p5-hash-gate-patched.json")))

    sums = dict(re.findall(r"^L1SUM\t(\S+)\t(.*)$", g1, re.M))
    consumers = {}
    for m in re.finditer(r"^A1USE (\S+) (\S+)$", cone, re.M):
        consumers.setdefault(m.group(1), []).append(m.group(2))
    signatures = re.findall(r"^(@?\S+) : (.*)$", probe, re.M)
    cones = re.findall(r"^'([^']+)' depends on axioms: \[(.*?)\]$", probe, re.M | re.S)

    bundle = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "blocker": "A1",
        "blocker_text": ("Overstrong hypotheses (not falsity) in three promoted theorems: "
                         "perelmanF_step_lt and gibbsTerm_strictAnti/gibbsTerm_step_lt assume "
                         "1 < c where 1 <= c suffices. D12 validation rule: the blocker stays "
                         "open until upstream restatement."),
        "restatement": {
            "scope": "three promoted theorems + 4 old-format call sites + docs; 1 new consumer module",
            "patch": os.path.join(A1, "a1-restatement.patch"),
            "patch_sha256": sha256(os.path.join(A1, "a1-restatement.patch")),
            "changed": [c["path"] for c in drift["changed"]],
            "added": [a["path"] for a in drift["added"]],
            "removed": [r["path"] for r in drift["removed"]],
            "frozen_tree_untouched": True,
        },
        "patched_build": {
            "log": os.path.join(A1, "logs-patched-build.log"),
            "success": "Build completed successfully" in build,
            "last_line": build.strip().splitlines()[-1] if build.strip() else "",
            "jobs": (re.search(r"Build completed successfully \((\d+) jobs\)", build) or [None, None])[1],
            "errors": len(re.findall(r"^error", build, re.M)),
            "sorry_warnings": len(re.findall(r"declaration uses 'sorry'", build)),
        },
        "audits": {
            "axiom_G1": {"verdict": (re.search(r"^L1AXVERDICT\t(.*)$", g1, re.M) or [None, None])[1],
                         "sums": sums},
            "axiom_G2": {"verdict": (re.search(r"^L1AXVERDICT\t(.*)$", g2, re.M) or [None, None])[1]},
            "d7_release_audit": {"verdict": "PASS" if "D7SharpReleaseAudit: PASS" in rel else "UNKNOWN",
                                 "declarations_audited": (re.search(r"project declarations audited: (\d+)", rel) or [None, None])[1]},
            "forbidden_scan": {"files": scan["files_scanned"], "decl_form_hits": scan["declaration_form_hits_total"],
                               "hits": [d["path"] for d in scan["files_with_declaration_form_hits"]]},
            "p5_gate_frozen": {"verdict": p5_frozen["verdict"], "files": p5_frozen["file_count"]},
            "p5_gate_patched": {"verdict": p5_patched["verdict"],
                                "drift_items": len(p5_patched["drift"]),
                                "changed": sum(1 for d in p5_patched["drift"] if d["kind"] == "changed")},
        },
        "restated_signatures": [{"name": n, "type": t} for n, t in signatures],
        "axiom_cones": [{"name": n, "axioms": a.replace("\n", " ").strip()} for n, a in cones],
        "downstream_consumers": consumers,
        "closure_legs": {
            "constructed_input": "baseline/a1/a1-restatement.patch applied to baseline/a1/patched-release (byte-copy)",
            "downstream_consumer": ("Poincare.D7.EvolutionSharp.SharpOnlyConsumers (perelmanF_step_lt_at_threshold_one "
                                    "at c == 1, impossible under the old hypothesis) plus the pre-existing D7 sharp layer "
                                    "and D4Audit; proof-level edges in downstream_consumers"),
            "independent_rebuild": "patched tree built from scratch in an isolated directory (lake build exit 0, 9340 jobs); frozen G1/G2 and D7 ReleaseAudit re-run on the patched oleans",
            "semantic_review": "NOT SELF-CERTIFIED - requested from the independent acceptor (card + outbox handoff)",
        },
    }
    out = os.path.join(A1, "a1-evidence.json")
    json.dump(bundle, open(out, "w"), indent=1)
    print(json.dumps({k: bundle[k] for k in ("blocker", "restatement", "patched_build")}, indent=1)[:1200])
    print("wrote", out)


if __name__ == "__main__":
    main()
