#!/usr/bin/env python3
"""Self-audit of the audit card: re-verify every sha256 recorded in the results
JSON against the bytes on disk.

Covers all four producer hash schemas (flat filename map, `release/`-relative
paths, module-name map, package/d12-authored maps), the audited-copy hashes, the
round-3 artifact hashes, and the round-3 probe/evidence hashes.  Fail-closed:
any mismatch is reported and the exit code is nonzero.
"""
import hashlib
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
TREES = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees"
RESULTS = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")

CARDS = ["D12-connection-curvature", "D12-volume-ibp", "D12-spectral-sobolev",
         "D12-semantic-ledger", "D12-comparison-geodesics", "D12-geometric-compactness",
         "D12-surgery-recognition"]


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


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

    def check_map(self, label, base, mapping, transform=lambda p: p):
        for rel, want in mapping.items():
            self.check(label + ":" + rel, os.path.join(base, transform(rel)), want)


def main():
    d = json.load(open(RESULTS))
    a = Audit()
    sh = d["source_hashes"]

    # --- producer source hashes, per schema ---
    root = lambda card: os.path.join(TREES, card)
    for card in CARDS:
        rec = sh[card]["producer_recorded"]
        if card == "D12-volume-ibp":
            def volpath(p):
                cand = os.path.join("Poincare", "D12", "VolumeIBP", p)
                if os.path.exists(os.path.join(root(card), "release", cand)):
                    return cand
                return p
            a.check_map(card, os.path.join(root(card), "release"), rec, volpath)
        elif card == "D12-spectral-sobolev":
            a.check_map(card, root(card), rec["sha256"])
        elif card == "D12-semantic-ledger":
            a.check_map(card, os.path.join(root(card), "release"), rec["package_lean_files"])
            a.check_map(card, os.path.join(root(card), "release"), rec["d12_authored"])
            modbase = os.path.join(HERE, "pkgs", "D12-semantic-ledger-snapshot")
            a.check_map(card + ":snapshot", modbase, rec["snapshot_rebuilt_modules"],
                        lambda m: m.replace(".", "/") + ".lean")
        elif card == "D12-connection-curvature":
            def ccpath(p):
                cand = os.path.join("release", p)
                if os.path.exists(os.path.join(root(card), cand)):
                    return cand
                return p
            a.check_map(card, root(card), rec, ccpath)
        else:
            # keys already carry the `release/` prefix
            a.check_map(card, root(card), rec)

        # audited-copy hashes (skip descriptive duplicate keys such as "... (snapshot copy)")
        copybase = os.path.join(HERE, "pkgs", card)
        copymap = {k: v for k, v in sh[card].get("audited_copy_sha256", {}).items() if " (" not in k}
        a.check_map(card + ":copy", copybase, copymap)

    # --- round-3 artifacts ---
    for name, h in d.get("round3_artifacts", {}).items():
        hit = None
        for root, _dirs, files in os.walk(WT):
            if name in files:
                hit = os.path.join(root, name)
                break
        if hit is None:
            a.missing.append((name, "not found under worktree"))
        else:
            a.check(name, hit, h)

    # --- round-3 named evidence ---
    for card, v in d.get("new_independent_closure_consumers", {}).items():
        if isinstance(v, dict) and "file" in v:
            a.check("closure:" + card, os.path.join(WT, v["file"]), v["sha256"])
    for key, label in [("f1_validation_round3", "f1"), ("a3_d2d3_round3", "a3d2d3")]:
        if key in d:
            a.check(label, os.path.join(WT, d[key]["file"]), d[key]["sha256"])
    if "f1_validation_round3" in d:
        e = d["f1_validation_round3"]
        a.check("f1:artifact", os.path.join(WT, e["artifact"]), e["artifact_sha256"])
    ub = d.get("unused_binder_screen_round3", {}).get("kernel_evidence", {})
    for name in ("phantom_params", "hyp_removal"):
        if name in ub:
            a.check(name, os.path.join(WT, ub[name]), ub[name + "_sha256"])
    fts = d.get("full_namespace_type_screen_round3", {})
    if "script_sha256" in fts:
        a.check("fulltype_screen.py", os.path.join(HERE, "fulltype_screen.py"), fts["script_sha256"])

    # --- round-5 independent closure consumer ---
    for card, v in d.get("new_independent_closure_consumers_round5", {}).items():
        if isinstance(v, dict) and "file" in v:
            a.check("closure5:" + card, os.path.join(WT, v["file"]), v["sha256"])

    # --- round-6 independent closure consumer ---
    for card, v in d.get("new_independent_closure_consumers_round6", {}).items():
        if isinstance(v, dict) and "file" in v:
            a.check("closure6:" + card, os.path.join(WT, v["file"]), v["sha256"])
            if "log" in v:
                a.check("closure6log:" + card, os.path.join(WT, v["log"]), v["log_sha256"])

    # --- round-6 artifacts (scripts, screens and summaries of invocation 5) ---
    for name, h in d.get("round6_artifacts", {}).items():
        hit = os.path.join(HERE, name)
        if not os.path.exists(hit):
            hit = None
            for root, _dirs, files in os.walk(WT):
                if name in files:
                    hit = os.path.join(root, name)
                    break
        if hit is None:
            a.missing.append((name, "not found under worktree"))
        else:
            a.check("round6:" + name, hit, h)

    # --- round-5 artifacts (screens, summaries and scripts of invocation 4) ---
    for name, h in d.get("round5_artifacts", {}).items():
        hit = os.path.join(HERE, name)
        if not os.path.exists(hit):
            hit = None
            for root, _dirs, files in os.walk(WT):
                if name in files:
                    hit = os.path.join(root, name)
                    break
        if hit is None:
            a.missing.append((name, "not found under worktree"))
        else:
            a.check("round5:" + name, hit, h)

    # --- round-11 artifacts ---
    r11 = d.get("round11", {})
    if r11:
        a.check("round11:sweep_summary", os.path.join(HERE, "round11_summary.json"),
                r11["sweep_summary_sha256"])
        a.check("round11:card_freeze", os.path.join(HERE, "card_freeze_round11.json"),
                r11["card_freeze_round11"]["sha256"])
        a.check("round11:producer_vs_staged",
                os.path.join(HERE, "r11", "producer_vs_staged_round11.json"),
                r11["producer_vs_staged_round11"]["sha256"])
        a.check("round11:missing_recheck",
                os.path.join(HERE, "missing_cards_recheck_round11.json"),
                r11["missing_cards_recheck"]["sha256"])
        a.check("round11:card8_json",
                os.path.join(TREES, "D12-triangulation-topology", "longrun", "results",
                             "D12-triangulation-topology.json"),
                r11["card8_arrival"]["card_json_sha256"])
        for rel, want in r11.get("audit_artifacts", {}).items():
            a.check("round11:" + rel, os.path.join(WT, rel), want)

    # --- round-12 artifacts ---
    r12 = d.get("round12", {})
    if r12:
        a.check("round12:sweep_summary", os.path.join(HERE, "round12_summary.json"),
                r12["sweep_summary_sha256"])
        for rel, want in r12.get("evidence_files", {}).items():
            a.check("round12:ev:" + os.path.basename(rel), os.path.join(WT, rel), want)
        for rel, want in r12.get("artifacts", {}).items():
            a.check("round12:" + rel, os.path.join(WT, rel), want)

    print("verified OK:", a.ok)
    print("mismatches:", len(a.bad))
    for b in a.bad:
        print("  MISMATCH", b)
    print("unresolved:", len(a.missing))
    for m in a.missing:
        print("  MISSING", m)
    return 1 if (a.bad or a.missing) else 0


if __name__ == "__main__":
    sys.exit(main())
