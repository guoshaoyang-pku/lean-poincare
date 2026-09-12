#!/usr/bin/env python3
"""D9 independent gate 6: D6 claim conformance.

Cross-checks the D6 manifests against the auditor's freshly computed census
(D9BCONST/D9BTHM from IndepCensus.lean) and the auditor's own hash checks:

  * declaration count / kinds / per-declaration axiom cone vs
    manifest/verified-declarations.json and manifest/axiom-report.json
  * forbidden-axiom theorem/constant lists (must be empty)
  * D5 provenance hashes (58/58), D6 input hashes, D6 card counts
  * fresh-rebuild equality of prebuilt vs rebuilt oleans

Output: release/Audit/D9/logs/d9b/conformance.json
"""
import hashlib
import json
import os
import sys
from collections import Counter

ROOT = "/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-adversarial-audit-release"
RELEASE = os.path.join(ROOT, "release")
OUTDIR = os.path.join(RELEASE, "Audit", "D9", "logs", "d9b")
APPROVED = {"propext", "Classical.choice", "Quot.sound"}


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def main():
    out = {"schema": "d9-adversarial-audit/indep-conformance-v1"}
    # --- census ---
    consts = {}
    thms = {}
    for line in open(os.path.join(OUTDIR, "census.raw"), encoding="utf-8", errors="replace"):
        if line.startswith("D9BCONST\t"):
            p = line.rstrip("\n").split("\t")
            consts[p[1]] = {"module": p[2], "kind": p[3], "safety": p[4],
                            "axioms": [a for a in p[5].split(";") if a]}
        elif line.startswith("D9BTHM\t"):
            p = line.rstrip("\n").split("\t")
            thms[p[1]] = {"module": p[2], "axioms": [a for a in p[13].split(";") if a]}
    vd = json.load(open(os.path.join(ROOT, "manifest/verified-declarations.json")))
    axrep = json.load(open(os.path.join(ROOT, "manifest/axiom-report.json")))
    man = {d["name"]: d for d in vd["declarations"]}
    out["census_constants"] = len(consts)
    out["census_theorems"] = len(thms)
    out["manifest_count"] = vd["count"]
    out["manifest_kinds"] = vd["kinds"]
    raw_kinds = Counter(
        (c["kind"] + (":" + c["safety"] if c["kind"] == "def" else ""))
        for c in consts.values())
    label_map = {"thm": "theorem", "def:safe": "def", "def:partial": "partial_def",
                 "def:unsafe": "unsafe_def"}
    out["census_kinds"] = {label_map.get(k, k): v for k, v in raw_kinds.items()}
    out["census_kinds_raw"] = dict(raw_kinds)
    out["kinds_match"] = (out["census_kinds"] == vd["kinds"])
    missing = sorted(set(man) - set(consts))
    extra = sorted(set(consts) - set(man))
    out["declarations_missing_from_census"] = missing
    out["declarations_extra_in_census"] = extra
    cone_mismatch = []
    for name, c in consts.items():
        if name in man:
            want = [a for a in man[name]["axioms"] if a]
            if want != c["axioms"]:
                cone_mismatch.append({"name": name, "census": c["axioms"],
                                      "manifest": want})
    out["axiom_cone_mismatches"] = cone_mismatch
    out["census_unapproved"] = sorted(
        n for n, c in consts.items() if any(a not in APPROVED for a in c["axioms"]))
    out["theorem_unapproved"] = sorted(
        n for n, t in thms.items() if any(a not in APPROVED for a in t["axioms"]))
    # --- provenance 58/58 ---
    prov = json.load(open(os.path.join(ROOT, "input/d5-manifest/provenance.json")))
    entries = []
    for c in prov["clusters"]:
        for f in c.get("files", []):
            entries.append((f["path"], f["sha256"]))
    for b in prov.get("base_dependencies", []):
        entries.append((b["path"], b["sha256"]))
    bad = []
    for rel, want in entries:
        fp = os.path.join(RELEASE, rel)
        if not os.path.exists(fp) or sha(fp) != want:
            bad.append(rel)
    out["provenance_entries"] = len(entries)
    out["provenance_mismatches"] = bad
    # --- D6 input hashes ---
    ih = json.load(open(os.path.join(ROOT, "manifest/input-hashes.json")))
    ih_ok, ih_bad, ih_missing = [], [], []
    for rel, want in ih["inputs"].items():
        fp = os.path.join(ROOT, rel)
        if not os.path.exists(fp):
            ih_missing.append(rel)
        elif sha(fp) != want:
            ih_bad.append(rel)
        else:
            ih_ok.append(rel)
    out["input_hashes_total"] = len(ih["inputs"])
    out["input_hashes_ok"] = len(ih_ok)
    out["input_hashes_mismatched"] = ih_bad
    out["input_hashes_unavailable"] = ih_missing
    # --- cardinality claims from the D6 card ---
    d6card = json.load(open(os.path.join(ROOT, "longrun/results/D6-weekly-release.json")))
    out["d6_card_verdict"] = d6card.get("verdict")
    # --- fresh rebuild vs prebuilt olean hashes ---
    pre, fresh = {}, {}
    for path, d in ((os.path.join(OUTDIR, "prebuilt_hashes.txt"), pre),
                    (os.path.join(OUTDIR, "fresh_hashes.txt"), fresh)):
        for line in open(path):
            p = line.split()
            if len(p) == 2:
                d[p[1]] = p[0]
    common = set(pre) & set(fresh)
    out["olean_files_compared"] = len(common)
    out["olean_identical"] = sum(1 for k in common if pre[k] == fresh[k])
    out["olean_differing"] = sorted(k for k in common if pre[k] != fresh[k])

    with open(os.path.join(OUTDIR, "conformance.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: v for k, v in out.items()
                      if k not in ("census_kinds", "manifest_kinds")}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
