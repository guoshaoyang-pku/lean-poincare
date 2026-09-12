#!/usr/bin/env python3
"""D9 post-hoc verification gate 6: D6 claim conformance, recomputed.

Independent recomputation (own implementation) of:
  * declaration census vs manifest/verified-declarations.json (count, kinds, cones);
  * D5 provenance hashes (input/d5-manifest/provenance.json);
  * D6 declared input hashes (manifest/input-hashes.json);
  * every declaration referenced anywhere in manifest/theorem-dependency-ledger.json
    resolves in the fresh census (exact or unique namespace suffix);
  * #check statement counts of ReleaseClaims.lean (card claims) and D6LedgerProbe.lean;
  * forbidden-axiom screen over all census constants and ledgers' recorded cones.

Output: release/Audit/D9/logs/verify/conformance.json
"""
import hashlib
import json
import os
import sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
RELEASE = os.path.join(ROOT, "release")
VR = os.path.join(RELEASE, "Audit", "D9", "logs", "verify")
RAW = os.path.join(VR, "raw")
APPROVED = {"propext", "Classical.choice", "Quot.sound"}


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def main():
    out = {"schema": "d9-adversarial-audit/verify-conformance-v1"}
    consts, thms = {}, {}
    for line in open(os.path.join(RAW, "Audit__D9__IndepCensus.lean.log"),
                     encoding="utf-8", errors="replace"):
        if line.startswith("D9BCONST\t"):
            p = line.rstrip("\n").split("\t")
            consts[p[1]] = {"module": p[2], "kind": p[3], "safety": p[4],
                            "axioms": [a for a in p[5].split(";") if a]}
        elif line.startswith("D9BTHM\t"):
            p = line.rstrip("\n").split("\t")
            thms[p[1]] = {"module": p[2], "axioms": [a for a in p[13].split(";") if a]}
    vd = json.load(open(os.path.join(ROOT, "manifest/verified-declarations.json")))
    man = {d["name"]: d for d in vd["declarations"]}
    raw_kinds = Counter(c["kind"] + (":" + c["safety"] if c["kind"] == "def" else "")
                        for c in consts.values())
    label = {"thm": "theorem", "def:safe": "def", "def:partial": "partial_def",
             "def:unsafe": "unsafe_def"}
    out["census_constants"] = len(consts)
    out["census_theorems"] = len(thms)
    out["manifest_count"] = vd["count"]
    out["census_kinds"] = {label.get(k, k): v for k, v in raw_kinds.items()}
    out["manifest_kinds"] = vd["kinds"]
    out["kinds_match"] = out["census_kinds"] == vd["kinds"]
    out["missing_from_census"] = sorted(set(man) - set(consts))
    out["extra_in_census"] = sorted(set(consts) - set(man))
    out["axiom_cone_mismatches"] = [
        {"name": n, "census": consts[n]["axioms"], "manifest": [a for a in man[n]["axioms"] if a]}
        for n in sorted(set(man) & set(consts))
        if [a for a in man[n]["axioms"] if a] != consts[n]["axioms"]]
    out["unapproved_constants"] = sorted(n for n, c in consts.items()
                                         if any(a not in APPROVED for a in c["axioms"]))
    out["unapproved_theorems"] = sorted(n for n, t in thms.items()
                                        if any(a not in APPROVED for a in t["axioms"]))
    out["axiom_kind_constants"] = sorted(n for n, c in consts.items() if c["kind"] == "axiom")
    out["unsafe_def_constants"] = sorted(n for n, c in consts.items() if c["safety"] == "unsafe")
    out["partial_def_constants"] = sorted(n for n, c in consts.items()
                                          if c["kind"] == "def" and c["safety"] == "partial")

    # provenance
    prov = json.load(open(os.path.join(ROOT, "input/d5-manifest/provenance.json")))
    entries = []
    for c in prov["clusters"]:
        for f in c.get("files", []):
            entries.append((f["path"], f["sha256"]))
    for b in prov.get("base_dependencies", []):
        entries.append((b["path"], b["sha256"]))
    out["provenance_entries"] = len(entries)
    out["provenance_mismatches"] = [rel for rel, want in entries
                                    if not os.path.exists(os.path.join(RELEASE, rel))
                                    or sha(os.path.join(RELEASE, rel)) != want]

    # declared input hashes
    ih = json.load(open(os.path.join(ROOT, "manifest/input-hashes.json")))
    ok, bad, miss = [], [], []
    for rel, want in ih["inputs"].items():
        fp = os.path.join(ROOT, rel)
        if not os.path.exists(fp):
            miss.append(rel)
        elif sha(fp) != want:
            bad.append(rel)
        else:
            ok.append(rel)
    out["input_hashes_total"] = len(ih["inputs"])
    out["input_hashes_ok"] = len(ok)
    out["input_hashes_mismatched"] = bad
    out["input_hashes_unavailable"] = miss

    # ledger declaration resolution
    led = json.load(open(os.path.join(ROOT, "manifest/theorem-dependency-ledger.json")))
    refs = set()

    def add(n):
        if n:
            refs.add(n)

    for r in led["checked_results"]:
        for n in r.get("lean_declarations", []):
            add(n)
        for d in r.get("evidence", {}).get("declarations", []):
            add(d.get("name"))
    for r in led["blocked_layer"]:
        add(r.get("lean_declaration"))
    for n_ in led["interface_nodes"]:
        for n in n_.get("lean_declarations", []):
            add(n)
    for c in led["claim_resolution"]["card_claims"]:
        add(c.get("name"))

    def resolve(n):
        if n in consts:
            return n, "exact"
        sufs = [c for c in consts if c.endswith("." + n)]
        if len(sufs) == 1:
            return sufs[0], "suffix"
        return None, ("ambiguous" if sufs else "unresolved")

    res = {n: resolve(n) for n in sorted(refs)}
    out["ledger_referenced_declarations"] = len(refs)
    out["ledger_resolved_exact"] = sum(1 for _, (r, k) in res.items() if k == "exact")
    out["ledger_resolved_suffix"] = sum(1 for _, (r, k) in res.items() if k == "suffix")
    out["ledger_unresolved"] = sorted(n for n, (r, k) in res.items() if r is None)
    out["ledger_card_claims"] = len(led["claim_resolution"]["card_claims"])
    out["ledger_evidence_cone_mismatches"] = [
        {"name": d["name"], "ledger": d.get("axiom_cone"), "census": consts[d["name"]]["axioms"]}
        for r in led["checked_results"]
        for d in r.get("evidence", {}).get("declarations", [])
        if d.get("name") in consts and [a for a in d.get("axiom_cone", []) if a]
        != consts[d["name"]]["axioms"]]

    # probe statement counts
    out["release_claims_check_statements"] = sum(
        1 for l in open(os.path.join(RELEASE, "ReleaseClaims.lean"))
        if l.strip().startswith("#check"))
    out["ledger_probe_check_statements"] = sum(
        1 for l in open(os.path.join(RELEASE, "D6LedgerProbe.lean"))
        if l.strip().startswith("#check"))
    d6 = json.load(open(os.path.join(ROOT, "longrun/results/D6-weekly-release.json")))
    out["d6_card_verdict"] = d6.get("verdict")
    out["d6_card_verification"] = d6.get("verification", {})

    with open(os.path.join(VR, "conformance.json"), "w") as fh:
        json.dump(out, fh, indent=1)
    print(json.dumps({k: v for k, v in out.items()
                      if k not in ("d6_card_verification",)}, indent=1)[:4000])
    print("wrote", os.path.join(VR, "conformance.json"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
