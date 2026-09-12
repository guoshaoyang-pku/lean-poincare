#!/usr/bin/env python3
"""Cross-check the per-module probe inventory against the grouped audit table.

Method diversity, not independence: the grouped audit (`AxiomAudit_G1/G2.lean`)
enumerates a whole import-disjoint partition at once and matches constants by
collecting every name in each partition module's `env.constants`; the probes
enumerate one module per Lean process and select constants by
`env.getModuleIdxFor? n == target`.  Agreement of the two inventories is a
cross-check on the enumeration and on the duplicate-module (F1) claim.

Reads baseline/audit/probes/*.log + manifest.tsv and baseline/audit/declarations.tsv.
Writes baseline/audit/probe-inventory-crosscheck.json.
"""
import glob
import json
import os
import sys
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def main():
    manifest = {}
    for line in open(os.path.join(WT, "baseline/audit/probes/manifest.tsv")):
        i, m = line.rstrip("\n").split("\t")
        manifest[i] = m

    per_name_modules = {}
    per_module_names = {}
    per_name_kind = {}
    bad_logs = []
    missing = []
    for i in sorted(manifest):
        log = os.path.join(WT, f"baseline/logs/probes/{i}.log")
        if not os.path.exists(log):
            missing.append(i)
            continue
        ok = False
        for line in open(log, encoding="utf-8", errors="replace"):
            if not line.startswith("MD\t"):
                continue
            parts = line.rstrip("\n").split("\t")
            if len(parts) != 4:
                continue
            _md, mod, name, kind = parts
            ok = True
            per_name_modules.setdefault(name, set()).add(mod)
            per_module_names.setdefault(mod, set()).add(name)
            per_name_kind[name] = kind
        if not ok:
            bad_logs.append(i)

    # grouped audit table
    tsv = {}
    kinds = {}
    with open(os.path.join(WT, "baseline/audit/declarations.tsv")) as f:
        hdr = f.readline().rstrip("\n").split("\t")
        for line in f:
            p = line.rstrip("\n").split("\t")
            row = dict(zip(hdr, p))
            tsv[row["name"]] = row
            kinds[row["kind"]] = kinds.get(row["kind"], 0) + 1

    audit = json.load(open(os.path.join(WT, "baseline/audit/axiom-audit.json")))
    dup_audit = set(audit["duplicate_names"])

    probe_names = set(per_name_modules)
    tsv_names = set(tsv)
    dup_probe = {n for n, ms in per_name_modules.items() if len(ms) > 1}

    kind_mismatch = []
    map_kind = {"partial_def": "partial_def", "unsafe_def": "unsafe_def", "def": "def",
                "theorem": "theorem", "axiom": "axiom", "opaque": "opaque",
                "inductive": "inductive", "ctor": "ctor", "recursor": "recursor", "quot": "quot"}
    for n in sorted(probe_names & tsv_names):
        if map_kind.get(per_name_kind[n], per_name_kind[n]) != tsv[n]["kind"]:
            kind_mismatch.append({"name": n, "probe": per_name_kind[n], "tsv": tsv[n]["kind"]})

    module_count_mismatch = []
    for mod, names in sorted(per_module_names.items()):
        tsv_n = sum(1 for n, r in tsv.items() if r["module"] == mod)
        probe_n = len(names)
        if tsv_n != probe_n:
            module_count_mismatch.append({"module": mod, "probe": probe_n, "tsv": tsv_n})

    report = {
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "method": "per-module env.constants probes vs grouped-partition collectAxioms enumeration",
        "independence_caveat": "same agent/toolchain; method diversity only, NOT independent verification",
        "probe_modules_run": len(per_module_names),
        "probe_logs_missing": missing,
        "probe_logs_without_MD_rows": bad_logs,
        "probe_distinct_names": len(probe_names),
        "tsv_distinct_names": len(tsv_names),
        "names_only_in_probes": sorted(probe_names - tsv_names)[:50],
        "names_only_in_tsv": sorted(tsv_names - probe_names)[:50],
        "names_exact_match": probe_names == tsv_names,
        "probe_duplicate_names": len(dup_probe),
        "audit_duplicate_names": len(dup_audit),
        "duplicate_sets_equal": dup_probe == dup_audit,
        "duplicates_only_in_probes": sorted(dup_probe - dup_audit)[:50],
        "duplicates_only_in_audit": sorted(dup_audit - dup_probe)[:50],
        "kind_mismatches": kind_mismatch[:50],
        "kind_mismatch_count": len(kind_mismatch),
        "module_decl_count_mismatches": module_count_mismatch[:50],
        "module_decl_count_mismatch_count": len(module_count_mismatch),
        "probe_kind_histogram": {k: sum(1 for n, kk in per_name_kind.items() if kk == k)
                                 for k in sorted(set(per_name_kind.values()))},
        "tsv_kind_histogram": kinds,
    }
    out = os.path.join(WT, "baseline/audit/probe-inventory-crosscheck.json")
    json.dump(report, open(out, "w"), indent=1)
    print(json.dumps({k: v for k, v in report.items()
                      if k not in ("names_only_in_probes", "names_only_in_tsv",
                                   "duplicates_only_in_probes", "duplicates_only_in_audit",
                                   "kind_mismatches", "module_decl_count_mismatches")}, indent=1))


if __name__ == "__main__":
    sys.exit(main())
