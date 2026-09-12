#!/usr/bin/env python3
"""Continuation-invocation verification of the L1 baseline evidence.

Read-only over the preserved artifacts: recomputes hashes, re-checks log
verdicts, and re-derives partition coverage.  Writes only the two report
files named on the command line (default baseline/logs/verify-baseline.*).

This is a same-agent re-check, NOT independent verification; the card says so.
"""
import glob
import hashlib
import json
import os
import re
import sys
import time

WT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
checks = []


def check(cid, ok, detail):
    checks.append({"id": cid, "ok": bool(ok), "detail": detail})
    print(("PASS " if ok else "FAIL ") + cid + " :: " + str(detail)[:300])


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def rel(p):
    return os.path.join(WT, p)


# ---- A. evidence manifest integrity -------------------------------------
man = json.load(open(rel("baseline/MANIFEST.json")))
bad = []
missing = []
for e in man["files"]:
    p = rel(e["path"])
    if not os.path.exists(p):
        missing.append(e["path"])
        continue
    if os.path.getsize(p) != e["bytes"] or sha256(p) != e["sha256"]:
        bad.append(e["path"])
check("A1_manifest_files_present", not missing, {"entries": len(man["files"]), "missing": missing})
check("A2_manifest_hashes_match", not bad, {"entries": len(man["files"]), "mismatched": bad})

# ---- B. release tree frozen-hash re-check --------------------------------
drift = json.load(open(rel("baseline/reconcile/source-hash-drift.json")))
cur = drift["current_hashes"]
changed, vanished, new = [], [], []
seen = set()
for dirpath, dirnames, filenames in os.walk(rel("release")):
    dirnames[:] = [d for d in dirnames if d != ".lake"]
    for f in filenames:
        p = os.path.join(dirpath, f)
        r = os.path.relpath(p, rel("release"))
        seen.add(r)
        if r not in cur:
            new.append(r)
        elif sha256(p) != cur[r]:
            changed.append(r)
vanished = sorted(set(cur) - seen)
check("B1_release_files_unchanged", not changed and not vanished and not new,
      {"frozen": len(cur), "on_disk": len(seen), "changed": changed, "removed": vanished, "added": new})

# ---- C. build / audit log verdicts ---------------------------------------
clean = open(rel("baseline/logs/clean-build.log"), errors="replace").read()
check("C1_clean_build_success",
      "Build completed successfully (9339 jobs)." in clean,
      {"marker": "Build completed successfully (9339 jobs).",
       "errors": len(re.findall(r"^error:", clean, re.M))})
n_sorry_warn = clean.count("declaration uses 'sorry'")
check("C1b_no_sorry_warnings", n_sorry_warn == 0,
      {"declaration_uses_sorry": n_sorry_warn,
       "warnings": len(re.findall(r"warning:", clean)),
       "note": "the 10 raw 'sorry' substrings in the log are audit lines (sorryAx counts = 0) and the def name Poincare.D13.IntegratedAudit.sorryAxiom"})
for part, decls in (("G1", 12071), ("G2", 472)):
    log = open(rel(f"baseline/logs/axiom-audit-{part}.log"), errors="replace").read()
    tail = log[-4000:]
    ok = ("L1AXVERDICT\tPASS" in tail
          and f"L1SUM\tdeclarations\t{decls}" in tail
          and "L1SUM\tunexpected_violations\t0" in tail
          and "L1SUM\tsorry\t0" in tail
          and "L1SUM\tunsafe\t0" in tail
          and "L1SUM\tnative\t0" in tail)
    check(f"C2_axiom_audit_{part}_PASS", ok, {"log": f"baseline/logs/axiom-audit-{part}.log"})
for mod, n in (("D6LedgerProbe", 262), ("ReleaseClaims", 193)):
    log = open(rel(f"baseline/logs/lean-{mod}.log"), errors="replace").read()
    errs = len(re.findall(r"^.*error", log, re.M))
    check(f"C3_driver_{mod}", errs == 0,
          {"error_lines": errs,
           "check_cmds": len([l for l in open(rel('release/' + mod + '.lean')) if l.startswith('#check')])})

# ---- D. forbidden-token scan ---------------------------------------------
fs = json.load(open(rel("baseline/logs/forbidden-scan.json")))
check("D1_forbidden_scan_two_controls",
      fs["files_scanned"] == 456 and fs["raw_hits_total"] == 2 and fs["declaration_form_hits_total"] == 2,
      {"files": fs["files_scanned"], "raw": fs["raw_hits_total"], "decl": fs["declaration_form_hits_total"]})

# ---- E. partition coverage -------------------------------------------------
part = json.load(open(rel("baseline/audit/partition.json")))
groups = part["groups"]
gmods = {g: set(v["modules"] if isinstance(v, dict) and "modules" in v else v) for g, v in groups.items()}
union = set().union(*gmods.values())
inter = set(gmods["G1"]) & set(gmods["G2"]) if len(gmods) > 1 else set()
check("E1_partitions_disjoint", not inter, {"intersection": sorted(inter)[:10], "n": len(inter)})
check("E2_total_modules_454", part["total_modules"] == 454 and len(union) == 454,
      {"declared": part["total_modules"], "union": len(union)})

# every module that produced an olean in release/.lake/build must be in the partition
built = set()
libdir = rel("release/.lake/build/lib/lean")
for dirpath, _dirnames, filenames in os.walk(libdir):
    for f in filenames:
        if f.endswith(".olean"):
            r = os.path.relpath(os.path.join(dirpath, f), libdir)[:-6].replace(os.sep, ".")
            built.add(r)
outside = sorted(built - union)
check("E3_all_built_modules_partitioned", not outside,
      {"built_oleans": len(built), "outside_partition": outside[:10], "n_outside": len(outside)})

# ---- F. declaration table sanity ------------------------------------------
audit = json.load(open(rel("baseline/audit/axiom-audit.json")))
rows = 0
names = set()
kinds = {}
cones = {}
with open(rel("baseline/audit/declarations.tsv")) as f:
    header = f.readline().rstrip("\n").split("\t")
    for line in f:
        p = line.rstrip("\n").split("\t")
        rows += 1
        names.add(p[0])
        kinds[p[1]] = kinds.get(p[1], 0) + 1
        cones[p[3]] = cones.get(p[3], 0) + 1
check("F1_tsv_rows_equal_distinct_names",
      rows == 12361 and len(names) == 12361 and len(audit["declarations"]) == 12361,
      {"tsv_rows": rows, "distinct": len(names), "audit_dict": len(audit["declarations"])})
check("F2_partition_row_sum_12543_distinct_12361",
      12071 + 472 == 12543 and audit["summary"]["declarations"] == 12361,
      {"partition_row_sum": 12071 + 472, "summary_distinct": audit["summary"]["declarations"]})
check("F3_no_forbidden_kinds", kinds.get("axiom", 0) == 2 and kinds.get("unsafe_def", 0) == 0,
      {"kind_histogram": kinds})
check("F4_duplicate_partition_153_29_182",
      len(audit["duplicate_names"]) == 182 and len(audit["authored_duplicate_names"]) == 153
      and len(audit["generated_duplicate_names"]) == 29,
      {"duplicates": len(audit["duplicate_names"]),
       "authored": len(audit["authored_duplicate_names"]),
       "generated": len(audit["generated_duplicate_names"])})
check("F5_audit_summary_clean",
      audit["summary"]["unexpected_violations"] == 0
      and len(audit["summary"]["sorry_declarations"]) == 0
      and len(audit["summary"]["unsafe_declarations"]) == 0 and audit["errors"] == [],
      {"unexpected": audit["summary"]["unexpected_violations"],
       "sorry": len(audit["summary"]["sorry_declarations"]),
       "unsafe": len(audit["summary"]["unsafe_declarations"]),
       "errors": audit["errors"]})

# ---- H. rebuild determinism and preserved artifacts ------------------------
oleancmp = json.load(open(rel("baseline/pre-rebuild/olean-rebuild-comparison.json")))
common = oleancmp.get("common")
identical = oleancmp.get("identical")
differing = oleancmp.get("differing")
ndiff = len(differing) if isinstance(differing, list) else differing
check("H1_olean_determinism",
      common == 377 and identical == 377 and ndiff == 0 and oleancmp.get("pre_count") == 377,
      {"common": common, "identical": identical, "differing": ndiff,
       "only_pre": len(oleancmp.get("only_pre", [])), "only_post": len(oleancmp.get("only_post", []))})
first_built = [l for l in open(rel("baseline/pre-rebuild/modules-first-built-by-baseline.txt"))
               if l.strip()]
check("H2_modules_first_built_77",
      len(first_built) == 77 and len(oleancmp.get("only_post", [])) == 77,
      {"list_count": len(first_built), "only_post": len(oleancmp.get("only_post", []))})
tree = rel("baseline/pre-rebuild/build-tree")
n_olean = sum(1 for dp, _dn, fns in os.walk(tree) for f in fns if f.endswith(".olean"))
check("H3_preserved_build_tree_present", os.path.isdir(tree) and n_olean > 0,
      {"dir": "baseline/pre-rebuild/build-tree", "oleans": n_olean})

# ---- I. corrected dependency graph + probe cross-check (continuation) ------
dep_sums = {}
for part, decs, edg in (("G1", 12071, 73648), ("G2", 472, 2503)):
    txt = open(rel(f"baseline/logs/dep-audit-{part}.log"), errors="replace").read()
    dep_sums[part] = {"L2DEP_rows": txt.count("L2DEP\t"),
                      "done": "L2DEPVERDICT\tDONE" in txt[-2000:],
                      "declarations": f"L2SUM\tdeclarations\t{decs}" in txt,
                      "edges": f"L2SUM\tedges\t{edg}" in txt}
check("I1_dep_audit_v2_complete",
      all(v["done"] and v["declarations"] and v["edges"] for v in dep_sums.values()),
      dep_sums)
v2pairs = set()
with open(rel("baseline/audit/dep-edges-v2.tsv")) as f:
    f.readline()
    for line in f:
        v2pairs.add(tuple(line.rstrip("\n").split("\t")))
check("I2_dep_edges_v2_distinct_pairs", len(v2pairs) == 50433, {"distinct_pairs": len(v2pairs)})
cmp = json.load(open(rel("baseline/audit/downstream-use-comparison.json")))
want = {"Poincare.Longrun.Evolution.perelmanF_step_lt": 1,
        "Poincare.Longrun.Evolution.gibbsTerm_strictAnti": 25,
        "Poincare.Longrun.Evolution.gibbsTerm_step_lt": 3,
        "Poincare.D7.Recognition.stage6Target_of_certificates": 4,
        "d12NegControlBadAxiom": 1}
got = {t["name"]: t["v2_proof_level_count"] for t in cmp["targets"]}
check("I3_corrected_target_counts", all(got.get(k) == v for k, v in want.items()),
      {k: got.get(k) for k in want})
exits = {}
for f in glob.glob(rel("baseline/logs/probes/*.exit")):
    code = open(f).read().strip()
    exits[code] = exits.get(code, 0) + 1
pc = json.load(open(rel("baseline/audit/probe-inventory-crosscheck.json")))
check("I4_probe_sweep_complete_clean",
      exits.get("0") == 454 and len(exits) == 1 and pc["probe_modules_run"] == 343
      and len(pc["probe_logs_without_MD_rows"]) == 111,
      {"exit_codes": exits, "modules_with_declarations": pc["probe_modules_run"],
       "import_only": len(pc["probe_logs_without_MD_rows"])})
missed = open(rel("baseline/logs/missed-decl-cone-check.log"), errors="replace").read()
check("I5_missed_declaration_cones_clean",
      "MISSEDCONEVERDICT\tPASS" in missed and "unexpected=0" in missed,
      {"log": "baseline/logs/missed-decl-cone-check.log"})
res = json.load(open(rel("baseline/audit/probe-crosscheck-resolution.json")))
check("I6_probe_crosscheck_explained",
      res["coverage_after_resolution"]["unexplained_differences"] == 0
      and res["coverage_after_resolution"]["distinct_names_union_of_both_methods"] == 12364,
      res["coverage_after_resolution"])

# ---- G. result card consistency -------------------------------------------
card = json.load(open(rel("longrun/results/L1-lean-baseline.json")))
check("G1_card_verdict", card["verdict"] in ("TASK_DONE", "TASK_BLOCKED"), {"verdict": card["verdict"]})
refs = [v for v in card["evidence_files"].values() if isinstance(v, str) and "/" in v and not v.endswith("/")]
missing_refs = [r for r in refs if not os.path.exists(rel(r))]
check("G2_card_evidence_refs_exist", not missing_refs, {"refs": len(refs), "missing": missing_refs})

summary = {
    "generated_at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    "worktree": WT,
    "checks": checks,
    "passed": sum(1 for c in checks if c["ok"]),
    "failed": sum(1 for c in checks if not c["ok"]),
}
out_json = sys.argv[1] if len(sys.argv) > 1 else rel("baseline/logs/verify-baseline.json")
with open(out_json, "w") as f:
    json.dump(summary, f, indent=2, sort_keys=False)
print(f"\n{summary['passed']} passed, {summary['failed']} failed -> {out_json}")
sys.exit(1 if summary["failed"] else 0)
