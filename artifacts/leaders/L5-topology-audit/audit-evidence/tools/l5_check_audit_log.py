#!/usr/bin/env python3
"""L5 topology audit — fail-closed post-processing of the two positive audit logs.

Usage: l5_check_audit_log.py <logA> <logB> <collisions.json> <out-summary.json>

Fails (nonzero exit) unless: both passes report `L5VERDICT PASS`, neither has an `L5PKGFAIL`
line or an `error` line, and the union of the two passes' imported-package module lists
covers every module recorded in `collisions.json`.
"""
import json
import pathlib
import sys
from collections import defaultdict


def parse(text):
    lines = text.splitlines()

    def rows(tag):
        return [ln.split("\t") for ln in lines if ln.startswith(tag + "\t")]

    d = {
        "pkg": {r[1]: r[2] for r in rows("L5PKG") if len(r) >= 3},
        "fails": rows("L5PKGFAIL"),
        "neg": rows("L5NEGCLUSTER"),
        "verdicts": [r[1] for r in rows("L5VERDICT")],
        "mods": [r[1] for r in rows("L5MOD") if len(r) >= 2 and r[1] not in ("imported_total", "imported_package")],
        "decl": rows("L5DECL"),
        "types": {r[1]: r[3] for r in rows("L5TYPE") if len(r) >= 4},
        "props": [r[1] for r in rows("L5PROP")],
        "equiv": [r for r in rows("L5EQUIV") if len(r) > 2 and r[1] == "HIT"],
        "uses": {r[1]: {"kind": r[2], "consumers": int(r[3]), "sample": r[4] if len(r) > 4 else ""}
                 for r in rows("L5USE") if len(r) >= 4 and not r[1].startswith("lane_")},
        "lane_meta": {r[1]: r[2] for r in rows("L5USE") if len(r) >= 3 and r[1].startswith("lane_")},
        "errors": [ln for ln in lines if ln.startswith("error")],
    }
    return d


def main() -> int:
    logA, logB, coll_path, out_path = (pathlib.Path(sys.argv[i]) for i in range(1, 5))
    A = parse(logA.read_text(encoding="utf-8", errors="replace"))
    B = parse(logB.read_text(encoding="utf-8", errors="replace"))
    coll = json.loads(coll_path.read_text())
    all_mods = set(coll["partition"]["side_a_modules_importing_first_of_a_pair"]) | \
        set(coll["partition"]["side_b_modules_importing_second_of_a_pair"]) | \
        set(coll["partition"]["clean_modules"])
    seen = set(A["mods"]) | set(B["mods"])

    module_prefix_counts = defaultdict(int)
    for r in A["decl"]:
        name = r[1]
        for pref in ("Poincare.D12.SurgeryRecognition.", "Poincare.D12.TriangulationTopology.",
                     "Poincare.D10.TriangulationLowDim.", "Poincare.D7.Recognition.",
                     "Poincare.D7.SurgeryFlow.", "Poincare.D7.Limit.", "Poincare.VKPort.",
                     "Poincare.D13.CriticalPathReview.", "Poincare.Stage6.", "Poincare.Longrun.Surgery.",
                     "Poincare.Longrun.Topology.", "Poincare.D8.Fidelity.", "Poincare.D12.SemanticLedger."):
            if name.startswith(pref):
                module_prefix_counts[pref.rstrip(".")] += 1
                break

    def cone_counts(d):
        c = defaultdict(int)
        for r in d["decl"]:
            c[r[3] if len(r) > 3 else "?"] += 1
        return dict(c)

    summary = {
        "logs": [str(logA), str(logB)],
        "verdict_pass_A": any("PASS" in v for v in A["verdicts"]),
        "verdict_pass_B": any("PASS" in v for v in B["verdicts"]),
        "package_A": A["pkg"],
        "package_B": B["pkg"],
        "package_failures_A": ["\t".join(r) for r in A["fails"]],
        "package_failures_B": ["\t".join(r) for r in B["fails"]],
        "error_lines_A": A["errors"],
        "error_lines_B": B["errors"],
        "negative_control_registry_A": ["\t".join(r) for r in A["neg"]],
        "negative_control_registry_B": ["\t".join(r) for r in B["neg"]],
        "module_coverage": {
            "modules_total": len(all_mods),
            "modules_in_pass_A": len(A["mods"]),
            "modules_in_pass_B": len(B["mods"]),
            "modules_in_union": len(seen),
            "modules_missing_from_both": sorted(all_mods - seen),
            "union_covers_all": all_mods <= seen,
        },
        "lane_declarations_by_prefix_A": dict(sorted(module_prefix_counts.items())),
        "lane_declaration_rows_A": len(A["decl"]),
        "lane_cone_histogram_A": cone_counts(A),
        "lane_meta_A": A["lane_meta"],
        "statement_only_props_A": A["props"],
        "conclusion_equivalent_hypotheses_A": ["\t".join(r) for r in A["equiv"]],
        "collisions": {
            "duplicate_declaration_names": coll["duplicate_declaration_names"],
            "colliding_module_pairs": coll["colliding_module_pairs"],
            "self_conflicting_modules": coll["self_conflicting_modules"],
        },
        "retained_consumer_counts_A": A["uses"],
    }
    checks = {
        "verdict_pass_A": summary["verdict_pass_A"],
        "verdict_pass_B": summary["verdict_pass_B"],
        "no_failures_A": len(A["fails"]) == 0,
        "no_failures_B": len(B["fails"]) == 0,
        "no_error_lines_A": len(A["errors"]) == 0,
        "no_error_lines_B": len(B["errors"]) == 0,
        "union_covers_all_modules": summary["module_coverage"]["union_covers_all"],
        "negative_controls_present": any(len(r) >= 4 and r[2] == "present=true"
                                         for r in A["neg"]),
    }
    summary["checks"] = checks
    summary["assertions_ok"] = all(checks.values())
    out_path.write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps(checks, indent=1))
    print("assertions_ok:", summary["assertions_ok"])
    return 0 if summary["assertions_ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
