#!/usr/bin/env python3
"""D13 integrated kernel audit — evidence driver.

Parses the audit logs produced by
  * `lake env lean Poincare/D13/IntegratedAudit/KernelAudit.lean`  (expected PASS)
  * `lake env lean ../audit-evidence/negcontrol/NegativeControlIncluded.lean` (expected FAIL)
and performs the independent checks that do not need a Lean process:

  C1  every expected clean module present; every audited declaration attributed to a module
  C2  axiom cones: only {propext, Classical.choice, Quot.sound}; no axiom/unsafe/sorry/native/proof_wanted
  C3  collision freedom: no name declared by the negative-control modules collides with a clean
      declaration or with the other negative-control module (all clean modules are already
      merged into one environment by SnapshotRoot, so Lean itself rules out duplicates there)
  C4  negative control: the detector flagged both forbidden axioms and nothing else
  C5  type inventory is complete (one D13TYPE line per D13DECL line)

Writes audit-evidence/kernel-audit.json and prints a PASS/FAIL summary.
"""
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

WT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit")
EVID = WT / "audit-evidence"
APPROVED = {"propext", "Classical.choice", "Quot.sound"}


def parse_log(path: Path):
    decls, types, audit, fails, notes, verdict = {}, {}, {}, [], [], None
    for line in path.read_text(errors="replace").splitlines():
        parts = line.split("\t")
        if parts[0] == "D13DECL" and len(parts) >= 5:
            name, kind, module, cone = parts[1], parts[2], parts[3], parts[4]
            decls[name] = {"kind": kind, "module": module,
                           "cone": [c for c in cone.split(";") if c]}
        elif parts[0] == "D13TYPE" and len(parts) >= 5:
            types[parts[1]] = {"kind": parts[2], "module": parts[3], "type": "\t".join(parts[4:])}
        elif parts[0] == "D13AUDIT" and len(parts) >= 3:
            audit[parts[1]] = parts[2]
        elif parts[0] == "D13FAIL":
            fails.append(parts[1:])
        elif parts[0] == "D13NOTE":
            notes.append(parts[1:])
        elif parts[0] == "D13VERDICT":
            verdict = parts[1]
    return {"decls": decls, "types": types, "audit": audit, "fails": fails,
            "notes": notes, "verdict": verdict}


def main() -> int:
    result = {"checks": {}, "problems": []}
    pos = parse_log(EVID / "logs" / "kernel-audit-02.log")
    neg = parse_log(EVID / "logs" / "negcontrol-included.log")

    # ---- C1 completeness -------------------------------------------------------
    a = pos["audit"]
    c1 = (int(a.get("missing_modules", -1)) == 0 and int(a.get("duplicate_module_names", -1)) == 0
          and int(a.get("declarations_audited", 0)) > 0
          and int(a.get("expected_clean_modules", 0)) > 0)
    result["checks"]["C1_completeness"] = {
        "pass": c1, "expected_clean_modules": a.get("expected_clean_modules"),
        "missing_modules": a.get("missing_modules"), "duplicate_module_names": a.get("duplicate_module_names"),
        "declarations_audited": a.get("declarations_audited"), "theorems": a.get("theorems")}
    if not c1:
        result["problems"].append("C1 completeness failed")

    # every declaration's module must be a D11/D12 module
    bad_module = [n for n, d in pos["decls"].items() if not (d["module"].startswith("Poincare.D11") or d["module"].startswith("Poincare.D12"))]
    result["checks"]["C1b_module_attribution"] = {"pass": not bad_module, "offenders": bad_module[:10]}
    if bad_module:
        result["problems"].append("C1b: declarations outside D11/D12 scope")

    # ---- C2 axiom cones --------------------------------------------------------
    viol = {n: d for n, d in pos["decls"].items() if not set(d["cone"]) <= APPROVED}
    kinds = Counter(d["kind"] for d in pos["decls"].values())
    cones = Counter(";".join(d["cone"]) for d in pos["decls"].values())
    c2 = (not viol and kinds.get("axiom", 0) == 0 and kinds.get("unsafe_def", 0) == 0
          and int(a.get("sorry_declarations", -1)) == 0 and int(a.get("native_decide_declarations", -1)) == 0
          and int(a.get("unapproved_axiom_declarations", -1)) == 0
          and int(a.get("proof_wanted_declarations", -1)) == 0
          and int(a.get("collect_axioms_failures", -1)) == 0)
    result["checks"]["C2_axiom_cones"] = {
        "pass": c2, "violations": {n: d["cone"] for n, d in list(viol.items())[:20]},
        "kind_histogram": dict(kinds), "cone_histogram": dict(cones),
        "partial_defs": [n for n, d in pos["decls"].items() if d["kind"] == "partial_def"]}
    if not c2:
        result["problems"].append("C2 axiom-cone violation")

    # ---- C3 collision freedom --------------------------------------------------
    clean_names = set(pos["decls"])
    neg_by_module = defaultdict(dict)
    for n, d in neg["decls"].items():
        if d["module"].startswith("Poincare.D12.TriangulationTopology.NegControl") or d["module"] == "Poincare.D12.VolumeIBP.Audit":
            neg_by_module[d["module"]][n] = d
    collisions = []
    for mod, decls in neg_by_module.items():
        for n in decls:
            if n in clean_names:
                collisions.append({"name": n, "neg_module": mod, "also_clean_module": pos["decls"][n]["module"]})
    # also compare the negative-control modules against each other
    neg_all = sorted(neg_by_module)
    for i in range(len(neg_all)):
        for j in range(i + 1, len(neg_all)):
            for n in set(neg_by_module[neg_all[i]]) & set(neg_by_module[neg_all[j]]):
                collisions.append({"name": n, "neg_module": neg_all[i], "also_clean_module": neg_all[j]})
    result["checks"]["C3_collisions"] = {
        "pass": not collisions, "collisions": collisions,
        "clean_declaration_names": len(clean_names),
        "negative_control_declarations": {m: sorted(d) for m, d in neg_by_module.items()}}
    if collisions:
        result["problems"].append("C3 name collision")

    # ---- C4 negative control fires --------------------------------------------
    flagged_axioms = sorted({f[1] for f in neg["fails"] if f[0] == "project_axiom"})
    flagged_unapproved = sorted({(f[1], f[2]) for f in neg["fails"] if f[0] == "unapproved_axiom"})
    c4 = (neg["verdict"] is not None and neg["verdict"].startswith("FAIL")
          and flagged_axioms == ["Poincare.D12.VolumeIBP.Audit.negativeControl", "d12NegControlBadAxiom"]
          and (("d12NegControlBadTheorem", "d12NegControlBadAxiom") in flagged_unapproved))
    result["checks"]["C4_negative_control"] = {
        "pass": c4, "verdict": neg["verdict"], "flagged_axioms": flagged_axioms,
        "flagged_unapproved": [list(x) for x in flagged_unapproved]}
    if not c4:
        result["problems"].append("C4 negative control did not fire as expected")

    # ---- C5 type inventory -----------------------------------------------------
    missing_types = sorted(set(pos["decls"]) - set(pos["types"]))
    extra_types = sorted(set(pos["types"]) - set(pos["decls"]))
    empty_types = sorted(n for n, t in pos["types"].items() if not t["type"].strip())
    c5 = not missing_types and not extra_types and not empty_types
    result["checks"]["C5_type_inventory"] = {
        "pass": c5, "decls": len(pos["decls"]), "types": len(pos["types"]),
        "missing": missing_types[:10], "extra": extra_types[:10], "empty": empty_types[:10]}
    if not c5:
        result["problems"].append("C5 type inventory incomplete")

    result["positive_log"] = str((EVID / "logs" / "kernel-audit-02.log").relative_to(WT))
    result["negative_log"] = str((EVID / "logs" / "negcontrol-included.log").relative_to(WT))
    result["pass"] = not result["problems"]
    (EVID / "kernel-audit.json").write_text(json.dumps(result, indent=1) + "\n")
    for k, v in result["checks"].items():
        print(f"{k}: {'PASS' if v['pass'] else 'FAIL'}")
    print("PROBLEMS:", result["problems"] if result["problems"] else "none")
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
