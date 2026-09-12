#!/usr/bin/env python3
"""
L4-child-ricci-to-doubling — independent verification driver.

Runs, and records as machine-readable evidence in `evidence/`:

  1. provenance: sha256 of every consumed round-3/D12 source in this worktree AND of the
     original file it was copied from (match/mismatch), plus the new files;
  2. a full `lake build` of the consumed modules + the new module (exit code, log);
  3. the fail-closed axiom audit `Audit/RicciToDoublingAudit.lean` (per-declaration
     `Lean.collectAxioms` cones, all required to be subsets of
     {propext, Classical.choice, Quot.sound}), with the full `#check` signature output;
  4. the planted negative control `negcontrol/NegativeControl.lean` (proves the audit
     predicate catches `sorryAx` and `native_decide`);
  5. the D5 comment/string-aware forbidden-token scan of the new sources (via the
     canonical `input/d5-tools/scan_forbidden.py`);
  6. a `**Class:**` label scan: every declaration in the new mathematical file must carry an
     explicit model/manifold classification line in its docstring.

Exit code 0 iff every gate passes.  Writes `evidence/ricci-to-doubling-verify.json`.
"""
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
import datetime

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-ricci-to-doubling"
REL = os.path.join(WT, "release")
EV = os.path.join(WT, "evidence")
LOG = os.path.join(WT, "logs")
ELAN = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV = dict(os.environ)
ENV["ELAN_HOME"] = ELAN
ENV["PATH"] = os.path.join(ELAN, "bin") + ":" + ENV.get("PATH", "")

NEW_FILE = "release/Poincare/L4/Compactness/RicciToDoubling.lean"
NEW_FILE_HYP = "release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean"
AUDIT_FILE = "release/Audit/RicciToDoublingAudit.lean"
AUDIT_FILE_HYP = "release/Audit/RicciToDoublingHyperbolicAudit.lean"
AUDITS = [(AUDIT_FILE, 13, "ricci-to-doubling-axiom-audit.log"),
          (AUDIT_FILE_HYP, 21, "ricci-to-doubling-hyperbolic-axiom-audit.log")]
# Labelled declarations include the two private hyperbolic helpers (audited indirectly).
LABEL_TOTAL = 36

# (worktree-relative consumed copy, immediate origin, ultimate origin or None)
CONSUMED = [
    ("release/Poincare/D12/ComparisonGeodesics/Definitions.lean",
     "/data1/guoshaoyang/offload/worktrees/D12-comparison-geodesics/release/Poincare/D12/ComparisonGeodesics/Definitions.lean", None),
    ("release/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean",
     "/data1/guoshaoyang/offload/worktrees/D12-comparison-geodesics/release/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean", None),
    ("release/Poincare/D12/ComparisonGeodesics/SturmComparison.lean",
     "/data1/guoshaoyang/offload/worktrees/D12-comparison-geodesics/release/Poincare/D12/ComparisonGeodesics/SturmComparison.lean", None),
    ("release/Poincare/D12/ComparisonGeodesics/VolumeRatio.lean",
     "/data1/guoshaoyang/offload/worktrees/D12-comparison-geodesics/release/Poincare/D12/ComparisonGeodesics/VolumeRatio.lean", None),
    ("release/Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean",
     "/data1/guoshaoyang/offload/worktrees/D12-comparison-geodesics/release/Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean", None),
    ("release/Poincare/D12/GeometricCompactness/Basic.lean",
     "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path/release/Poincare/D12/GeometricCompactness/Basic.lean",
     "/data1/guoshaoyang/offload/worktrees/D12-geometric-compactness/release/Poincare/D12/GeometricCompactness/Basic.lean"),
    ("release/Poincare/D12/GeometricCompactness/Criterion.lean",
     "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path/release/Poincare/D12/GeometricCompactness/Criterion.lean",
     "/data1/guoshaoyang/offload/worktrees/D12-geometric-compactness/release/Poincare/D12/GeometricCompactness/Criterion.lean"),
    ("release/Poincare/L4/Compactness/CoveringStability.lean",
     "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path/release/Poincare/L4/Compactness/CoveringStability.lean", None),
    ("release/Poincare/L4/Compactness/DoublingToCovers.lean",
     "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path/release/Poincare/L4/Compactness/DoublingToCovers.lean", None),
    ("release/Poincare/L4/Compactness/MeasureGrowthCovers.lean",
     "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L4-geometric-critical-path/release/Poincare/L4/Compactness/MeasureGrowthCovers.lean", None),
]

APPROVED = ["propext", "Classical.choice", "Quot.sound"]


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run(cmd, cwd, logname):
    os.makedirs(LOG, exist_ok=True)
    logpath = os.path.join(LOG, logname)
    with open(logpath, "w") as f:
        p = subprocess.run(cmd, cwd=cwd, env=ENV, stdout=f, stderr=subprocess.STDOUT)
    return p.returncode, logpath, open(logpath, encoding="utf-8", errors="replace").read()


def main():
    os.makedirs(EV, exist_ok=True)
    result = {
        "schema": "l4-child-ricci-to-doubling/verify-v1",
        "task_id": "L4-child-ricci-to-doubling",
        "worktree": WT,
        "generated_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "gates": {},
        "pass": True,
    }

    def fail(gate, msg):
        result["pass"] = False
        result["gates"].setdefault(gate, {})["error"] = msg

    # ---- 1. provenance hashes -------------------------------------------------
    prov = []
    for rel, orig, ult in CONSUMED:
        cur = os.path.join(WT, rel)
        entry = {"file": rel, "immediate_origin": orig, "ultimate_origin": ult,
                 "worktree_sha256": sha256(cur) if os.path.exists(cur) else None,
                 "immediate_origin_sha256": sha256(orig) if os.path.exists(orig) else None}
        entry["match"] = entry["worktree_sha256"] == entry["immediate_origin_sha256"]
        if ult is not None:
            entry["ultimate_origin_sha256"] = sha256(ult) if os.path.exists(ult) else None
            entry["ultimate_match"] = (entry["worktree_sha256"] == entry["ultimate_origin_sha256"])
        prov.append(entry)
        if not entry["match"]:
            fail("provenance", f"consumed source differs from its immediate origin: {rel}")
        if ult is not None and not entry["ultimate_match"]:
            fail("provenance", f"consumed source differs from its ultimate origin: {rel}")
    new_hashes = {}
    for rel in (NEW_FILE, NEW_FILE_HYP, AUDIT_FILE, AUDIT_FILE_HYP):
        new_hashes[rel] = sha256(os.path.join(WT, rel))
    result["gates"]["provenance"] = {"consumed": prov, "new_file_sha256": new_hashes,
                                     "all_consumed_match_origin": all(e["match"] for e in prov)}
    if not result["gates"]["provenance"]["all_consumed_match_origin"]:
        fail("provenance", "at least one consumed source is not byte-identical to its origin")

    # ---- 2. build -------------------------------------------------------------
    targets = [
        "Poincare.D12.ComparisonGeodesics.ModelEuclidean",
        "Poincare.D12.ComparisonGeodesics.VolumeRatio",
        "Poincare.L4.Compactness.CoveringStability",
        "Poincare.L4.Compactness.DoublingToCovers",
        "Poincare.L4.Compactness.MeasureGrowthCovers",
        "Poincare.L4.Compactness.RicciToDoubling",
        "Poincare.L4.Compactness.RicciToDoublingHyperbolic",
    ]
    rc, buildlog, out = run(["lake", "build"] + targets, REL, "ricci-to-doubling-build.log")
    result["gates"]["build"] = {
        "command": "lake build " + " ".join(targets),
        "exit_code": rc,
        "log": os.path.relpath(buildlog, WT),
        "tail": out.strip().splitlines()[-6:],
    }
    if rc != 0:
        fail("build", f"lake build exit {rc}")

    # ---- 3. fail-closed axiom audit + signatures ------------------------------
    cones = {}
    audit_pass = True
    signature_output_present = True
    audit_logs = {}
    for audit_file, expected_here, logname in AUDITS:
        rel_audit = os.path.relpath(os.path.join(WT, audit_file), REL)
        rc, auditlog, out = run(["lake", "env", "lean", rel_audit], REL, logname)
        audit_logs[audit_file] = os.path.relpath(auditlog, WT)
        notes = []
        for line in out.splitlines():
            m = re.match(r"^AXIOM-JSON (Poincare\.L4\.Compactness\.[A-Za-z0-9_.]+): (.*)$", line.strip())
            if m:
                ax = [a for a in m.group(2).split(",") if a]
                cones[m.group(1)] = ax
        if rc != 0:
            audit_pass = False
            notes.append(f"exit {rc}")
        if "AXIOM-AUDIT PASS" not in out:
            audit_pass = False
            notes.append("PASS line missing")
        if not out.strip():
            signature_output_present = False
            notes.append("no output")
        copy_log = os.path.join(EV, os.path.basename(logname).replace("axiom-audit", "audit-full"))
        with open(copy_log, "w") as f:
            f.write(out)
        audit_logs[audit_file + "#notes"] = notes
    bad_cones = {d: [a for a in ax if a not in APPROVED] for d, ax in cones.items()
                 if any(a not in APPROVED for a in ax)}
    declared_total = sum(n for _, n, _ in AUDITS)
    if len(cones) != declared_total:
        audit_pass = False
    result["gates"]["axiom_audit"] = {
        "commands": [f"lake env lean {f}" for f, _, _ in AUDITS],
        "approved": APPROVED,
        "declaration_count": len(cones),
        "expected_declaration_count": declared_total,
        "cones": cones,
        "unapproved_cones": bad_cones,
        "pass_line_present": audit_pass,
        "logs": audit_logs,
        "signature_output_present": signature_output_present,
    }
    if not audit_pass:
        fail("axiom_audit", f"axiom audit did not pass (count {len(cones)} != {declared_total}, exit, or PASS line)")
    if bad_cones:
        fail("axiom_audit", f"unapproved axiom cones: {bad_cones}")

    # ---- 4. negative control --------------------------------------------------
    rc, nclog, out = run(["lake", "env", "lean", "../negcontrol/NegativeControl.lean"], REL,
                         "ricci-to-doubling-negative-control.log")
    nc_pass = (rc == 0 and "sorryAx" in out and "PASS" in out)
    result["gates"]["negative_control"] = {
        "command": "lake env lean ../negcontrol/NegativeControl.lean",
        "exit_code": rc,
        "detected_sorryAx": "sorryAx" in out,
        "pass_line_present": "PASS" in out,
        "log": os.path.relpath(nclog, WT),
        "tail": out.strip().splitlines()[-4:],
    }
    if not nc_pass:
        fail("negative_control", "negative control did not demonstrate detection of sorryAx/native_decide")

    # ---- 5. forbidden-token scan ---------------------------------------------
    spec = importlib.util.spec_from_file_location(
        "scan_forbidden", os.path.join(WT, "input/d5-tools/scan_forbidden.py"))
    sf = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(sf)
    matches = []
    for rel in (NEW_FILE, NEW_FILE_HYP, AUDIT_FILE, AUDIT_FILE_HYP):
        for m in sf.scan_file(os.path.join(WT, rel)):
            m["file"] = rel
            matches.append(m)
    hard = [m for m in matches if m["hard"]]
    result["gates"]["forbidden_scan"] = {
        "scanner": "input/d5-tools/scan_forbidden.py (comment/string-aware)",
        "files": [NEW_FILE, NEW_FILE_HYP, AUDIT_FILE, AUDIT_FILE_HYP],
        "hard_forbidden": sf.HARD,
        "hard_match_count": len(hard),
        "hard_matches": hard,
        "soft_flags": [m for m in matches if not m["hard"]],
    }
    if hard:
        fail("forbidden_scan", f"{len(hard)} hard-forbidden token occurrences")

    # ---- 6. classification-label scan ----------------------------------------
    decl_re = re.compile(
        r"^(?:private\s+)?(?:protected\s+)?(?:noncomputable\s+)?"
        r"(?:theorem|lemma|def|abbrev|structure)\s+([A-Za-z_][A-Za-z0-9_'.]*)")
    decls = []
    for rel in (NEW_FILE, NEW_FILE_HYP):
        lines = open(os.path.join(WT, rel), encoding="utf-8").read().splitlines()
        for i, line in enumerate(lines):
            m = decl_re.match(line)
            if m:
                j = i - 1
                while j >= 0 and lines[j].strip() == "":
                    j -= 1
                start = j
                while start >= 0 and not lines[start].strip().startswith("/--"):
                    start -= 1
                doc = "\n".join(lines[start:i]) if start >= 0 else ""
                cm = re.search(r"\*\*Class:\*\*\s*(.+)", doc)
                decls.append({"file": rel, "name": m.group(1), "line": i + 1,
                              "has_class_label": cm is not None,
                              "class": cm.group(1).strip() if cm else None})
    unlabeled = [d for d in decls if not d["has_class_label"]]
    result["gates"]["classification_labels"] = {
        "declarations": decls,
        "declaration_count": len(decls),
        "unlabeled": unlabeled,
    }
    audited_names = {d.split(".")[-1] for d in cones}
    labelled_names = {d["name"] for d in decls}
    missing_from_labels = sorted(audited_names - labelled_names)
    result["gates"]["classification_labels"]["audited_names_missing_from_label_scan"] = missing_from_labels
    if unlabeled or len(decls) != LABEL_TOTAL or missing_from_labels:
        fail("classification_labels",
             f"{len(unlabeled)} unlabeled; count {len(decls)} != {LABEL_TOTAL}; "
             f"audited names missing from label scan: {missing_from_labels}")

    with open(os.path.join(EV, "ricci-to-doubling-verify.json"), "w") as f:
        json.dump(result, f, indent=1)
    print(json.dumps({k: (v.get("error", "PASS") if isinstance(v, dict) else v)
                      for k, v in result["gates"].items()}, indent=1))
    print("OVERALL:", "PASS" if result["pass"] else "FAIL")
    return 0 if result["pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
