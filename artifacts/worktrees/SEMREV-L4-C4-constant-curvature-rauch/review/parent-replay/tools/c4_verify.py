#!/usr/bin/env python3
"""L4-C4 fail-closed verification: hashes, forbidden-token scan, compile, axiom audit.

Run from the worktree root:

    python3 tools/c4_verify.py

Writes manifest/c4-verification.json and prints a human-readable summary.  Every gate is
fail-closed: a missing log line, an unexpected axiom cone, a forbidden token, or a non-zero
compile exit makes the script exit non-zero.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RELEASE = os.path.join(ROOT, "release")
LOGS = os.path.join(ROOT, "logs")
MANIFEST = os.path.join(ROOT, "manifest")
ELAN_HOME = "/data3/guoshaoyang/workdir/lean_poincare/elan"
L1 = ("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/"
      "leaders/L1-lean-baseline/release")

AUTHORED = [
    "release/Poincare/L4/GeodesicComparison/ConstCurvNormalization.lean",
    "release/Poincare/L4/GeodesicComparison/AxiomAudit.lean",
]
IMPORTED = [
    "release/Poincare/D10/JacobiConstantCurvature/Basic.lean",
    "release/Poincare/D10/JacobiConstantCurvature/ODE.lean",
    "release/Poincare/D10/JacobiConstantCurvature/Comparison.lean",
    "release/Poincare/D12/ComparisonGeodesics/Definitions.lean",
    "release/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean",
]
# canonical upstream location of every non-authored source (provenance check)
IMPORTED_ORIGIN = {
    "release/Poincare/D10/JacobiConstantCurvature/Basic.lean":
        f"{L1}/Poincare/D10/JacobiConstantCurvature/Basic.lean",
    "release/Poincare/D10/JacobiConstantCurvature/ODE.lean":
        f"{L1}/Poincare/D10/JacobiConstantCurvature/ODE.lean",
    "release/Poincare/D10/JacobiConstantCurvature/Comparison.lean":
        f"{L1}/Poincare/D10/JacobiConstantCurvature/Comparison.lean",
    "release/Poincare/D12/ComparisonGeodesics/Definitions.lean":
        f"{L1}/Poincare/D12/ComparisonGeodesics/Definitions.lean",
    "release/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean":
        f"{L1}/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean",
}

FORBIDDEN = [
    (r"\bsorry\b", "sorry"),
    (r"(?m)^\s*(private\s+|protected\s+|noncomputable\s+)*axiom\b", "axiom declaration"),
    (r"\badmit\b", "admit"),
    (r"\bunsafe\b", "unsafe"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bproof_wanted\b", "proof_wanted"),
]

AUDIT_DECLS = [
    "sin_sub_mul_cos_nonneg", "sin_sub_mul_cos_le_cube", "sphere_logDeriv_bound",
    "jacobiSolSphere_abs_le", "jacobiSolSphere_logDeriv_bound", "jacobiSol_logDeriv_bound",
    "jacobiSol_logDeriv_normalized", "jacobiSol_pos_of_nonneg",
    "jacobiSol_pos_of_nonneg_Ioc", "jacobiSol_riccati_identity",
    "abs_sub_le_of_deriv_bound", "jacobi_linear_bounds", "jacobi_pos_and_ratio_bound",
    "euclideanNormalizedOn_of_jacobi", "jacobi_riccati_identity",
    "logDeriv_continuousOn", "logDeriv_continuousOn_jacobi", "rauch_upper_of_constCurv",
    "rauch_upper_of_constCurv_jacobi", "rauch_upper_flat_of_jacobi",
    "sphere_jacobiSolutionOn_four_oneHalf", "spherical_rauch_witness",
    "spherical_rauch_witness_cot", "jacobiSolOne_normalization_witness",
    "jacobiSolOne_normalized", "flat_model_normalized",
]
AUDIT_ENGINE = [
    "riccati_le_of_singular_normalization", "riccati_le_of_initial", "riccati_delta_le_exp",
]
AUDIT_MODEL = [
    "jacobiSol_ode", "hasDerivAt_jacobiSol", "hasDerivAt_jacobiDeriv",
    "jacobiSolSphere_pos", "continuous_jacobiSol",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def run(cmd, cwd, log):
    with open(log, "w") as fh:
        fh.write("=== %s ===\n(cwd %s)\n" % (" ".join(cmd), cwd))
        fh.flush()
        p = subprocess.run(cmd, cwd=cwd, stdout=fh, stderr=subprocess.STDOUT,
                           env={**os.environ, "ELAN_HOME": ELAN_HOME,
                                "PATH": ELAN_HOME + "/bin:" + os.environ.get("PATH", "")})
    return p.returncode


def strip_comments(text):
    # block comments (nested) and line comments, replaced by spaces
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if depth == 0 and text.startswith("/-", i):
            depth = 1
            i += 2
            out.append("  ")
        elif depth > 0 and text.startswith("/-", i):
            depth += 1
            i += 2
            out.append("  ")
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            out.append("  ")
        elif depth > 0:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
        elif text.startswith("--", i):
            while i < len(text) and text[i] != "\n":
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


AXIOM_LINE = re.compile(
    r"^(?:info: )?.*?'([^']+)' depends on axioms: \[(.*?)\]", re.M | re.S)


def parse_axioms(log_path):
    text = open(log_path).read()
    # merge wrapped lines: entries continue with leading whitespace/commas
    text = re.sub(r"\n\s+", " ", text)
    found = {}
    for m in AXIOM_LINE.finditer(text):
        name = m.group(1)
        cone = [a.strip() for a in m.group(2).split(",") if a.strip()]
        found[name] = cone
    return found


def main():
    stamp = datetime.now(timezone.utc).isoformat()
    result = {"task_id": "L4-C4-constant-curvature-rauch", "generated_at": stamp,
              "gates": {}, "hashes": {}, "axiom_audit": {}, "ok": False}
    failures = []

    # ---- gate 1: hashes + provenance ------------------------------------------------
    for rel in AUTHORED + IMPORTED:
        result["hashes"][rel] = sha256(os.path.join(ROOT, rel))
    for rel in ["release/lakefile.toml", "release/lean-toolchain", "release/lake-manifest.json"]:
        result["hashes"][rel] = sha256(os.path.join(ROOT, rel))
    prov = {}
    for rel in IMPORTED:
        same = sha256(os.path.join(ROOT, rel)) == sha256(IMPORTED_ORIGIN[rel])
        prov[rel] = {"origin": IMPORTED_ORIGIN[rel], "unchanged": same}
        if not same:
            failures.append("provenance mismatch: " + rel)
    result["provenance"] = prov
    result["gates"]["provenance_unchanged"] = all(v["unchanged"] for v in prov.values())

    # ---- gate 2: forbidden tokens ---------------------------------------------------
    scan = {}
    hits = []
    for rel in AUTHORED:
        clean = strip_comments(open(os.path.join(ROOT, rel)).read())
        for pat, label in FORBIDDEN:
            n = len(re.findall(pat, clean))
            if n:
                hits.append({"file": rel, "token": label, "count": n})
        scan[rel] = "clean"
    result["forbidden_scan"] = {"hits": hits, "files": scan}
    result["gates"]["forbidden_tokens_clean"] = not hits
    if hits:
        failures.append("forbidden tokens: %s" % hits)

    # ---- gate 3: compile ------------------------------------------------------------
    os.makedirs(LOGS, exist_ok=True)
    os.makedirs(MANIFEST, exist_ok=True)
    cc = run(["lake", "build",
              "Poincare.L4.GeodesicComparison.ConstCurvNormalization",
              "Poincare.L4.GeodesicComparison.AxiomAudit"],
             cwd=RELEASE, log=os.path.join(LOGS, "c4-verify-build.log"))
    result["gates"]["compile_exit_zero"] = cc == 0
    result["compile"] = {"cmd": ("lake build Poincare.L4.GeodesicComparison."
                                 "ConstCurvNormalization Poincare.L4.GeodesicComparison."
                                 "AxiomAudit"),
                         "cwd": "release/", "exit": cc,
                         "log": "logs/c4-verify-build.log"}
    if cc != 0:
        failures.append("compile exit %d" % cc)

    # re-run the audit module to capture #print axioms output
    aa = run(["lake", "env", "lean", "Poincare/L4/GeodesicComparison/AxiomAudit.lean"],
             cwd=RELEASE, log=os.path.join(LOGS, "c4-verify-axioms.log"))
    result["axiom_run"] = {"cmd": "lake env lean Poincare/L4/GeodesicComparison/AxiomAudit.lean",
                           "cwd": "release/", "exit": aa, "log": "logs/c4-verify-axioms.log"}
    if aa != 0:
        failures.append("axiom audit run exit %d" % aa)

    cones = parse_axioms(os.path.join(LOGS, "c4-verify-axioms.log"))
    expected = {d: "authored" for d in AUDIT_DECLS}
    expected.update({d: "engine" for d in AUDIT_ENGINE})
    expected.update({d: "model" for d in AUDIT_MODEL})
    by_short = {k.rsplit(".", 1)[-1]: k for k in cones}
    missing = [d for d in expected if d not in by_short]
    bad = {d: c for d, c in cones.items() if not set(c) <= ALLOWED_AXIOMS}
    result["axiom_audit"] = {
        "expected_declarations": len(expected),
        "found_declarations": len(cones),
        "missing": missing,
        "bad_cones": bad,
        "cones": cones,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
    }
    # audit-list integrity: the declarations queried in AxiomAudit.lean must be exactly the
    # expected fully-qualified set (no silent additions or omissions)
    audit_src = open(os.path.join(ROOT, "release/Poincare/L4/GeodesicComparison/AxiomAudit.lean")).read()
    queried = re.findall(r"^#print axioms (\S+)\s*$", audit_src, re.M)
    expected_fq = sorted(["Poincare.L4.GeodesicComparison." + d for d in AUDIT_DECLS]
                         + ["Poincare.D12.ComparisonGeodesics." + d for d in AUDIT_ENGINE]
                         + ["Poincare.D10." + d for d in AUDIT_MODEL])
    result["audit_query_integrity"] = {
        "queried": len(queried), "expected": len(expected_fq),
        "exact_match": sorted(queried) == expected_fq,
        "unexpected": sorted(set(queried) - set(expected_fq)),
        "not_queried": sorted(set(expected_fq) - set(queried)),
    }
    result["gates"]["audit_query_list_exact"] = sorted(queried) == expected_fq
    if sorted(queried) != expected_fq:
        failures.append("audit query list mismatch: %s" % result["audit_query_integrity"])

    # negative control: a synthetic audit log carrying a sorryAx cone must be parsed by the
    # same parser and rejected by the same acceptance predicate used for the real audit
    control_log = os.path.join(LOGS, "c4-negative-control-synthetic.log")
    with open(control_log, "w") as fh:
        fh.write("info: Fake.lean:1:0: 'Fake.sorryThm' depends on axioms: [sorryAx]\n")
        fh.write("'Fake.classicalThm' depends on axioms: [propext,\n Classical.choice,\n"
                 " Quot.sound]\n")
    control_cones = parse_axioms(control_log)
    control_bad = {d: c for d, c in control_cones.items() if not set(c) <= ALLOWED_AXIOMS}
    control_rejected = ("Fake.sorryThm" in control_cones
                        and control_cones.get("Fake.sorryThm") == ["sorryAx"]
                        and bool(control_bad))
    result["negative_control"] = {
        "synthetic_log": "logs/c4-negative-control-synthetic.log",
        "synthetic_cones": control_cones,
        "detected_tainted": "Fake.sorryThm" in control_bad,
        "rejected": control_rejected,
    }
    result["gates"]["axiom_audit_all_expected_found"] = not missing
    result["gates"]["axiom_cones_allowed"] = not bad
    result["gates"]["negative_control_rejects_sorryAx"] = control_rejected
    if missing:
        failures.append("axiom audit missing: %s" % missing)
    if bad:
        failures.append("bad axiom cones: %s" % bad)

    result["ok"] = not failures and all(result["gates"].values())
    result["failures"] = failures
    with open(os.path.join(MANIFEST, "c4-verification.json"), "w") as fh:
        json.dump(result, fh, indent=1, sort_keys=True)
    print(json.dumps({"ok": result["ok"], "gates": result["gates"],
                      "axiom_audit": {k: v for k, v in result["axiom_audit"].items()
                                      if k != "cones"},
                      "failures": failures}, indent=1))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
