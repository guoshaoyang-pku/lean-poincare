#!/usr/bin/env python3
"""L4-child-conjugate-point-bound fail-closed verification.

Run from the worktree root:

    python3 tools/l4cp_verify.py

Gates (all fail-closed; a non-zero exit means at least one gate failed):

  1. provenance  - every imported (non-authored) source is byte-identical to its recorded
                   canonical origin (L1-lean-baseline for D10/D12, the L4 leader worktree
                   for the three GeodesicComparison files) and to its recorded sha256;
  2. forbidden   - no `sorry`, `axiom` declaration, `admit`, `unsafe`, `native_decide` or
                   `proof_wanted` in the authored sources (comments stripped);
  3. compile     - `lake build` of the endpoint module + audit module exits 0;
  4. audit run   - `lake env lean` of the audit module exits 0;
  5. audit list  - the `#print axioms` queries in the audit module are exactly the expected
                   fully-qualified set;
  6. coverage    - every declaration scanned in the endpoint module is on the audit list;
  7. forms       - no declaration form the scanner does not understand (instance, structure,
                   class, opaque, example, mutual) is present in the endpoint module;
  8. audit found - every expected declaration appears in the audit output;
  9. cones       - every axiom cone is a subset of {propext, Classical.choice, Quot.sound};
 10. negcontrol  - a *real* tainted file (`negcontrol/EndpointNegativeControl.lean`) is
                   compiled and both its `sorryAx` and declared-axiom cones are rejected;
 11. negcontrol2 - the same parser/acceptance predicate rejects a synthetic tainted log.

Writes `manifest/l4cp-verification.json` and the raw logs under `logs/`.
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
LEADER = ("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/"
          "leaders/L4-geometric-critical-path/release")

AUTHORED = [
    "release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean",
    "release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean",
]

# imported sources: (path, canonical origin, sha256 recorded at bootstrap)
IMPORTED = [
    ("release/Poincare/D10/JacobiConstantCurvature/Basic.lean",
     f"{L1}/Poincare/D10/JacobiConstantCurvature/Basic.lean",
     "af126a030be3d08fb553b51faff8ff0840713b5bd9f44344b781e233c86cda40"),
    ("release/Poincare/D10/JacobiConstantCurvature/ODE.lean",
     f"{L1}/Poincare/D10/JacobiConstantCurvature/ODE.lean",
     "e83ec3c5922d865569b000209e593a284f70bd57127cd226a202abd0df9b2a28"),
    ("release/Poincare/D10/JacobiConstantCurvature/Comparison.lean",
     f"{L1}/Poincare/D10/JacobiConstantCurvature/Comparison.lean",
     "d187e56c2a359aa18c0cd3bf04837e87f48819e9593acf35bd6d273be97b9992"),
    ("release/Poincare/D12/ComparisonGeodesics/Definitions.lean",
     f"{L1}/Poincare/D12/ComparisonGeodesics/Definitions.lean",
     "62b9637d467cb483890e7e95685ac0beb1e29571892a09d7682d41f06de00dd5"),
    ("release/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean",
     f"{L1}/Poincare/D12/ComparisonGeodesics/SingularRiccati.lean",
     "446605cd23dca7ab1bb29cd036e0c78cd612dc565c5b8d44a0788062e47ef9a8"),
    ("release/Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean",
     f"{L1}/Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean",
     "e749d396e903166d9a7943e169a93bd2ffbf232fed02ff4a1ffdf5e09f2d7e4a"),
    ("release/Poincare/D12/ComparisonGeodesics/VolumeRatio.lean",
     f"{L1}/Poincare/D12/ComparisonGeodesics/VolumeRatio.lean",
     "2855a05b42335dbae566860c7198d47d08853e580dbd06dfe55179c05f2b66dc"),
    ("release/Poincare/D12/ComparisonGeodesics/SturmComparison.lean",
     f"{L1}/Poincare/D12/ComparisonGeodesics/SturmComparison.lean",
     "1c7cb4ce8be44765dbc2f2db9c8ebfaeea84357efc50e16448e195f660e7cd03"),
    ("release/Poincare/L4/GeodesicComparison/RauchBridge.lean",
     f"{LEADER}/Poincare/L4/GeodesicComparison/RauchBridge.lean",
     "dddc988dc10d7bf0b218a5c888f208e9ecd279c94d66461a98770d38d9bed0bb"),
    ("release/Poincare/L4/GeodesicComparison/DownstreamComparison.lean",
     f"{LEADER}/Poincare/L4/GeodesicComparison/DownstreamComparison.lean",
     "93a653e28623f62b5c796786ebe81b7f8028b468e1454f0cbb5d6d1041cef3b3"),
    ("release/Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean",
     f"{LEADER}/Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean",
     "93cb411e25f19079d39c36202bdf61a23e3b23a5939694fb668583d6c6e96048"),
]

FORBIDDEN = [
    (r"\bsorry\b", "sorry"),
    (r"(?m)^\s*(private\s+|protected\s+|noncomputable\s+)*axiom\b", "axiom declaration"),
    (r"\badmit\b", "admit"),
    (r"\bunsafe\b", "unsafe"),
    (r"\bnative_decide\b", "native_decide"),
    (r"\bproof_wanted\b", "proof_wanted"),
]

# fully-qualified audit targets, grouped by provenance class
AUDIT_L4_AUTHORED = [
    "JacobiSolutionOn.mono", "basePoint_lt_firstZero", "conjugate_point_bound_strict",
    "conjugate_point_bound", "endpoint_bound_acceptance_lock",
    "jacobiSolTwo_second_deriv_bound_four", "jacobiSolTwo_pos_Ioc_two",
    "conjugate_point_bound_witness_k2_K1", "conjugate_point_bound_witness_k2_K2",
    "pi_div_sqrt_two_lt_pi", "jacobiSol_pos_iff", "jacobiSol_two_pos_iff",
    "jacobiSol_two_firstZero", "jacobiSol_two_not_pos_at_firstZero",
]
AUDIT_L4_CONSUMED = [
    "jacobi_le_constCurvModel", "rauch_upper_of_jacobi_constCurv",
    "jacobiSol_jacobiSolutionOn", "jacobiSol_pos_of_nonneg",
    "jacobiSol_second_deriv_bound", "euclideanNormalizedOn_of_jacobi",
]
AUDIT_D12_ENGINE = ["riccati_le_of_singular_normalization"]
AUDIT_D10_MODEL = [
    "jacobiSolSphere_firstZero", "jacobiSol_of_pos", "jacobiSol_zero",
    "jacobiDeriv_zero", "jacobiSolSphere_pos", "continuous_jacobiSol",
]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

EXPECTED_FQ = (
    ["Poincare.L4.GeodesicComparison." + d for d in AUDIT_L4_AUTHORED]
    + ["Poincare.L4.GeodesicComparison." + d for d in AUDIT_L4_CONSUMED]
    + ["Poincare.D12.ComparisonGeodesics." + d for d in AUDIT_D12_ENGINE]
    + ["Poincare.D10." + d for d in AUDIT_D10_MODEL]
)

HEADLINE_STATEMENTS = [
    "conjugate_point_bound : k >= K > 0 on (0,T), u 0 = 0, u' 0 = 1, u > 0 on (0,T], "
    "analytic normalization hypotheses of rauch_upper_of_jacobi_constCurv  ==>  "
    "T <= pi / sqrt K",
    "conjugate_point_bound_strict : same hypotheses  ==>  T < pi / sqrt K",
    "conjugate_point_bound_witness_k2_K1 : 2 <= pi / sqrt 1  (witness k = 2, K = 1)",
    "conjugate_point_bound_witness_k2_K2 : 2 <= pi / sqrt 2  (sharpened witness k = 2, K = 2)",
    "jacobiSol_two_pos_iff : (forall t in (0,T], 0 < jacobiSol 2 t) <-> T < pi / sqrt 2",
    "jacobiSol_pos_iff : K > 0  ==>  (forall t in (0,T], 0 < jacobiSol K t) <-> "
    "T < pi / sqrt K",
]


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
    """Remove nested block comments and line comments (replaced by spaces)."""
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
    r"^(?:info: )?.*?'([^']+)' (?:depends on axioms: \[(.*?)\]|does not depend on any axioms)",
    re.M | re.S)


def parse_axioms(log_path):
    text = open(log_path).read()
    # merge wrapped lines: axiom-list entries continue with leading whitespace/commas
    text = re.sub(r"\n\s+", " ", text)
    found = {}
    for m in AXIOM_LINE.finditer(text):
        name = m.group(1)
        raw = m.group(2) or ""
        cone = [a.strip() for a in raw.split(",") if a.strip()]
        found[name] = cone
    return found


def main():
    stamp = datetime.now(timezone.utc).isoformat()
    result = {"task_id": "L4-child-conjugate-point-bound", "generated_at": stamp,
              "gates": {}, "hashes": {}, "axiom_audit": {}, "ok": False,
              "headline_statements": HEADLINE_STATEMENTS,
              "toolchain": open(os.path.join(RELEASE, "lean-toolchain")).read().strip(),
              "semantic_class": ("conditional analytic scalar Jacobi/Riccati comparison; "
                                 "manifold-level conjugate-point theorem not claimed")}
    failures = []

    # ---- gate 1: hashes + provenance ------------------------------------------------
    for rel in AUTHORED:
        result["hashes"][rel] = sha256(os.path.join(ROOT, rel))
    for rel in ["release/lakefile.toml", "release/lean-toolchain", "release/lake-manifest.json"]:
        result["hashes"][rel] = sha256(os.path.join(ROOT, rel))
    prov = {}
    for rel, origin, expected in IMPORTED:
        actual = sha256(os.path.join(ROOT, rel))
        result["hashes"][rel] = actual
        origin_actual = sha256(origin) if os.path.exists(origin) else None
        ok = (actual == expected == origin_actual)
        prov[rel] = {"origin": origin, "recorded_sha256": expected,
                     "origin_sha256": origin_actual, "unchanged": ok}
        if not ok:
            failures.append("provenance mismatch: " + rel)
    result["provenance"] = prov
    result["gates"]["provenance_unchanged"] = all(v["unchanged"] for v in prov.values())

    # ---- gate 2: forbidden tokens ---------------------------------------------------
    hits = []
    scan = {}
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
    modules = ["Poincare.L4.GeodesicComparison.ConjugatePointEndpoint",
               "Poincare.L4.GeodesicComparison.ConjugatePointAxiomAudit"]
    cc = run(["lake", "build"] + modules, cwd=RELEASE,
             log=os.path.join(LOGS, "l4cp-verify-build.log"))
    result["compile"] = {"cmd": "lake build " + " ".join(modules), "cwd": "release/",
                         "exit": cc, "log": "logs/l4cp-verify-build.log"}
    result["gates"]["compile_exit_zero"] = cc == 0
    if cc != 0:
        failures.append("compile exit %d" % cc)

    # ---- gate 4 + 5: axiom run and query-list integrity ------------------------------
    aa = run(["lake", "env", "lean",
              "Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean"],
             cwd=RELEASE, log=os.path.join(LOGS, "l4cp-verify-axioms.log"))
    result["axiom_run"] = {"cmd": ("lake env lean "
                                   "Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean"),
                           "cwd": "release/", "exit": aa,
                           "log": "logs/l4cp-verify-axioms.log"}
    result["gates"]["axiom_run_exit_zero"] = aa == 0
    if aa != 0:
        failures.append("axiom audit run exit %d" % aa)

    audit_src = open(os.path.join(
        ROOT, "release/Poincare/L4/GeodesicComparison/ConjugatePointAxiomAudit.lean")).read()
    queried = re.findall(r"^#print axioms (\S+)\s*$", audit_src, re.M)
    result["audit_query_integrity"] = {
        "queried": len(queried), "expected": len(EXPECTED_FQ),
        "exact_match": sorted(queried) == sorted(EXPECTED_FQ),
        "unexpected": sorted(set(queried) - set(EXPECTED_FQ)),
        "not_queried": sorted(set(EXPECTED_FQ) - set(queried)),
    }
    result["gates"]["audit_query_list_exact"] = sorted(queried) == sorted(EXPECTED_FQ)
    if not result["gates"]["audit_query_list_exact"]:
        failures.append("audit query list mismatch")

    # every declaration authored in the endpoint module must be on the audit list, so a
    # future silent addition cannot escape the axiom audit
    decl_re = re.compile(
        r"^(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][\w.']*)", re.M)
    endpoint_src = strip_comments(open(os.path.join(
        ROOT, "release/Poincare/L4/GeodesicComparison/ConjugatePointEndpoint.lean")).read())
    authored_scan = sorted(set(decl_re.findall(endpoint_src)))
    expected_scan = sorted(d for d in AUDIT_L4_AUTHORED
                           if d != "endpoint_bound_acceptance_lock")
    result["authored_declaration_scan"] = {
        "scanned": authored_scan, "expected": expected_scan,
        "exact_match": authored_scan == expected_scan,
        "not_audited": sorted(set(authored_scan) - set(expected_scan)),
        "audited_but_absent": sorted(set(expected_scan) - set(authored_scan)),
    }
    result["gates"]["authored_declarations_all_audited"] = authored_scan == expected_scan
    if authored_scan != expected_scan:
        failures.append("authored declaration scan mismatch: %s"
                        % result["authored_declaration_scan"])

    # declaration forms the inventory scanner does not understand must not appear in the
    # endpoint module: if one is introduced, this gate fails and forces a tooling update
    # instead of letting the declaration escape the axiom audit
    unknown_form_re = re.compile(
        r"^(?:private\s+|protected\s+|noncomputable\s+)*"
        r"(?:instance|structure|class|opaque|example|mutual)\b", re.M)
    unknown_forms = unknown_form_re.findall(endpoint_src)
    result["unknown_declaration_forms"] = unknown_forms
    result["gates"]["no_unscanned_declaration_forms"] = not unknown_forms
    if unknown_forms:
        failures.append("unscanned declaration forms present: %s" % unknown_forms)

    # ---- gate 6 + 7: expected declarations, allowed cones ----------------------------
    cones = parse_axioms(os.path.join(LOGS, "l4cp-verify-axioms.log"))
    missing = [d for d in EXPECTED_FQ if d not in cones]
    bad = {d: c for d, c in cones.items() if not set(c) <= ALLOWED_AXIOMS}
    result["axiom_audit"] = {
        "expected_declarations": len(EXPECTED_FQ),
        "found_declarations": len(cones),
        "missing": missing,
        "bad_cones": bad,
        "cones": cones,
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
    }
    result["gates"]["axiom_audit_all_expected_found"] = not missing
    result["gates"]["axiom_cones_allowed"] = not bad
    if missing:
        failures.append("axiom audit missing: %s" % missing)
    if bad:
        failures.append("bad axiom cones: %s" % bad)

    # ---- gate 8: real negative control ----------------------------------------------
    nc = run(["lake", "env", "lean", "../negcontrol/EndpointNegativeControl.lean"],
             cwd=RELEASE, log=os.path.join(LOGS, "l4cp-negative-control.log"))
    nc_cones = parse_axioms(os.path.join(LOGS, "l4cp-negative-control.log"))
    nc_bad = {d: c for d, c in nc_cones.items() if not set(c) <= ALLOWED_AXIOMS}
    nc_rejected = ("negControl_sorry" in nc_cones
                   and nc_cones.get("negControl_sorry") == ["sorryAx"]
                   and "negControl_axiom" in nc_cones
                   and nc_cones.get("negControl_axiom") == ["negControl_axiom"]
                   and set(nc_bad) == {"negControl_sorry", "negControl_axiom"})
    result["negative_control_real"] = {
        "cmd": "lake env lean ../negcontrol/EndpointNegativeControl.lean",
        "exit": nc, "cones": nc_cones, "rejected": nc_rejected,
        "log": "logs/l4cp-negative-control.log",
    }
    result["gates"]["negative_control_real_rejected"] = nc_rejected
    if not nc_rejected:
        failures.append("real negative control not rejected: %s" % nc_cones)

    # ---- gate 9: synthetic negative control (parser/acceptance predicate) ------------
    control_log = os.path.join(LOGS, "l4cp-negative-control-synthetic.log")
    with open(control_log, "w") as fh:
        fh.write("info: Fake.lean:1:0: 'Fake.sorryThm' depends on axioms: [sorryAx]\n")
        fh.write("'Fake.classicalThm' depends on axioms: [propext,\n Classical.choice,\n"
                 " Quot.sound]\n")
        fh.write("'Fake.cleanThm' does not depend on any axioms\n")
    control_cones = parse_axioms(control_log)
    control_bad = {d: c for d, c in control_cones.items() if not set(c) <= ALLOWED_AXIOMS}
    control_rejected = (control_cones.get("Fake.sorryThm") == ["sorryAx"]
                        and control_cones.get("Fake.classicalThm")
                        == ["propext", "Classical.choice", "Quot.sound"]
                        and control_cones.get("Fake.cleanThm") == []
                        and bool(control_bad))
    result["negative_control_synthetic"] = {
        "synthetic_log": "logs/l4cp-negative-control-synthetic.log",
        "synthetic_cones": control_cones, "rejected": control_rejected,
    }
    result["gates"]["negative_control_synthetic_rejected"] = control_rejected
    if not control_rejected:
        failures.append("synthetic negative control not rejected")

    result["ok"] = not failures and all(result["gates"].values())
    result["failures"] = failures
    with open(os.path.join(MANIFEST, "l4cp-verification.json"), "w") as fh:
        json.dump(result, fh, indent=1, sort_keys=True)
    print(json.dumps({"ok": result["ok"], "gates": result["gates"],
                      "hashes": result["hashes"],
                      "axiom_audit": {k: v for k, v in result["axiom_audit"].items()
                                      if k != "cones"},
                      "failures": failures}, indent=1))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    sys.exit(main())
