#!/usr/bin/env python3
"""
L4-child-sturm-zero-interlacing: release gate driver.

Runs, records and fail-closes on:

  1. lake build of the two deliverable modules + the axiom-audit driver
  2. per-file elaboration of every deliverable module
  3. the mathematical negative control and the soundness negative control
  4. the comment/string-aware forbidden-token scan of `release/`
  5. the per-declaration kernel axiom audit (cone subset of
     {propext, Classical.choice, Quot.sound}; every declaration must be reported)
  6. byte-identity of the read-only inputs against the leader release
  7. sha256 source manifest of the deliverable sources
  8. toolchain / mathlib pin record

Outputs: evidence/gates.json, evidence/axiom-report.json,
evidence/source-hashes.json, evidence/input-hash-verification.json,
evidence/verification.json.  Exit code 0 iff every gate passes.
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RELEASE = os.path.join(ROOT, "release")
LOGS = os.path.join(ROOT, "logs")
EVIDENCE = os.path.join(ROOT, "evidence")
LEADER = os.path.join(os.path.dirname(ROOT), "leaders", "L4-geometric-critical-path", "release")
ELAN = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=f"{ELAN}/bin:" + os.environ["PATH"])

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

DELIVERABLE_MODULES = [
    "Poincare/L4/GeodesicComparison/SturmInterlacing.lean",
    "Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean",
    "Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean",
]
AUDIT_MODULE = "Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean"

# read-only inputs copied byte-identically from the leader release
INPUT_FILES = [
    "Poincare/D10/JacobiConstantCurvature/Basic.lean",
    "Poincare/D10/JacobiConstantCurvature/ODE.lean",
    "Poincare/D10/JacobiConstantCurvature/Comparison.lean",
    "Poincare/D12/ComparisonGeodesics/Definitions.lean",
    "Poincare/D12/ComparisonGeodesics/SturmComparison.lean",
    "Poincare/D12/ComparisonGeodesics/SingularRiccati.lean",
    "Poincare/D12/ComparisonGeodesics/VolumeRatio.lean",
    "Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean",
    "Poincare/L4/GeodesicComparison/RauchBridge.lean",
    "Poincare/L4/GeodesicComparison/DownstreamComparison.lean",
    "Poincare/L4/GeodesicComparison/ConstantCurvatureRauch.lean",
    "Poincare/L4/GeodesicComparison/ConjugatePointBound.lean",
    "Poincare/L4/GeodesicComparison/SturmZeroCount.lean",
]

os.makedirs(LOGS, exist_ok=True)
os.makedirs(EVIDENCE, exist_ok=True)


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def run(step_id, cmd, cwd, log_name, gate=True, timeout=3600, shell=False):
    log_path = os.path.join(LOGS, log_name)
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {cmd if shell else ' '.join(cmd)}\n# cwd: {cwd}\n\n")
        log.flush()
        try:
            p = subprocess.run(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                               env=ENV, timeout=timeout, shell=shell)
            code, timed_out = p.returncode, False
        except subprocess.TimeoutExpired:
            code, timed_out = 124, True
    out = open(log_path).read()
    rec = {
        "step": step_id,
        "command": cmd if shell else " ".join(cmd),
        "cwd": cwd,
        "exit_code": code,
        "seconds": round(time.time() - t0, 2),
        "timed_out": timed_out,
        "gate": gate,
        "log": os.path.relpath(log_path, ROOT),
        "passed": (code == 0) if gate else True,
    }
    print(f"[{'OK ' if rec['passed'] else 'FAIL'}] {step_id} exit={code} "
          f"({rec['seconds']}s) -> {rec['log']}")
    return rec, out


def parse_axiom_output(text):
    """Parse `#print axioms` output, tolerating wrapped lines."""
    flat = re.sub(r"\s+", " ", text)
    results = {}
    pattern = re.compile(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
    for m in pattern.finditer(flat):
        name = m.group(1)
        cone = [a.strip() for a in m.group(2).split(",")] if m.group(2) else []
        results[name] = cone
    return results


def main():
    started = datetime.now(timezone.utc).isoformat()
    steps = []
    failures = []

    # ---- 0. pins -------------------------------------------------------
    toolchain = open(os.path.join(RELEASE, "lean-toolchain")).read().strip()
    manifest = json.load(open(os.path.join(RELEASE, "lake-manifest.json")))
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    pins = {
        "toolchain": toolchain,
        "mathlib_rev": mathlib["rev"],
        "mathlib_url": mathlib["url"],
    }

    # ---- 1. clean rebuild of the deliverable modules --------------------
    removed = []
    for stem in ["SturmInterlacing", "SturmInterlacingConjugateCrossCheck",
                 "SturmInterlacingAxiomAudit"]:
        for ext in [".olean", ".ilean", ".trace", ".olean.hash", ".ilean.hash"]:
            p = os.path.join(RELEASE, ".lake", "build", "lib", "lean", "Poincare", "L4",
                             "GeodesicComparison", stem + ext)
            if os.path.exists(p):
                os.remove(p)
                removed.append(os.path.relpath(p, ROOT))
    rec, _ = run("clean_deliverable_rebuild",
                 ["lake", "build",
                  "Poincare.L4.GeodesicComparison.SturmInterlacing",
                  "Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck",
                  "Poincare.L4.GeodesicComparison.SturmInterlacingAxiomAudit"],
                 RELEASE, "09_clean_rebuild.log")
    rec["removed_artifacts"] = removed
    steps.append(rec)
    if not rec["passed"]:
        failures.append("clean_deliverable_rebuild")

    # ---- 1b. lake build -------------------------------------------------
    rec, _ = run("lake_build",
                 ["lake", "build",
                  "Poincare.L4.GeodesicComparison.SturmInterlacing",
                  "Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck",
                  "Poincare.L4.GeodesicComparison.SturmInterlacingAxiomAudit"],
                 RELEASE, "10_lake_build.log")
    steps.append(rec)
    if not rec["passed"]:
        failures.append("lake_build")

    # ---- 2. per-file elaboration ---------------------------------------
    for i, rel in enumerate(DELIVERABLE_MODULES, start=1):
        rec, _ = run(f"per_file_{os.path.basename(rel)}",
                     ["lake", "env", "lean", rel],
                     RELEASE, f"1{i}_per_file_{os.path.basename(rel)}.log")
        steps.append(rec)
        if not rec["passed"]:
            failures.append(rec["step"])

    # ---- 3. negative controls ------------------------------------------
    rec, _ = run("negative_control_math",
                 ["lake", "env", "lean", "../negcontrol/SturmInterlacingNegativeControl.lean"],
                 RELEASE, "20_negcontrol_math.log")
    steps.append(rec)
    if not rec["passed"]:
        failures.append("negative_control_math")

    rec, _ = run("negative_control_soundness",
                 ["lake", "env", "lean", "../negcontrol/NegativeControl.lean"],
                 RELEASE, "21_negcontrol_soundness.log")
    steps.append(rec)
    if not rec["passed"]:
        failures.append("negative_control_soundness")

    # ---- 4. forbidden-token scan ---------------------------------------
    rec, out = run("forbidden_token_scan",
                   ["python3", os.path.join("input", "d5-tools", "scan_forbidden.py"), "release"],
                   ROOT, "22_forbidden_scan.log")
    steps.append(rec)
    scan_json = None
    try:
        scan_json = json.loads(out[out.index("{"):])
    except Exception:
        pass
    if not rec["passed"] or scan_json is None or scan_json.get("hard_match_count", 1) != 0:
        failures.append("forbidden_token_scan")
    if scan_json is not None:
        with open(os.path.join(EVIDENCE, "forbidden-scan.json"), "w") as f:
            json.dump(scan_json, f, indent=1)

    # ---- 5. fail-closed axiom audit ------------------------------------
    audit_src = open(os.path.join(RELEASE, AUDIT_MODULE)).read()
    expected = re.findall(r"#print axioms (\S+)", audit_src)
    rec, out = run("axiom_audit",
                   ["lake", "env", "lean", AUDIT_MODULE],
                   RELEASE, "23_axiom_audit.log")
    steps.append(rec)
    parsed = parse_axiom_output(out)
    violations = []
    missing = [d for d in expected if d not in parsed]
    for decl, cone in parsed.items():
        bad = [a for a in cone if a not in ALLOWED_AXIOMS]
        if bad:
            violations.append({"declaration": decl, "cone": cone, "disallowed": bad})
    audit_ok = rec["passed"] and not missing and not violations and len(parsed) == len(expected)
    if not audit_ok:
        failures.append("axiom_audit")
    axiom_report = {
        "schema": "l4-child-sturm-zero-interlacing/axiom-report-v1",
        "generated": started,
        "module": AUDIT_MODULE,
        "allowed_cone": sorted(ALLOWED_AXIOMS),
        "expected_declarations": len(expected),
        "reported_declarations": len(parsed),
        "missing": missing,
        "violations": violations,
        "forbidden_tokens": ["sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler"],
        "verdict": "PASS" if audit_ok else "FAIL",
        "declarations": {d: parsed[d] for d in expected if d in parsed},
    }
    with open(os.path.join(EVIDENCE, "axiom-report.json"), "w") as f:
        json.dump(axiom_report, f, indent=1, sort_keys=True)

    # ---- 6. input byte-identity ----------------------------------------
    input_records = []
    input_ok = True
    for rel in INPUT_FILES:
        local = os.path.join(RELEASE, rel)
        leader = os.path.join(LEADER, rel)
        lh, rh = sha256(local), sha256(leader)
        same = lh == rh
        input_ok &= same
        input_records.append({"file": rel, "sha256": lh, "leader_sha256": rh,
                              "byte_identical": same})
    if not input_ok:
        failures.append("input_hash_verification")
    with open(os.path.join(EVIDENCE, "input-hash-verification.json"), "w") as f:
        json.dump({"schema": "l4-child-sturm-zero-interlacing/input-hashes-v1",
                   "leader_release": LEADER, "files": input_records,
                   "verdict": "PASS" if input_ok else "FAIL"}, f, indent=1)
    steps.append({"step": "input_hash_verification",
                  "command": f"sha256 byte-identity check of {len(INPUT_FILES)} copied inputs "
                             "vs leader release",
                  "cwd": LEADER, "exit_code": 0 if input_ok else 1, "seconds": 0.0,
                  "timed_out": False, "gate": True, "passed": input_ok,
                  "log": "evidence/input-hash-verification.json"})

    # ---- 7. source manifest --------------------------------------------
    sources = {}
    for dirpath, dirnames, filenames in os.walk(RELEASE):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                sources[os.path.relpath(p, ROOT)] = sha256(p)
    sources[os.path.relpath(os.path.join(ROOT, "negcontrol",
                                         "SturmInterlacingNegativeControl.lean"), ROOT)] = \
        sha256(os.path.join(ROOT, "negcontrol", "SturmInterlacingNegativeControl.lean"))
    with open(os.path.join(EVIDENCE, "source-hashes.json"), "w") as f:
        json.dump({"schema": "l4-child-sturm-zero-interlacing/source-hashes-v1",
                   "root": ROOT, "files": dict(sorted(sources.items()))}, f, indent=1)
    deliverable_hashes = {os.path.join("release", m): sources[os.path.join("release", m)]
                          for m in DELIVERABLE_MODULES}

    # ---- 8. verdict -----------------------------------------------------
    verification = {
        "schema": "l4-child-sturm-zero-interlacing/verification-v1",
        "task_id": "L4-child-sturm-zero-interlacing",
        "generated": started,
        "pins": pins,
        "steps": steps,
        "failures": failures,
        "verdict": "PASS" if not failures else "FAIL",
        "deliverable_source_hashes": deliverable_hashes,
        "axiom_audit_verdict": axiom_report["verdict"],
        "forbidden_scan": scan_json,
    }
    with open(os.path.join(EVIDENCE, "verification.json"), "w") as f:
        json.dump(verification, f, indent=1, sort_keys=True)
    with open(os.path.join(EVIDENCE, "gates.json"), "w") as f:
        json.dump({"generated": started, "pins": pins, "steps": steps,
                   "failures": failures, "verdict": verification["verdict"]},
                  f, indent=1)

    print(json.dumps({"verdict": verification["verdict"], "failures": failures,
                      "axiom_audit": axiom_report["verdict"],
                      "declarations_audited": len(parsed)}, indent=1))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
