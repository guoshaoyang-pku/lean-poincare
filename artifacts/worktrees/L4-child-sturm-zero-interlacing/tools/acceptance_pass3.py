#!/usr/bin/env python3
"""
L4-child-sturm-zero-interlacing: independent acceptance pass 3.

This driver is deliberately *not* a re-run of the deliverable's own gate driver.  It

  1. re-checks the deliverable source hashes against the checkpoint record;
  2. re-checks the 13 read-only inputs byte-for-byte against the current leader release;
  3. scans for declaration-name collisions between the deliverable's own modules and the
     current leader release (integration hygiene);
  4. temporarily stages the leader's *newest* complementary Sturm files
     (`TwoSidedSturm.lean`, `SturmUniqueness.lean`) in the release tree, compiles them
     there (integration compatibility against the byte-identical `SturmZeroCount.lean`),
     and compiles `tmp/acceptance_probe_r3_audit.lean`: a probe that exercises the
     delivered theorems on hand-rolled data (`sin(4t)/4`, `sin(2t)/2`) never used by the
     deliverable, including a two-sided first-zero bracket obtained by combining the
     deliverable's one-sided zero counting with the leader's complementary
     `no_first_zero_before_pi_sqrt_of_curvature_le`;
  5. audits every probe declaration fail-closed (cone subset of
     {propext, Classical.choice, Quot.sound}, every expected declaration reported);
  6. removes the staged files and verifies that every `release/*.lean` file is back to the
     byte-exact state recorded by the deliverable's gate run;
  7. performs a full project-closure rebuild (all project oleans deleted, then
     `lake build` of the three deliverable modules from source) and re-runs the
     per-declaration deliverable axiom audit on the freshly rebuilt oleans.

Writes evidence/acceptance-pass3.json.  Exit code 0 iff every check passes.
"""
import hashlib
import json
import os
import re
import shutil
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
# leader files staged temporarily for the integration cross-check (read-only inputs)
STAGED = [
    "Poincare/L4/GeodesicComparison/TwoSidedSturm.lean",
    "Poincare/L4/GeodesicComparison/SturmUniqueness.lean",
]
PROBE = "tmp/acceptance_probe_r3.lean"
PROBE_AUDIT = "tmp/acceptance_probe_r3_audit.lean"
PROBE_NAMES = "tmp/acceptance_probe_r3_names.txt"
BUILD_ROOT = os.path.join(RELEASE, ".lake", "build", "lib", "lean", "Poincare")

os.makedirs(LOGS, exist_ok=True)
os.makedirs(EVIDENCE, exist_ok=True)

checks = []


def check(name, ok, detail=""):
    checks.append({"check": name, "ok": bool(ok), "detail": str(detail)})
    print(f"[{'OK ' if ok else 'FAIL'}] {name} {detail}")
    return ok


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def run(step_id, cmd, cwd, log_name, timeout=3600):
    log_path = os.path.join(LOGS, log_name)
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {' '.join(cmd)}\n# cwd: {cwd}\n\n")
        log.flush()
        try:
            p = subprocess.run(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                               env=ENV, timeout=timeout)
            code, timed_out = p.returncode, False
        except subprocess.TimeoutExpired:
            code, timed_out = 124, True
    out = open(log_path).read()
    rec = {"step": step_id, "command": " ".join(cmd), "cwd": cwd, "exit_code": code,
           "seconds": round(time.time() - t0, 2), "timed_out": timed_out,
           "log": os.path.relpath(log_path, ROOT)}
    print(f"[{'OK ' if code == 0 else 'FAIL'}] {step_id} exit={code} ({rec['seconds']}s)")
    return rec, out


def parse_axiom_output(text):
    flat = re.sub(r"\s+", " ", text)
    results = {}
    pattern = re.compile(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
    for m in pattern.finditer(flat):
        name = m.group(1)
        cone = [a.strip() for a in m.group(2).split(",")] if m.group(2) else []
        results[name] = cone
    return results


def decl_names_in(path):
    """Names declared by a Lean file (theorem/lemma/def/abbrev), unqualified."""
    src = open(path).read()
    return set(re.findall(
        r"^(?:noncomputable\s+)?(?:private\s+)?(?:protected\s+)?"
        r"(?:theorem|lemma|def|abbrev)\s+([A-Za-z_][\w'.]*)", src, re.M))


def lean_files_under(d):
    out = []
    for dirpath, dirnames, filenames in os.walk(d):
        dirnames[:] = [x for x in dirnames if x != ".lake"]
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                out.append(os.path.join(dirpath, fn))
    return out


def main():
    started = datetime.now(timezone.utc).isoformat()
    cp = json.load(open(os.path.join(ROOT, "checkpoint.json")))
    latest = cp["checkpoints"][-1]
    sh = json.load(open(os.path.join(EVIDENCE, "source-hashes.json")))

    # ---- 0. deliverable hashes against the checkpoint record ------------
    bad = []
    deliverable_hashes = {}
    for rel in DELIVERABLE_MODULES:
        p = os.path.join(RELEASE, rel)
        h = sha256(p)
        deliverable_hashes[os.path.join("release", rel)] = h
        rec = latest["deliverable_hashes"].get(os.path.join("release", rel))
        if rec is not None and rec != h:
            bad.append(rel)
    check("deliverable_hashes_match_checkpoint", not bad, f"{latest['id']} mismatches={bad}")

    # ---- 1. read-only input byte-identity (current leader release) ------
    inp = []
    for rel in INPUT_FILES:
        lh, rh = sha256(os.path.join(RELEASE, rel)), sha256(os.path.join(LEADER, rel))
        inp.append({"file": rel, "sha256": lh, "leader_sha256": rh, "byte_identical": lh == rh})
    check("input_byte_identity_direct_sha256",
          all(r["byte_identical"] for r in inp),
          f"{sum(r['byte_identical'] for r in inp)}/{len(inp)} identical")

    # ---- 2. name-collision scan vs current leader release ---------------
    own = []
    for rel in DELIVERABLE_MODULES:
        own.append(os.path.join(RELEASE, rel))
    own.append(os.path.join(ROOT, "negcontrol", "SturmInterlacingNegativeControl.lean"))
    own_names = set()
    for p in own:
        own_names |= decl_names_in(p)
    leader_names = {}
    for p in lean_files_under(os.path.join(LEADER, "Poincare")):
        for n in decl_names_in(p):
            leader_names.setdefault(n, os.path.relpath(p, LEADER))
    collisions = sorted(n for n in own_names if n in leader_names)
    check("no_declaration_name_collisions_with_leader", not collisions,
          f"own={len(own_names)} leader={len(leader_names)} collisions={collisions}")

    # ---- 2b. shared queue / manifest / input preservation ---------------
    task_start = datetime.fromisoformat(cp["checkpoints"][0]["at"])
    shared_rel = ["longrun/queue.updated.json"]
    for sub in ("manifest", "input"):
        for dp, dn, fn in os.walk(os.path.join(ROOT, sub)):
            for f in fn:
                shared_rel.append(os.path.relpath(os.path.join(dp, f), ROOT))
    preserved, touched = [], []
    for rel in sorted(shared_rel):
        p = os.path.join(ROOT, rel)
        mt = datetime.fromtimestamp(os.path.getmtime(p), timezone.utc)
        preserved.append({"file": rel, "sha256": sha256(p), "mtime": mt.isoformat()})
        if mt >= task_start:
            touched.append(rel)
    check("shared_queue_manifest_input_preserved", not touched,
          f"files={len(preserved)} modified_since_cp1={touched} "
          f"(all mtimes predate {task_start.isoformat()})")

    # ---- 3. stage the leader's newest complementary Sturm files ---------
    staged_hashes = {}
    for rel in STAGED:
        src, dst = os.path.join(LEADER, rel), os.path.join(RELEASE, rel)
        shutil.copyfile(src, dst)
        staged_hashes[rel] = {"sha256": sha256(dst), "leader_sha256": sha256(src)}
    build_rec, build_out = run(
        "stage_leader_complementary_sturm",
        ["lake", "build", "Poincare.L4.GeodesicComparison.TwoSidedSturm",
         "Poincare.L4.GeodesicComparison.SturmUniqueness"],
        RELEASE, "60_stage_leader_sturm.log")
    stage_ok = (build_rec["exit_code"] == 0
                and all(v["sha256"] == v["leader_sha256"] for v in staged_hashes.values()))
    check("leader_complementary_files_compile_here", stage_ok,
          f"exits={build_rec['exit_code']} hashes_identical="
          f"{all(v['sha256'] == v['leader_sha256'] for v in staged_hashes.values())}")

    # ---- 4. probe compile + fail-closed axiom audit ----------------------
    probe_rec, probe_out = run("probe_r3_compile_audit",
                               ["lake", "env", "lean", os.path.join("..", PROBE_AUDIT)],
                               RELEASE, "61_probe_r3_audit.log")
    expected = [l.strip() for l in open(os.path.join(ROOT, PROBE_NAMES)) if l.strip()]
    parsed = parse_axiom_output(probe_out)
    missing = [d for d in expected if d not in parsed]
    out_of_cone = {d: c for d, c in parsed.items() if not set(c) <= ALLOWED_AXIOMS}
    forbidden = [d for d, c in parsed.items()
                 if any(t in a for a in c for t in ("sorryAx", "trustCompiler", "ofReduceBool"))]
    probe_ok = (probe_rec["exit_code"] == 0 and not missing and not out_of_cone
                and not forbidden and len(parsed) == len(expected))
    check("probe_r3_fail_closed_axiom_audit", probe_ok,
          f"declarations={len(parsed)}/{len(expected)} missing={missing} "
          f"out_of_cone={list(out_of_cone)} forbidden={forbidden}")

    # ---- 5. unstage and verify exact restoration of release/*.lean ------
    removed = []
    for rel in STAGED:
        p = os.path.join(RELEASE, rel)
        os.remove(p)
        removed.append(rel)
        stem = os.path.splitext(os.path.basename(rel))[0]
        for ext in [".olean", ".ilean", ".trace", ".olean.hash", ".ilean.hash"]:
            art = os.path.join(RELEASE, ".lake", "build", "lib", "lean",
                               "Poincare", "L4", "GeodesicComparison", stem + ext)
            if os.path.exists(art):
                os.remove(art)
    disk = {}
    for p in lean_files_under(RELEASE):
        disk[os.path.relpath(p, ROOT)] = sha256(p)
    expected_disk = {k: v for k, v in sh["files"].items() if k.startswith("release/")}
    restored = disk == expected_disk
    check("release_tree_restored_to_gate_recorded_state", restored,
          f"files={len(disk)} expected={len(expected_disk)} "
          f"extra={sorted(set(disk) - set(expected_disk))[:3]} "
          f"missing={sorted(set(expected_disk) - set(disk))[:3]} "
          f"differing={[k for k in disk if k in expected_disk and disk[k] != expected_disk[k]][:3]}")

    # ---- 6. full project-closure rebuild --------------------------------
    oleans_deleted = 0
    if os.path.isdir(BUILD_ROOT):
        for dirpath, dirnames, filenames in os.walk(BUILD_ROOT):
            oleans_deleted += sum(1 for fn in filenames if fn.endswith((".olean", ".ilean", ".trace")))
        shutil.rmtree(BUILD_ROOT)
    t0 = time.time()
    clo_rec, clo_out = run(
        "closure_rebuild_deliverables",
        ["lake", "build",
         "Poincare.L4.GeodesicComparison.SturmInterlacing",
         "Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck",
         "Poincare.L4.GeodesicComparison.SturmInterlacingAxiomAudit"],
        RELEASE, "62_closure_rebuild.log")
    m = re.search(r"Built.*?\((\d+) jobs\)", clo_out)
    jobs = int(m.group(1)) if m else -1
    if jobs < 0:
        m2 = re.findall(r"\[(\d+)/(\d+)\]", clo_out)
        jobs = int(m2[-1][1]) if m2 else -1
    check("project_closure_rebuild_exit0", clo_rec["exit_code"] == 0,
          f"exit={clo_rec['exit_code']} jobs={jobs} "
          f"oleans_deleted={oleans_deleted} seconds={clo_rec['seconds']}")

    # ---- 7. re-run the deliverable axiom audit on rebuilt oleans --------
    audit_rec, audit_out = run("deliverable_axiom_audit_after_rebuild",
                               ["lake", "env", "lean", AUDIT_MODULE],
                               RELEASE, "63_axiom_audit_after_rebuild.log")
    audit_src = open(os.path.join(RELEASE, AUDIT_MODULE)).read()
    audit_expected = re.findall(r"#print axioms (\S+)", audit_src)
    audit_parsed = parse_axiom_output(audit_out)
    a_missing = [d for d in audit_expected if d not in audit_parsed]
    a_viol = {d: c for d, c in audit_parsed.items() if not set(c) <= ALLOWED_AXIOMS}
    audit_ok = (audit_rec["exit_code"] == 0 and not a_missing and not a_viol
                and len(audit_parsed) == len(audit_expected))
    check("deliverable_axiom_audit_after_closure_rebuild", audit_ok,
          f"declarations={len(audit_parsed)}/{len(audit_expected)} "
          f"missing={a_missing} violations={list(a_viol)}")

    # ---- 8. evidence -----------------------------------------------------
    probe_theorems = [{"name": d.split(".")[-1], "cone": parsed[d]} for d in expected if d in parsed]
    evidence = {
        "schema": "l4-child-sturm-zero-interlacing/acceptance-pass3-v1",
        "task_id": "L4-child-sturm-zero-interlacing",
        "generated": started,
        "verdict": "PASS" if all(c["ok"] for c in checks) else "FAIL",
        "checks": checks,
        "deliverable_hashes": deliverable_hashes,
        "checkpoint_reference": latest["id"],
        "input_byte_identity": inp,
        "name_collisions": {"own_declarations": len(own_names),
                            "leader_declarations": len(leader_names),
                            "collisions": collisions},
        "preserved_shared_files": preserved,
        "integration": {
            "leader_files_staged": staged_hashes,
            "build": build_rec,
            "combined_theorem": ("p3_two_sided_bracket / p3_bracket_sharp: for the "
                                 "hand-rolled solution p3u = sin(4t)/4 (curvature 16), the "
                                 "deliverable's zero counting (K=9) gives "
                                 "firstPositiveZero p3u <= pi/3 and the leader's "
                                 "no_first_zero_before_pi_sqrt_of_curvature_le (K=25) gives "
                                 "pi/5 <= firstPositiveZero p3u; the exact value is pi/4"),
        },
        "tree_restoration": {"removed": removed, "release_lean_files": len(disk),
                             "matches_gate_recorded_state": restored},
        "closure_rebuild": {
            "command": clo_rec["command"], "exit_code": clo_rec["exit_code"],
            "jobs": jobs, "oleans_deleted": oleans_deleted,
            "seconds": clo_rec["seconds"], "log": clo_rec["log"]},
        "probe": {
            "file": PROBE, "sha256": sha256(os.path.join(ROOT, PROBE)),
            "audit_file": PROBE_AUDIT, "audit_sha256": sha256(os.path.join(ROOT, PROBE_AUDIT)),
            "command": f"lake env lean ../{PROBE_AUDIT}", "compile_exit": probe_rec["exit_code"],
            "log": probe_rec["log"], "declarations_audited": len(parsed),
            "missing": missing, "out_of_cone": list(out_of_cone), "forbidden": forbidden,
            "allowed_cone": sorted(ALLOWED_AXIOMS), "theorems": probe_theorems},
        "deliverable_axiom_audit": {
            "exit_code": audit_rec["exit_code"], "log": audit_rec["log"],
            "expected": len(audit_expected), "reported": len(audit_parsed),
            "missing": a_missing, "violations": list(a_viol)},
    }
    out_path = os.path.join(EVIDENCE, "acceptance-pass3.json")
    with open(out_path, "w") as f:
        json.dump(evidence, f, indent=1)
    print(json.dumps({"verdict": evidence["verdict"],
                      "checks_failed": [c["check"] for c in checks if not c["ok"]]}, indent=1))
    return 0 if evidence["verdict"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
