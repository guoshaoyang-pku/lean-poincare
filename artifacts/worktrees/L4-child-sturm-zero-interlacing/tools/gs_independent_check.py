#!/usr/bin/env python3
"""
Second-invocation independent acceptance check for `L4-child-sturm-zero-interlacing`.

This driver is deliberately independent of `tools/run_sturm_gates.py`,
`tools/acceptance_pass2.py` and `tools/acceptance_pass3.py`: it uses a new probe
(`tmp/gs_independent_probe.lean`, written from scratch) and re-derives the release-level
facts from the files on disk.

Fail-closed gates:

  1. full project-closure rebuild: every project `.olean` under
     `release/.lake/build/lib/lean/Poincare` is deleted, then the three deliverable modules
     are rebuilt with `lake build` (exit 0, jobs > 0); the `.lean` sources are byte-identical
     before and after (the build writes only oleans);
  2. the fresh probe compiles against those rebuilt oleans with `lake env lean`
     (exit 0, no `error` in the output);
  3. every `#print axioms` line of the probe is reported exactly once and its cone is a
     subset of {propext, Classical.choice, Quot.sound} (no `sorryAx`);
  4. the probe source contains no `sorry`/`admit`/`axiom`/`unsafe` token;
  5. the axiom-audit module re-run on the rebuilt oleans reports all 62 declarations with
     cones inside the allowed set;
  6. the five deliverable files match the hashes recorded in the result card;
  7. all 13 read-only inputs are byte-identical to the leader release;
  8. the main deliverable module does not import the cross-checked prior result
     `ConjugatePointBound` (the target theorem is not assumed) and does not mention
     `conjugate_point_bound` in any declaration type;
  9. no declaration name in the two deliverable modules collides with a declaration of the
     imported prior art (`SturmZeroCount.lean`, `ConjugatePointBound.lean`) or of the leader
     release tree;
 10. the axiom-audit driver `#print axioms`-covers every declaration of the two deliverable
     modules, and the stored signature transcript `evidence/signatures.txt` contains a
     signature entry for every own declaration.

Outputs `evidence/gs-independent-acceptance.json`; exits nonzero on any failure.
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
LEADER = os.path.normpath(os.path.join(ROOT, os.pardir, "leaders",
                                      "L4-geometric-critical-path", "release"))
EV = os.path.join(ROOT, "evidence")
LOGS = os.path.join(ROOT, "logs")
ELAN = "/data3/guoshaoyang/workdir/lean_poincare/elan"
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=f"{ELAN}/bin:" + os.environ["PATH"])

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
PROBE = "tmp/gs_independent_probe.lean"
PROBE_LOG = "70_gs_independent_probe.log"

CORE = "release/Poincare/L4/GeodesicComparison/SturmInterlacing.lean"
CROSS = "release/Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean"
AUDIT = "release/Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean"
AUDIT_REL = "Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean"
NEG = "negcontrol/SturmInterlacingNegativeControl.lean"

CARD = "longrun/results/L4-child-sturm-zero-interlacing.json"
MODULE_KEYS = {
    "core": CORE, "cross_check": CROSS, "axiom_audit": AUDIT,
    "negative_control": NEG, "gate_driver": "tools/run_sturm_gates.py",
}

MODULES = ["Poincare.L4.GeodesicComparison.SturmInterlacing",
           "Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck",
           "Poincare.L4.GeodesicComparison.SturmInterlacingAxiomAudit"]

BUILD_ROOT = os.path.join(RELEASE, ".lake", "build", "lib", "lean", "Poincare")

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

PRIOR_ART = [
    "release/Poincare/L4/GeodesicComparison/SturmZeroCount.lean",
    "release/Poincare/L4/GeodesicComparison/ConjugatePointBound.lean",
]

DECL_RE = re.compile(
    r"^(?:theorem|lemma|noncomputable def|def|abbrev|instance|structure|class)\s+"
    r"([A-Za-z0-9_'.]+)", re.M)

checks = []


def check(name, ok, detail=""):
    checks.append({"check": name, "ok": bool(ok), "detail": detail})
    print(f"[{'OK ' if ok else 'FAIL'}] {name} — {detail}")


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def parse_cones(text):
    flat = re.sub(r"\s+", " ", text)
    out = {}
    pat = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|"
                     r"does not depend on any axioms)")
    for m in pat.finditer(flat):
        out[m.group(1)] = [a.strip() for a in m.group(2).split(",")] if m.group(2) else []
    return out


def decls_of(path):
    return set(DECL_RE.findall(open(path).read()))


def lean_tree_hashes():
    out = {}
    for dirpath, dirnames, filenames in os.walk(RELEASE):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in filenames:
            if fn.endswith(".lean"):
                p = os.path.join(dirpath, fn)
                out[os.path.relpath(p, ROOT)] = sha(p)
    return out


def run_logged(step, cmd, log_name, timeout=3600):
    log_path = os.path.join(LOGS, log_name)
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {' '.join(cmd)}\n# cwd: {RELEASE}\n\n")
        log.flush()
        p = subprocess.run(cmd, cwd=RELEASE, stdout=log, stderr=subprocess.STDOUT,
                           env=ENV, timeout=timeout)
    return (p.returncode, open(log_path).read(), round(time.time() - t0, 2),
            os.path.relpath(log_path, ROOT))


def main():
    started = datetime.now(timezone.utc).isoformat()

    # ---- 1. full project-closure rebuild --------------------------------
    src_before = lean_tree_hashes()
    oleans_deleted = 0
    if os.path.isdir(BUILD_ROOT):
        for dirpath, _dirnames, filenames in os.walk(BUILD_ROOT):
            oleans_deleted += sum(1 for fn in filenames
                                  if fn.endswith((".olean", ".ilean", ".trace")))
        shutil.rmtree(BUILD_ROOT)
    clo_exit, clo_out, clo_secs, clo_log = run_logged(
        "closure_rebuild", ["lake", "build"] + MODULES, "70_gs_closure_rebuild.log")
    m = re.search(r"Build completed successfully \((\d+) jobs\)", clo_out)
    jobs = int(m.group(1)) if m else -1
    src_after = lean_tree_hashes()
    check("closure_rebuild_exit0_jobs", clo_exit == 0 and jobs > 0,
          f"exit={clo_exit} jobs={jobs} oleans_deleted={oleans_deleted} "
          f"seconds={clo_secs} log={clo_log}")
    check("closure_rebuild_left_sources_unchanged", src_before == src_after,
          f"lean_files={len(src_before)} differing="
          f"{[k for k in src_before if src_before.get(k) != src_after.get(k)][:3]}")

    # ---- 2. compile the fresh probe against the rebuilt oleans ----------
    probe_exit, probe_out, probe_secs, probe_log = run_logged(
        "probe", ["lake", "env", "lean", os.path.join("..", PROBE)], PROBE_LOG)
    check("probe_compiles_clean", probe_exit == 0 and "error" not in probe_out,
          f"exit={probe_exit}, seconds={probe_secs}, log={probe_log}")

    # ---- 3. probe axiom cones, fail-closed ------------------------------
    probe_src = open(os.path.join(ROOT, PROBE)).read()
    expected = re.findall(r"#print axioms (\S+)", probe_src)
    cones = parse_cones(probe_out)
    missing = [d for d in expected if d not in cones]
    bad = {d: c for d, c in cones.items() if not set(c) <= ALLOWED}
    sorry = {d: c for d, c in cones.items() if "sorryAx" in c}
    check("probe_axiom_cones_reported_once",
          len(cones) == len(expected) and not missing,
          f"expected={len(expected)} reported={len(cones)} missing={missing}")
    check("probe_axiom_cones_in_allowed_set", not bad and not sorry,
          f"allowed={sorted(ALLOWED)} out_of_cone={bad} sorryAx={sorted(sorry)}")

    # ---- 4. probe source hygiene ---------------------------------------
    tokens = re.findall(r"\b(sorry|admit|axiom|unsafe|opaque|partial|native_decide)\b",
                        probe_src)
    check("probe_source_no_forbidden_tokens", not tokens, f"tokens={sorted(set(tokens))}")

    # ---- 5. audit module re-run on the rebuilt oleans -------------------
    audit_src = open(os.path.join(ROOT, AUDIT)).read()
    audit_expected = re.findall(r"#print axioms (\S+)", audit_src)
    au_exit, au_out, au_secs, au_log = run_logged(
        "audit", ["lake", "env", "lean", AUDIT_REL], "71_gs_axiom_audit.log")
    au_cones = parse_cones(au_out)
    au_missing = [d for d in audit_expected if d not in au_cones]
    au_bad = {d: c for d, c in au_cones.items() if not set(c) <= ALLOWED}
    check("audit_rerun_all_62_in_cone",
          au_exit == 0 and not au_missing and not au_bad
          and len(au_cones) == len(audit_expected),
          f"exit={au_exit} expected={len(audit_expected)} reported={len(au_cones)} "
          f"missing={au_missing} out_of_cone={au_bad} seconds={au_secs} log={au_log}")

    # ---- 6. deliverable hashes match the result card --------------------
    card = json.load(open(os.path.join(ROOT, CARD)))
    h_bad = []
    hashes = {}
    for key, rel in MODULE_KEYS.items():
        h = sha(os.path.join(ROOT, rel))
        hashes[key] = h
        if card.get("module_hashes", {}).get(key) != h:
            h_bad.append(key)
    check("deliverable_hashes_match_card", not h_bad,
          f"mismatched={h_bad} core={hashes['core'][:16]}...")

    # ---- 7. input byte-identity vs the leader release -------------------
    input_bad = []
    input_records = []
    for rel in INPUT_FILES:
        lp = os.path.join(RELEASE, rel)
        rp = os.path.join(LEADER, rel)
        lo = sha(lp) if os.path.exists(lp) else None
        ro = sha(rp) if os.path.exists(rp) else None
        same = lo is not None and lo == ro
        if not same:
            input_bad.append(rel)
        input_records.append({"file": rel, "sha256": lo, "leader_sha256": ro,
                              "byte_identical": same})
    check("inputs_byte_identical_to_leader", not input_bad,
          f"files={len(INPUT_FILES)} mismatched={input_bad}")

    # ---- 8. main module does not assume the cross-checked target --------
    core_src = open(os.path.join(ROOT, CORE)).read()
    imports = re.findall(r"^import\s+(\S+)", core_src, re.M)
    check("main_module_does_not_import_conjugate_point_bound",
          all("ConjugatePointBound" not in i for i in imports),
          f"imports={imports}")
    code = re.sub(r"/-.*?-/", "", core_src, flags=re.S)
    code = re.sub(r"--[^\n]*", "", code)
    check("main_module_code_never_mentions_conjugate_point_bound",
          "conjugate_point_bound" not in code,
          "identifier absent from code (only in doc comments)")

    # ---- 9. no declaration-name collision with prior art / leader -------
    own = set()
    for rel in (CORE, CROSS):
        own |= decls_of(os.path.join(ROOT, rel))
    prior = set()
    for rel in PRIOR_ART:
        prior |= decls_of(os.path.join(ROOT, rel))
    leader = set()
    lgc = os.path.join(LEADER, "Poincare", "L4", "GeodesicComparison")
    for fn in os.listdir(lgc):
        if fn.endswith(".lean"):
            leader |= decls_of(os.path.join(lgc, fn))
    collisions_prior = sorted(own & prior)
    collisions_leader = sorted(own & leader)
    check("no_prior_art_name_collisions", not collisions_prior, f"{collisions_prior}")
    check("no_leader_name_collisions", not collisions_leader, f"{collisions_leader}")

    # ---- 10. audit + signature coverage of every deliverable decl -------
    audit_short = [d.split(".")[-1] for d in audit_expected]
    uncovered = sorted(own - set(audit_short))
    check("axiom_audit_covers_every_own_declaration", not uncovered,
          f"own={len(own)} audited_own={len(set(audit_short) & own)} uncovered={uncovered}")
    sig_txt = open(os.path.join(EV, "signatures.txt")).read()
    sig_missing = sorted(n for n in own if f"Poincare.L4.GeodesicComparison.{n} :" not in sig_txt)
    check("signature_transcript_covers_every_own_declaration", not sig_missing,
          f"own={len(own)} missing_from_signatures_txt={sig_missing}")

    verdict = "PASS" if all(c["ok"] for c in checks) else "FAIL"
    evidence = {
        "schema": "l4-child-sturm-zero-interlacing/gs-independent-acceptance-v1",
        "task_id": "L4-child-sturm-zero-interlacing",
        "generated": started,
        "invocation": "second invocation (continuation), independent fresh probe",
        "verdict": verdict,
        "checks": checks,
        "closure_rebuild": {
            "command": "lake build " + " ".join(MODULES),
            "cwd": RELEASE,
            "exit_code": clo_exit,
            "jobs": jobs,
            "oleans_deleted": oleans_deleted,
            "seconds": clo_secs,
            "log": clo_log,
        },
        "audit_rerun": {
            "command": f"lake env lean {AUDIT_REL}",
            "exit_code": au_exit,
            "expected": len(audit_expected),
            "reported": len(au_cones),
            "missing": au_missing,
            "out_of_cone": au_bad,
            "seconds": au_secs,
            "log": au_log,
        },
        "probe": {
            "file": PROBE,
            "sha256": sha(os.path.join(ROOT, PROBE)),
            "command": f"lake env lean ../{PROBE} (cwd release)",
            "compile_exit": probe_exit,
            "log": "logs/" + PROBE_LOG,
            "declarations_audited": len(cones),
            "out_of_cone": bad,
            "theorems": [{"name": d, "cone": cones.get(d)} for d in expected],
        },
        "deliverable_hashes": hashes,
        "card_module_hashes": card.get("module_hashes"),
        "inputs": input_records,
        "own_declarations": sorted(own),
        "probe_content": {
            "GS1": "jacobiSol 3 zero pi/sqrt 3 strictly inside (0, 2 pi) = (0, pi/sqrt(1/4))",
            "GS1b": "exists_zero_of_curvature_lt on (k1,k2)=(3,1/4) with the shifted model",
            "GS2": "firstPositiveZero (jacobiSol 5) <= pi/sqrt 2 from K=2",
            "GS2b": "closed form pi/sqrt 5 <= pi/sqrt 2",
            "GS2c": "horizon form H=2, K=4, k=5: firstPositiveZero (jacobiSol 5) <= pi/2",
            "GS2d": "attainment: jacobiSol 5 (firstPositiveZero (jacobiSol 5)) = 0 and positivity",
            "GS3": "equality case k = K = 3 forces the endpoint zero",
            "GS4": "wronskian t*cos t <= sin t at pi/3",
            "GS4b": "wronskian derivative at pi/3 equals -pi*sqrt 3/6",
            "GS5": "literal acceptance branch refuted (prior art, reused by name)",
            "GS5b": "firstPositiveZero sin = pi",
            "GS6": "leader cross-check sample k=3, K=1, T=3/2 through the engine route and the leader theorem",
        },
    }
    with open(os.path.join(EV, "gs-independent-acceptance.json"), "w") as f:
        json.dump(evidence, f, indent=1)
    print(json.dumps({"verdict": verdict,
                      "checks_failed": [c["check"] for c in checks if not c["ok"]],
                      "probe_declarations": len(cones),
                      "closure_jobs": jobs,
                      "audit_reported": len(au_cones)}, indent=1))
    return 0 if verdict == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
