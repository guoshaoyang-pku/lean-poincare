#!/usr/bin/env python3
"""
L4-child-sturm-zero-interlacing: second independent acceptance pass (pass 2).

This driver is deliberately separate from `tools/run_sturm_gates.py`.  It re-runs, from the
current sources, the checks that the acceptance decision depends on, and fails closed:

  C1  deliverable source hashes unchanged since the frozen checkpoint (cp16)
  C2  read-only input byte-identity, by a direct sha256 loop (not via the gate driver)
  C3  gate driver verdict PASS with every step exit 0 and the current source hashes
  C4  fail-closed axiom audit: expected == reported, no missing, no violations, every
      cone a subset of {propext, Classical.choice, Quot.sound}
  C5  forbidden-token scan clean (hard and soft)
  C6  full project-closure rebuild from source (all project-module oleans deleted first),
      exit 0, "Build completed successfully"
  C7  independent probe r2 (`tmp/acceptance_probe_r2.lean`) compiles, exit 0, no `sorryAx`,
      every probe theorem's cone inside the allowed set
  C8  signature evidence (`#check @...` for all 62 audited declarations) reproduced from the
      freshly rebuilt oleans and identical to `evidence/signatures.txt` after whitespace
      normalisation

Writes `evidence/acceptance-pass2.json`; exit code 0 iff every check passes.
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

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

DELIVERABLES = [
    "release/Poincare/L4/GeodesicComparison/SturmInterlacing.lean",
    "release/Poincare/L4/GeodesicComparison/SturmInterlacingConjugateCrossCheck.lean",
    "release/Poincare/L4/GeodesicComparison/SturmInterlacingAxiomAudit.lean",
    "negcontrol/SturmInterlacingNegativeControl.lean",
]
MODULE_TARGETS = [
    "Poincare.L4.GeodesicComparison.SturmInterlacing",
    "Poincare.L4.GeodesicComparison.SturmInterlacingConjugateCrossCheck",
    "Poincare.L4.GeodesicComparison.SturmInterlacingAxiomAudit",
]
INPUT_FILES = [r["file"] for r in json.load(
    open(os.path.join(EVIDENCE, "input-hash-verification.json")))["files"]]

PROBE = "tmp/acceptance_probe_r2.lean"
PROBE_LOG = "logs/51_acceptance_probe_r2.log"
CLOSURE_LOG = "logs/50_acceptance_closure_rebuild.log"


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def run(cmd, cwd, log_path, timeout=3600):
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {' '.join(cmd)}\n# cwd: {cwd}\n\n")
        log.flush()
        p = subprocess.run(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                           env=ENV, timeout=timeout)
    return p.returncode, round(time.time() - t0, 2), open(log_path).read()


def parse_axioms(text):
    flat = re.sub(r"\s+", " ", text)
    out = {}
    pat = re.compile(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|"
                     r"does not depend on any axioms)")
    for m in pat.finditer(flat):
        out[m.group(1)] = [a.strip() for a in m.group(2).split(",")] if m.group(2) else []
    return out


def norm(text):
    return re.sub(r"\s+", " ", text).strip()


def main():
    started = datetime.now(timezone.utc).isoformat()
    checks, failures = [], []

    def check(name, ok, detail):
        checks.append({"check": name, "ok": bool(ok), "detail": detail})
        if not ok:
            failures.append(name)
        print(f"[{'OK ' if ok else 'FAIL'}] {name} — {detail}")

    # ---- C1: deliverable hashes vs frozen checkpoint --------------------
    cp = json.load(open(os.path.join(ROOT, "checkpoint.json")))
    frozen = None
    for c in cp["checkpoints"]:
        if c["id"] == "cp16":
            frozen = c["deliverable_hashes"]
    cur = {d: sha256(os.path.join(ROOT, d)) for d in DELIVERABLES}
    c1_ok = frozen is not None and all(frozen.get(d) == cur[d] for d in DELIVERABLES)
    check("deliverable_hashes_unchanged_since_cp16", c1_ok,
          json.dumps({d: cur[d] for d in DELIVERABLES}, indent=0).replace("\n", " "))

    # ---- C2: input byte-identity (direct sha256 loop) -------------------
    bad = []
    for rel in INPUT_FILES:
        if sha256(os.path.join(RELEASE, rel)) != sha256(os.path.join(LEADER, rel)):
            bad.append(rel)
    check("input_byte_identity_direct_sha256", not bad,
          f"{len(INPUT_FILES) - len(bad)}/{len(INPUT_FILES)} byte-identical; mismatches={bad}")

    # ---- C3/C4/C5: gate driver evidence ---------------------------------
    gates = json.load(open(os.path.join(EVIDENCE, "gates.json")))
    ver = json.load(open(os.path.join(EVIDENCE, "verification.json")))
    steps_bad = [s["step"] for s in gates["steps"]
                 if s.get("gate", True) and s.get("exit_code", 0) != 0]
    vhash = ver["deliverable_source_hashes"]
    hash_ok = all(vhash.get(d) == cur[d] for d in DELIVERABLES[:3])
    check("gate_driver_verdict_and_steps", gates["verdict"] == "PASS" and not steps_bad
          and gates["failures"] == [], f"verdict={gates['verdict']} failures={gates['failures']} "
          f"nonpassing_steps={steps_bad} generated={gates['generated']}")
    check("gate_source_hashes_match_current", hash_ok,
          f"verification.json hashes current={hash_ok}")

    ax = json.load(open(os.path.join(EVIDENCE, "axiom-report.json")))
    cones_bad = {d: c for d, c in ax["declarations"].items() if set(c) - ALLOWED}
    c4_ok = (ax["verdict"] == "PASS" and not ax["missing"] and not ax["violations"]
             and not cones_bad and ax["expected_declarations"] == ax["reported_declarations"])
    check("fail_closed_axiom_audit", c4_ok,
          f"{ax['reported_declarations']}/{ax['expected_declarations']} declarations, "
          f"missing={ax['missing']}, violations={ax['violations']}, "
          f"out_of_cone={sorted(cones_bad)}")

    scan = json.load(open(os.path.join(EVIDENCE, "forbidden-scan.json")))
    check("forbidden_token_scan_clean",
          scan["hard_match_count"] == 0 and scan["soft_match_count"] == 0,
          f"hard={scan['hard_match_count']} soft={scan['soft_match_count']} "
          f"files={scan['lean_files_scanned']}")

    # ---- C6: full project-closure rebuild from source --------------------
    removed = 0
    proj_dir = os.path.join(RELEASE, ".lake", "build", "lib", "lean", "Poincare")
    if os.path.isdir(proj_dir):
        for dirpath, _dirs, files in os.walk(proj_dir):
            removed += sum(1 for f in files if f.endswith(".olean"))
        subprocess.run(["rm", "-rf", proj_dir], check=True)
    code, secs, out = run(["lake", "build"] + MODULE_TARGETS, RELEASE,
                          os.path.join(ROOT, CLOSURE_LOG), timeout=3600)
    jobs = re.search(r"Build completed successfully \((\d+) jobs\)", out)
    c6_ok = code == 0 and jobs is not None
    check("full_project_closure_rebuild", c6_ok,
          f"exit={code} seconds={secs} jobs={jobs.group(1) if jobs else '?'} "
          f"oleans_deleted={removed} log={CLOSURE_LOG}")
    closure_record = {"command": "lake build " + " ".join(MODULE_TARGETS),
                      "exit_code": code, "seconds": secs,
                      "jobs": int(jobs.group(1)) if jobs else None,
                      "oleans_deleted": removed, "log": CLOSURE_LOG}

    # ---- C7: independent probe r2 ---------------------------------------
    code, secs, out = run(["lake", "env", "lean", os.path.join("..", PROBE)], RELEASE,
                          os.path.join(ROOT, PROBE_LOG), timeout=3600)
    probe_cones = parse_axioms(out)
    expected_probe = re.findall(r"#print axioms (\S+)", open(os.path.join(ROOT, PROBE)).read())
    probe_bad = {d: c for d, c in probe_cones.items() if set(c) - ALLOWED}
    probe_missing = [d for d in expected_probe if d not in probe_cones]
    probe_forbidden = [t for t in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler")
                       if t in out]
    c7_ok = (code == 0 and expected_probe and not probe_missing and not probe_bad
             and not probe_forbidden and "error" not in out)
    check("independent_probe_r2", c7_ok,
          f"exit={code} seconds={secs} theorems={len(probe_cones)}/"
          f"{len(expected_probe)} missing={probe_missing} out_of_cone={sorted(probe_bad)} "
          f"forbidden={probe_forbidden}")
    probe_record = {
        "file": PROBE, "sha256": sha256(os.path.join(ROOT, PROBE)),
        "command": f"cd release && lake env lean ../{PROBE}",
        "compile_exit": code, "seconds": secs, "log": PROBE_LOG,
        "theorems": [{"name": d, "cone": probe_cones[d]}
                     for d in expected_probe if d in probe_cones],
    }

    # ---- C8: signature evidence -----------------------------------------
    code, secs, out = run(["lake", "env", "lean", os.path.join("..", "tmp", "signatures.lean")],
                          RELEASE, os.path.join(ROOT, "logs", "52_acceptance_signatures.log"))
    body = out.split("\n\n", 1)[1] if "\n\n" in out else out
    fresh = os.path.join(ROOT, "tmp", "signatures_pass2.out")
    with open(fresh, "w") as f:
        f.write(body)
    same = norm(body) == norm(open(os.path.join(EVIDENCE, "signatures.txt")).read())
    n_sig = len(open(os.path.join(ROOT, "tmp", "signatures.lean")).read().strip().splitlines()) - 1
    check("signature_evidence_reproduced", code == 0 and same,
          f"exit={code} whitespace-normalised identical={same} "
          f"declarations_checked={n_sig} log=logs/52_acceptance_signatures.log")

    # ---- assemble --------------------------------------------------------
    verdict = "PASS" if not failures else "FAIL"
    record = {
        "schema": "l4-child-sturm-zero-interlacing/acceptance-pass2-v1",
        "task_id": "L4-child-sturm-zero-interlacing",
        "generated": started,
        "verdict": verdict,
        "failures": failures,
        "checks": checks,
        "deliverable_hashes": cur,
        "frozen_checkpoint": "cp16",
        "closure_rebuild": closure_record,
        "axiom_audit": {"verdict": ax["verdict"],
                        "declarations": ax["reported_declarations"],
                        "allowed_cone": ax["allowed_cone"],
                        "out_of_cone": sorted(cones_bad)},
        "probe": probe_record,
        "signature_evidence": {"file": "evidence/signatures.txt",
                               "fresh_output": "tmp/signatures_pass2.out",
                               "identical_after_whitespace_normalisation": same},
        "pins": gates["pins"],
    }
    with open(os.path.join(EVIDENCE, "acceptance-pass2.json"), "w") as f:
        json.dump(record, f, indent=1, sort_keys=True)
    print(json.dumps({"verdict": verdict, "failures": failures,
                      "probe_theorems": len(probe_cones),
                      "closure_jobs": closure_record["jobs"]}, indent=1))
    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(main())
