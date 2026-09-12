#!/usr/bin/env python3
"""
D5-clean-rebuild: run the release gate from the fresh build directory and record
every command with its exact exit code.

Gate steps (a nonzero exit in any `gate: true` step fails the release):
  1. record pinned toolchain / mathlib revision and git cleanliness
  2. wipe the project build dir  (mathlib's shared prebuilt packages are untouched)
  3. lake build                  (all release libraries)
  4. lake env lean ReleaseCheck.lean
  5. lake env lean ReleaseAudit.lean
  6. lake env lean <every promoted file>            (per-artifact elaboration)
  7. comment-aware forbidden-token source scan
  8. record mathlib revision/git cleanliness again
Informational (never gates the release):
  9. lake env lean ReleaseClaims.lean               (result-card claim resolution)
"""
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timezone

ROOT = "/data3/guoshaoyang/workdir/lean_poincare"
D5 = os.path.join(ROOT, "longrun", "worktrees", "D5_clean_rebuild")
RELEASE = os.path.join(D5, "release")
LOGS = os.path.join(D5, "logs")
MANIFEST = os.path.join(D5, "manifest")
MATHLIB = os.path.join(ROOT, "poincare-lab", ".lake", "packages", "mathlib")
ELAN = os.path.join(ROOT, "elan")
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=f"{ELAN}/bin:" + os.environ["PATH"])

os.makedirs(LOGS, exist_ok=True)


def promoted_files():
    files = []
    for dirpath, dirnames, filenames in os.walk(RELEASE):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                files.append(os.path.relpath(os.path.join(dirpath, fn), RELEASE))
    # deterministic order, but never re-elaborate the two release drivers as "artifacts"
    return sorted(f for f in files if f not in ("ReleaseCheck.lean", "ReleaseAudit.lean",
                                                "ReleaseClaims.lean"))


def run_step(step_id, cmd, cwd, log_path, timeout=3600, shell=False):
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {cmd if shell else ' '.join(cmd)}\n")
        log.write(f"# cwd: {cwd}\n")
        log.flush()
        try:
            p = subprocess.run(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                               env=ENV, timeout=timeout, shell=shell)
            code = p.returncode
            timed_out = False
        except subprocess.TimeoutExpired:
            code = 124
            timed_out = True
    tail = "".join(open(log_path, errors="replace").readlines()[-25:])
    return {
        "id": step_id,
        "cmd": cmd if not shell else cmd,
        "cwd": cwd,
        "exit_code": code,
        "timed_out": timed_out,
        "duration_s": round(time.time() - t0, 1),
        "log": os.path.relpath(log_path, D5),
        "tail": tail,
    }


def main():
    steps = []

    # 1. pre-build mathlib pin / cleanliness
    steps.append(run_step("mathlib_precheck_head", ["git", "rev-parse", "HEAD"], MATHLIB,
                          os.path.join(LOGS, "00_mathlib_precheck.log")))
    steps.append(run_step("mathlib_precheck_status", ["git", "status", "--porcelain"], MATHLIB,
                          os.path.join(LOGS, "00b_mathlib_precheck_status.log")))

    # 2. fresh project build dir
    steps.append(run_step("wipe_project_build", ["rm", "-rf", ".lake/build"], RELEASE,
                          os.path.join(LOGS, "01_wipe_project_build.log")))

    # 3. fresh build of every release library
    steps.append(run_step("lake_build", ["lake", "build"], RELEASE,
                          os.path.join(LOGS, "02_lake_build.log"), timeout=5400))

    # 4. release check root
    steps.append(run_step("release_check", ["lake", "env", "lean", "ReleaseCheck.lean"], RELEASE,
                          os.path.join(LOGS, "03_release_check.log"), timeout=3600))

    # 5. kernel dependency audit
    steps.append(run_step("release_audit", ["lake", "env", "lean", "ReleaseAudit.lean"], RELEASE,
                          os.path.join(LOGS, "04_release_audit.log"), timeout=3600))

    # 6. per-artifact elaboration
    per_file = {}
    per_file_log = os.path.join(LOGS, "05_per_file_checks.log")
    t0 = time.time()
    with open(per_file_log, "w") as agg:
        for rel in promoted_files():
            p = subprocess.run(["lake", "env", "lean", rel], cwd=RELEASE, env=ENV,
                               capture_output=True, text=True, timeout=1800)
            per_file[rel] = p.returncode
            agg.write(f"=== {rel} (exit {p.returncode})\n")
            agg.write(p.stdout)
            agg.write(p.stderr)
            agg.write("\n")
            agg.flush()
    per_file_bad = {k: v for k, v in per_file.items() if v != 0}
    steps.append({
        "id": "per_file_checks",
        "cmd": "lake env lean <each release module>",
        "cwd": RELEASE,
        "exit_code": 0 if not per_file_bad else 1,
        "timed_out": False,
        "duration_s": round(time.time() - t0, 1),
        "log": os.path.relpath(per_file_log, D5),
        "files": len(per_file),
        "failures": per_file_bad,
    })

    # 7. source scan
    steps.append(run_step("source_scan",
                          ["python3", os.path.join(D5, "tools", "scan_forbidden.py"), RELEASE],
                          D5, os.path.join(LOGS, "06_source_scan.log"), timeout=600))

    # 8. post-build mathlib integrity
    steps.append(run_step("mathlib_postcheck_head", ["git", "rev-parse", "HEAD"], MATHLIB,
                          os.path.join(LOGS, "07_mathlib_postcheck.log")))
    steps.append(run_step("mathlib_postcheck_status", ["git", "status", "--porcelain"], MATHLIB,
                          os.path.join(LOGS, "07b_mathlib_postcheck_status.log")))

    # 9. informational claim-resolution probe
    claims_file = os.path.join(RELEASE, "ReleaseClaims.lean")
    if os.path.exists(claims_file):
        steps.append(run_step("claim_resolution", ["lake", "env", "lean", "ReleaseClaims.lean"],
                              RELEASE, os.path.join(LOGS, "08_claim_resolution.log"), timeout=3600))

    gate_steps = ["wipe_project_build", "lake_build", "release_check", "release_audit",
                  "per_file_checks", "source_scan"]
    by_id = {s["id"]: s for s in steps}
    gate_failures = [s["id"] for s in steps if s["id"] in gate_steps and s["exit_code"] != 0]
    result = {
        "schema": "d5-clean-rebuild/gate-results-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "release_dir": RELEASE,
        "mathlib_rev_expected": "7974e751bece493b6ff508039423ca9fa2452fa8",
        "gate_pass": not gate_failures,
        "gate_failures": gate_failures,
        "per_file": per_file,
        "per_file_failures": per_file_bad,
        "steps": steps,
        "claim_resolution_exit_code": by_id.get("claim_resolution", {}).get("exit_code"),
    }
    with open(os.path.join(MANIFEST, "gate-results.json"), "w") as fh:
        json.dump(result, fh, indent=1)
    print(json.dumps({s["id"]: s["exit_code"] for s in steps}, indent=1))
    print("gate_pass:", result["gate_pass"], "failures:", gate_failures)
    return 0 if result["gate_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
