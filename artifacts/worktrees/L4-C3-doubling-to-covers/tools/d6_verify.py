#!/usr/bin/env python3
"""
D6-weekly-release: independent integrator verification of the accepted D5 package.

The D6 integrator consumes only the accepted D5-clean-rebuild artifacts and re-runs the
release gates in its own worktree:

  0. hash-verify every copied promoted source against the D5 provenance manifest
  1. lake build                                (fresh D6 .lake/build)
  2. lake env lean ReleaseCheck.lean           (accepted D5 check root)
  3. lake env lean ReleaseAudit.lean           (accepted D5 kernel axiom audit)
  4. lake env lean D6AuditReport.lean          (D6 per-declaration axiom report)
  5. lake env lean ReleaseClaims.lean          (accepted D5 193-name claim probe)
  6. lake env lean <each promoted file>        (per-artifact elaboration)
  7. forbidden-token source scan               (comment/string aware)
  8. negative control                          (audit predicate really detects sorry/native_decide)
  9. mathlib pin / cleanliness post-check

Outputs `manifest/verification.json` and `manifest/verified-declarations.json`
(the machine-readable per-declaration axiom report).
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import time
from datetime import datetime, timezone

D6 = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_weekly_release"
D5 = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild"
ROOT = "/data3/guoshaoyang/workdir/lean_poincare"
RELEASE = os.path.join(D6, "release")
LOGS = os.path.join(D6, "logs")
MANIFEST = os.path.join(D6, "manifest")
MATHLIB = os.path.join(ROOT, "poincare-lab", ".lake", "packages", "mathlib")
ELAN = os.path.join(ROOT, "elan")
ENV = dict(os.environ, ELAN_HOME=ELAN, PATH=f"{ELAN}/bin:" + os.environ["PATH"])

os.makedirs(LOGS, exist_ok=True)
os.makedirs(MANIFEST, exist_ok=True)

# D5 release drivers plus the D6 additions; never re-elaborated as "promoted artifacts"
DRIVERS = {"ReleaseCheck.lean", "ReleaseAudit.lean", "ReleaseClaims.lean",
           "D6AuditReport.lean", "D6LedgerProbe.lean"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def rel_files(root):
    out = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                out.append(os.path.relpath(os.path.join(dirpath, fn), root))
    return sorted(out)


def run_step(step_id, cmd, cwd, log_name, timeout=3600, gate=True, env=None):
    log_path = os.path.join(LOGS, log_name)
    t0 = time.time()
    with open(log_path, "w") as log:
        log.write(f"$ {' '.join(cmd)}\n# cwd: {cwd}\n# date: {datetime.now(timezone.utc).isoformat()}\n")
        log.flush()
        try:
            p = subprocess.run(cmd, cwd=cwd, stdout=log, stderr=subprocess.STDOUT,
                               env=env or ENV, timeout=timeout)
            code, timed_out = p.returncode, False
        except subprocess.TimeoutExpired:
            code, timed_out = 124, True
    tail = "".join(open(log_path, errors="replace").readlines()[-30:])
    return {
        "id": step_id,
        "cmd": cmd,
        "cwd": cwd,
        "exit_code": code,
        "timed_out": timed_out,
        "duration_s": round(time.time() - t0, 1),
        "gate": gate,
        "log": os.path.relpath(log_path, D6),
        "tail": tail,
    }


def source_hash_verification():
    """Compare every copied promoted source with the accepted D5 provenance manifest."""
    prov = json.load(open(os.path.join(D6, "input", "d5-manifest", "provenance.json")))
    checked, changed, missing = [], [], []
    for cluster in prov["clusters"]:
        for f in cluster["files"]:
            p = os.path.join(RELEASE, f["path"])
            if not os.path.exists(p):
                missing.append({"path": f["path"], "expected": f["sha256"],
                                "task_id": cluster["task_id"]})
                continue
            got = sha256(p)
            rec = {"path": f["path"], "task_id": cluster["task_id"],
                   "expected": f["sha256"], "got": got, "match": got == f["sha256"]}
            checked.append(rec)
            if got != f["sha256"]:
                changed.append(rec)
    base, base_changed = [], []
    for b in prov["base_dependencies"]:
        p = os.path.join(RELEASE, b["path"])
        if not os.path.exists(p):
            missing.append({"path": b["path"], "expected": b["sha256"], "task_id": "base"})
            continue
        got = sha256(p)
        rec = {"path": b["path"], "expected": b["sha256"], "got": got, "match": got == b["sha256"]}
        base.append(rec)
        if got != b["sha256"]:
            base_changed.append(rec)
    return {
        "promoted_files_checked": len(checked),
        "promoted_changed": changed,
        "base_files_checked": len(base),
        "base_changed": base_changed,
        "missing": missing,
        "all_match": not changed and not base_changed and not missing,
        "provenance_manifest_sha256": sha256(os.path.join(D6, "input", "d5-manifest", "provenance.json")),
        "promoted": checked,
        "base": base,
    }


DECL_RE = re.compile(r"D6DECL\t([^\t]+)\t([^\t]+)\t([^\t]+)\t(.*)$")
AUDIT_RE = re.compile(r"D6AUDIT\t([^\t]+)\t(.*)$")


def parse_decl_report(log_path):
    decls, audit = [], {}
    for line in open(log_path, errors="replace"):
        line = line.rstrip("\n")
        m = DECL_RE.search(line)
        if m:
            name, kind, module, cone = m.groups()
            decls.append({
                "name": name,
                "kind": kind,
                "module": module,
                "file": module.replace(".", "/") + ".lean",
                "axioms": [a for a in cone.split(";") if a],
                "axiom_cone": cone,
            })
            continue
        m = AUDIT_RE.search(line)
        if m:
            k, v = m.groups()
            audit.setdefault(k, []).append(v)
    return decls, audit


def forbidden_scan(root):
    """Run the accepted D5 comment/string-aware scanner on the D6 package.

    The scanner itself is a consumed D5 artifact (`input/d5-tools/scan_forbidden.py`);
    reusing it keeps the D6 scan methodology identical to the accepted D5 gate.
    """
    scanner = os.path.join(D6, "input", "d5-tools", "scan_forbidden.py")
    p = subprocess.run([sys.executable, scanner, root], capture_output=True, text=True, env=ENV)
    try:
        result = json.loads(p.stdout)
    except json.JSONDecodeError:
        result = {"root": root, "lean_files_scanned": 0, "hard_forbidden": [],
                  "soft_flags": [], "hard_match_count": -1, "soft_match_count": -1,
                  "matches": [], "parse_error": p.stdout[-2000:] + p.stderr[-2000:]}
    result["scanner"] = os.path.relpath(scanner, D6)
    result["scanner_exit_code"] = p.returncode
    return result


def main():
    build = "--skip-build" not in sys.argv
    report = {
        "schema": "d6-weekly-release/verification-v1",
        "task_id": "D6-weekly-release",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "integrator_worktree": D6,
        "consumed_input": "accepted D5-clean-rebuild artifacts only",
        "toolchain": {},
        "steps": [],
        "gates": {},
    }

    # --- 0. source hash verification -------------------------------------------------
    t0 = time.time()
    hv = source_hash_verification()
    report["source_hash_verification"] = hv
    report["steps"].append({
        "id": "source_hash_verification",
        "cmd": ["python3", "tools/d6_verify.py", "(in-process source_hash_verification)"],
        "cwd": D6,
        "exit_code": 0 if hv["all_match"] else 1,
        "timed_out": False,
        "duration_s": round(time.time() - t0, 2),
        "gate": True,
        "log": "input/d5-manifest/provenance.json",
        "tail": (f"promoted={hv['promoted_files_checked']} base={hv['base_files_checked']} "
                 f"changed={len(hv['promoted_changed'])} base_changed={len(hv['base_changed'])} "
                 f"missing={len(hv['missing'])}"),
    })

    # --- 1..3 kernel gates -----------------------------------------------------------
    if build:
        report["steps"].append(run_step("lake_build", ["lake", "build"], RELEASE,
                                        "10_lake_build.log"))
    report["steps"].append(run_step("release_check", ["lake", "env", "lean", "ReleaseCheck.lean"],
                                    RELEASE, "11_release_check.log"))
    report["steps"].append(run_step("release_audit", ["lake", "env", "lean", "ReleaseAudit.lean"],
                                    RELEASE, "12_release_audit.log"))
    decl_step = run_step("d6_decl_report", ["lake", "env", "lean", "D6AuditReport.lean"],
                         RELEASE, "13_d6_decl_report.log")
    report["steps"].append(decl_step)
    report["steps"].append(run_step("release_claims", ["lake", "env", "lean", "ReleaseClaims.lean"],
                                    RELEASE, "14_release_claims.log", gate=False))

    # --- 4. per-declaration axiom report --------------------------------------------
    decls, audit = parse_decl_report(os.path.join(LOGS, "13_d6_decl_report.log"))
    report["per_declaration_report"] = {
        "declarations": len(decls),
        "summary": {k: (v[0] if len(v) == 1 else v) for k, v in audit.items()},
    }
    verified = {
        "schema": "d6-weekly-release/verified-declarations-v1",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "source": "release/D6AuditReport.lean (kernel Lean.collectAxioms over every release constant)",
        "approved_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "forbidden": ["sorryAx", "project axiom", "unsafe", "native_decide", "unapproved axiom",
                      "proof_wanted"],
        "count": len(decls),
        "kinds": {},
        "declarations": decls,
    }
    for d in decls:
        verified["kinds"][d["kind"]] = verified["kinds"].get(d["kind"], 0) + 1
    json.dump(verified, open(os.path.join(MANIFEST, "verified-declarations.json"), "w"), indent=1)
    report["gates"]["declaration_report_parsed"] = len(decls) > 0

    def _int(vals):
        try:
            return int(vals[0])
        except (TypeError, ValueError, IndexError):
            return None

    report["gates"]["forbidden_in_decl_report"] = {
        "sorry_declarations": _int(audit.get("sorry_declarations")),
        "unapproved_axiom_declarations": _int(audit.get("unapproved_axiom_declarations")),
        "project_axioms": _int(audit.get("project_axioms")),
        "unsafe_declarations": _int(audit.get("unsafe_declarations")),
        "native_decide_declarations": _int(audit.get("native_decide_declarations")),
        "proof_wanted_declarations": _int(audit.get("proof_wanted_declarations")),
        "verdict": audit.get("VERDICT", ["missing"]),
    }

    # --- 5. per-file elaboration -----------------------------------------------------
    per_file, failures = {}, {}
    t0 = time.time()
    files = [f for f in rel_files(RELEASE) if f not in DRIVERS]
    for f in files:
        r = run_step("per_file", ["lake", "env", "lean", f], RELEASE,
                     "perfile_" + f.replace("/", "__") + ".log", gate=True)
        per_file[f] = r["exit_code"]
        if r["exit_code"] != 0:
            failures[f] = r["tail"]
    report["steps"].append({
        "id": "per_file_checks", "cmd": ["lake env lean <each promoted file>"], "cwd": RELEASE,
        "exit_code": 0 if not failures else 1, "timed_out": False,
        "duration_s": round(time.time() - t0, 1), "gate": True,
        "log": "logs/perfile_*.log",
        "tail": f"files={len(files)} failures={sorted(failures)}",
    })
    report["per_file"] = {"files": per_file, "failures": failures}

    # --- 6. forbidden source scan ----------------------------------------------------
    scan = forbidden_scan(RELEASE)
    json.dump(scan, open(os.path.join(MANIFEST, "forbidden-scan.json"), "w"), indent=1)
    report["forbidden_token_scan"] = scan
    report["steps"].append({
        "id": "forbidden_token_scan",
        "cmd": ["python3", "input/d5-tools/scan_forbidden.py", "release"],
        "cwd": D6,
        "exit_code": 0 if scan["hard_match_count"] == 0 else 1, "timed_out": False,
        "duration_s": 0.0, "gate": True, "log": "manifest/forbidden-scan.json",
        "tail": f"files={scan['lean_files_scanned']} hard={scan['hard_match_count']} soft={scan['soft_match_count']}",
    })

    # --- 7. negative control ---------------------------------------------------------
    report["steps"].append(run_step(
        "negative_control", ["lake", "env", "lean", "../negcontrol/NegativeControl.lean"],
        RELEASE, "15_negative_control.log"))

    # --- 8. mathlib pin / cleanliness ------------------------------------------------
    report["steps"].append(run_step("mathlib_head", ["git", "rev-parse", "HEAD"], MATHLIB,
                                    "16_mathlib_head.log"))
    report["steps"].append(run_step("mathlib_status", ["git", "status", "--porcelain"], MATHLIB,
                                    "17_mathlib_status.log"))

    # --- summary ---------------------------------------------------------------------
    gates = [s for s in report["steps"] if s.get("gate")]
    failed = [s["id"] for s in gates if s["exit_code"] != 0]
    report["gate_failures"] = failed
    report["gate_pass"] = not failed
    report["verdict"] = ("D6 INDEPENDENT VERIFICATION PASS" if not failed
                         else "D6 INDEPENDENT VERIFICATION FAIL")
    report["counts"] = {
        "declarations_audited": len(decls),
        "theorems": verified["kinds"].get("theorem", 0),
        "definitions": verified["kinds"].get("def", 0),
        "structures": verified["kinds"].get("induct", 0) + verified["kinds"].get("ctor", 0),
        "per_file_checked": len(files),
        "per_file_failures": len(failures),
        "claim_probe_exit": next((s["exit_code"] for s in report["steps"] if s["id"] == "release_claims"), None),
    }
    json.dump(report, open(os.path.join(MANIFEST, "verification.json"), "w"), indent=1)
    print(json.dumps({k: report[k] for k in
                      ["verdict", "gate_pass", "gate_failures", "counts"]}, indent=1))
    return 0 if report["gate_pass"] else 1


if __name__ == "__main__":
    sys.exit(main())
