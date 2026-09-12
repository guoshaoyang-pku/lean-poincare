#!/usr/bin/env python3
"""L4-C3 doubling-to-covers — verification driver.

Run from the worktree root (or anywhere; paths are derived from this file):

    python3 tools/l4c3_audit.py

The driver, operating only inside this worktree and only from ``release/``:

1. computes SHA-256 hashes of the authored L4-C3 sources, the imported D12 interface
   sources, the audit file, the pinned toolchain and the mathlib manifest;
2. scans the authored sources for the forbidden trust primitives
   (``sorry``, ``axiom``, ``admit``, ``unsafe``, ``native_decide``, ``proof_wanted``)
   with Lean comments stripped;
3. runs the pinned per-module build and the package default build, recording exit codes;
4. runs the fail-closed per-declaration kernel axiom audit
   (``Audit/L4C3AxiomAudit.lean``) and parses every axiom cone;
5. runs the pre-existing D5 negative control to show the detector still catches
   ``sorryAx`` and ``native_decide``.

It writes evidence files under ``evidence/`` and prints a summary.  It does not modify
any other worktree, queue, test or global setting.
"""

from __future__ import annotations

import datetime
import hashlib
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RELEASE = os.path.join(ROOT, "release")
EVIDENCE = os.path.join(ROOT, "evidence")
ELAN_HOME = "/data3/guoshaoyang/workdir/lean_poincare/elan"

AUTHORED = [
    "Poincare/L4/DoublingToCovers/Bridge.lean",
    "Poincare/L4/DoublingToCovers/Counterexample.lean",
    "Poincare/L4/DoublingToCovers/Consumption.lean",
    "Poincare/L4/DoublingToCovers/EuclideanWitness.lean",
    "Poincare/L4/DoublingToCovers/Sharpness.lean",
]
IMPORTED = [
    "Poincare/D12/GeometricCompactness/Basic.lean",
    "Poincare/D12/GeometricCompactness/Criterion.lean",
]
AUDIT = "Audit/L4C3AxiomAudit.lean"
PINS = ["lean-toolchain", "lake-manifest.json"]

MODULE_TARGETS = [
    "Poincare.L4.DoublingToCovers.Bridge",
    "Poincare.L4.DoublingToCovers.Counterexample",
    "Poincare.L4.DoublingToCovers.Consumption",
    "Poincare.L4.DoublingToCovers.EuclideanWitness",
    "Poincare.L4.DoublingToCovers.Sharpness",
]

FORBIDDEN = ["sorry", "axiom", "admit", "unsafe", "native_decide", "proof_wanted"]
FORBIDDEN_RE = re.compile(r"\b(" + "|".join(FORBIDDEN) + r")\b")
AXIOM_BLOCK_RE = re.compile(r"(?P<name>[\w.]+): axioms \[(?P<cones>[^\]]*)\]", re.S)


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def strip_lean_comments(text: str) -> str:
    """Remove nested block comments and line comments (strings are not modelled: the
    authored files contain no string literals with comment markers)."""
    out = []
    i, depth, n = 0, 0, len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        i += 1
    return "".join(out)


def run(cmd, log_name):
    env = dict(os.environ)
    env["ELAN_HOME"] = ELAN_HOME
    env["PATH"] = os.path.join(ELAN_HOME, "bin") + os.pathsep + env.get("PATH", "")
    proc = subprocess.run(
        cmd, cwd=RELEASE, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True,
    )
    log_path = os.path.join(EVIDENCE, log_name)
    with open(log_path, "w") as fh:
        fh.write("$ " + " ".join(cmd) + "\n")
        fh.write(proc.stdout)
        fh.write(f"\n[exit code: {proc.returncode}]\n")
    return proc.returncode, proc.stdout


def main() -> int:
    os.makedirs(EVIDENCE, exist_ok=True)
    summary = {
        "task_id": "L4-C3-doubling-to-covers",
        "ran_at": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "worktree": ROOT,
        "toolchain": open(os.path.join(RELEASE, "lean-toolchain")).read().strip(),
    }

    # 1. hashes
    hashes = {}
    for rel in AUTHORED + IMPORTED + [AUDIT] + PINS:
        hashes[rel] = sha256(os.path.join(RELEASE, rel))
    with open(os.path.join(EVIDENCE, "l4c3_source_hashes.json"), "w") as fh:
        json.dump(hashes, fh, indent=2, sort_keys=True)
    summary["source_hashes"] = hashes

    # 2. forbidden-token scan
    scan = {}
    for rel in AUTHORED:
        with open(os.path.join(RELEASE, rel)) as fh:
            code = strip_lean_comments(fh.read())
        hits = sorted(set(FORBIDDEN_RE.findall(code)))
        scan[rel] = hits
    with open(os.path.join(EVIDENCE, "l4c3_forbidden_token_scan.json"), "w") as fh:
        json.dump(scan, fh, indent=2, sort_keys=True)
    summary["forbidden_token_scan"] = scan

    # 3. builds
    builds = {}
    rc, _ = run(["lake", "build"] + MODULE_TARGETS, "l4c3-build-modules.log")
    builds["modules"] = rc
    rc, _ = run(["lake", "build"], "l4c3-build-package.log")
    builds["package_default_targets"] = rc
    summary["builds"] = builds

    # 4. axiom audit
    rc, out = run(["lake", "env", "lean", AUDIT], "l4c3-axiom-audit.log")
    cones = {}
    for m in AXIOM_BLOCK_RE.finditer(out):
        cones[m.group("name")] = [
            c.strip() for c in m.group("cones").replace("\n", " ").split(",") if c.strip()
        ]
    audit = {
        "exit_code": rc,
        "declarations_audited": len(cones),
        "cones": cones,
        "pass": rc == 0 and "PASS" in out,
        "approved_axioms": ["propext", "Classical.choice", "Quot.sound"],
    }
    with open(os.path.join(EVIDENCE, "l4c3-axiom-audit.json"), "w") as fh:
        json.dump(audit, fh, indent=2, sort_keys=True)
    summary["axiom_audit"] = {
        "exit_code": rc,
        "declarations_audited": len(cones),
        "distinct_cones": sorted({tuple(sorted(v)) for v in cones.values()}),
        "pass": audit["pass"],
    }

    # 5. negative control (pre-existing D5 artifact, not part of the release package)
    rc, out = run(["lake", "env", "lean", "../negcontrol/NegativeControl.lean"],
                  "l4c3-negative-control.log")
    summary["negative_control"] = {
        "exit_code": rc,
        "detected_sorry": "sorryAx" in out,
        "detected_unapproved_native_axiom": "unapproved axiom" in out,
        "pass": rc == 0 and "NegativeControl: PASS" in out,
    }

    with open(os.path.join(EVIDENCE, "l4c3-verify.json"), "w") as fh:
        json.dump(summary, fh, indent=2, sort_keys=True)

    print(json.dumps(summary, indent=2, sort_keys=True))
    ok = (
        all(v == 0 for v in builds.values())
        and all(not hits for hits in scan.values())
        and audit["pass"]
        and summary["negative_control"]["pass"]
    )
    print("L4C3 DRIVER:", "PASS" if ok else "FAIL")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
