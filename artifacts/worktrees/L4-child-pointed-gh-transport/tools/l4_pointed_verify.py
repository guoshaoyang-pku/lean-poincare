#!/usr/bin/env python3
"""Compile + provenance gate for task L4-child-pointed-gh-transport.

Runs, in order, recording exit codes and timings into
`manifest/l4-pointed-gh-verification.json`:

1. `lake build` in `release/` (all default targets, including every new
   `Poincare.L4.PointedGH.*` module through the `Poincare.+` glob).
2. Per-module builds of the four new modules.
3. The fail-closed axiom/source audit `tools/l4_pointed_axiom_audit.py`.
4. Provenance: every one of the 63 files recorded in the accepted
   `manifest/weekly-release-manifest.json` must be byte-identical (the task
   only *adds* modules), and the five consumed D12 modules must match the
   hashes recorded in the D12 result card.

Exit code 0 only if every gate exits 0 and provenance holds.

Usage (from the worktree root):
    python3 tools/l4_pointed_verify.py
"""
import hashlib
import json
import os
import subprocess
import sys
import time

WORKTREE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
RELEASE = os.path.join(WORKTREE, "release")

D12_SOURCES = {
    "Poincare/D12/GeometricCompactness/Basic.lean":
        "61b65b02a94ecc159cecbdba2e01bae8b2c7dc7aaa8844fb36099b60d94943e5",
    "Poincare/D12/GeometricCompactness/Criterion.lean":
        "aef17c6cb4911bdaba050d985e9e511a3bb0102eec4ac0cce08ea3888f38f7a7",
    "Poincare/D12/GeometricCompactness/GridFamily.lean":
        "c67bffe0d77fc8ab09da0a50cff5d8e55f8ffd793763d11a61459dbaf52d0f41",
    "Poincare/D12/GeometricCompactness/Frontier.lean":
        "63d64c02e6a4bf201ff26ee03013fc70292383a7129b74a2e490139e969869ef",
    "Poincare/D12/GeometricCompactness/AxiomAudit.lean":
        "112af468c973832c70efd2dbf8d4686ce5c1bc679f2a35fc88a847dc1cbd5e08",
}

NEW_SOURCES = [
    "Poincare/L4/PointedGH/Transport.lean",
    "Poincare/L4/PointedGH/Family.lean",
    "Poincare/L4/PointedGH/Instances.lean",
    "Poincare/L4/PointedGH/AxiomAudit.lean",
]

GATES = [
    ("lake_build_full", ["lake", "build"], RELEASE),
    ("build_transport", ["lake", "build", "Poincare.L4.PointedGH.Transport"], RELEASE),
    ("build_family", ["lake", "build", "Poincare.L4.PointedGH.Family"], RELEASE),
    ("build_instances", ["lake", "build", "Poincare.L4.PointedGH.Instances"], RELEASE),
    ("build_axiom_audit", ["lake", "build", "Poincare.L4.PointedGH.AxiomAudit"], RELEASE),
    ("fail_closed_audit", ["python3", "tools/l4_pointed_axiom_audit.py"], WORKTREE),
]


def sha256(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def main():
    report = {"schema": "l4-child-pointed-gh-transport/verification-v1",
              "worktree": WORKTREE, "gates": []}
    ok = True

    for name, cmd, cwd in GATES:
        t0 = time.time()
        proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
        dt = time.time() - t0
        entry = {
            "name": name,
            "command": " ".join(cmd),
            "cwd": os.path.relpath(cwd, WORKTREE),
            "exit": proc.returncode,
            "seconds": round(dt, 1),
            "stdout_tail": proc.stdout[-1500:],
            "stderr_tail": proc.stderr[-1500:],
        }
        report["gates"].append(entry)
        status = "OK" if proc.returncode == 0 else "FAIL"
        print(f"[{status}] {name}: exit {proc.returncode} ({dt:.1f}s)")
        if proc.returncode != 0:
            ok = False
            print(proc.stdout[-2000:])
            print(proc.stderr[-2000:])

    # provenance: accepted weekly-release files unchanged
    manifest = json.load(open(os.path.join(WORKTREE, "manifest", "weekly-release-manifest.json")))
    unchanged, changed, missing = 0, [], []
    for f in manifest["package"]["files"]:
        p = os.path.join(RELEASE, f["path"])
        if not os.path.exists(p):
            missing.append(f["path"])
        elif sha256(p) != f["sha256"]:
            changed.append(f["path"])
        else:
            unchanged += 1
    print(f"[{'OK' if not changed and not missing else 'FAIL'}] weekly-release files: "
          f"{unchanged} unchanged, {len(changed)} changed, {len(missing)} missing")
    if changed or missing:
        ok = False

    # provenance: consumed D12 sources match the D12 result-card hashes
    d12 = {rel: {"expected": exp, "actual": sha256(os.path.join(RELEASE, rel))}
           for rel, exp in D12_SOURCES.items()}
    d12_ok = all(v["expected"] == v["actual"] for v in d12.values())
    print(f"[{'OK' if d12_ok else 'FAIL'}] D12 consumed sources: "
          f"{sum(v['expected'] == v['actual'] for v in d12.values())}/{len(d12)} match D12 card")
    if not d12_ok:
        ok = False

    new_hashes = {rel: sha256(os.path.join(RELEASE, rel)) for rel in NEW_SOURCES}
    new_hashes["tools/l4_pointed_axiom_audit.py"] = sha256(
        os.path.join(WORKTREE, "tools", "l4_pointed_axiom_audit.py"))
    new_hashes["tools/l4_pointed_verify.py"] = sha256(
        os.path.join(WORKTREE, "tools", "l4_pointed_verify.py"))

    report["provenance"] = {
        "weekly_release_unchanged": unchanged,
        "weekly_release_changed": changed,
        "weekly_release_missing": missing,
        "d12_consumed": d12,
        "d12_ok": d12_ok,
        "new_source_hashes": new_hashes,
    }
    report["ok"] = ok
    out = os.path.join(WORKTREE, "manifest", "l4-pointed-gh-verification.json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        json.dump(report, f, indent=1)
    print(f"wrote {os.path.relpath(out, WORKTREE)}")
    print("[PASS] all compile/provenance gates passed" if ok else "[FAIL] gates failed")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
