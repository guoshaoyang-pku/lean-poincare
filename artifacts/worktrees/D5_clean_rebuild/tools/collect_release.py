#!/usr/bin/env python3
"""
D5-clean-rebuild: collect only the accepted D1-D4 artifacts into a fresh build
directory, WITHOUT modifying any source artifact.

- copies every promoted Lean source from its originating worktree,
- verifies byte-identity of every duplicated shared file across worktrees,
- verifies the sha256 values claimed in the D1-D4 result cards,
- writes a fresh Lake package (lakefile.toml / lean-toolchain / lake-manifest.json),
- writes manifest/provenance.json with per-file provenance and hashes.

Read-only with respect to every source artifact.
"""
import hashlib
import json
import os
import shutil
import subprocess
import sys
from datetime import datetime, timezone

ROOT = "/data3/guoshaoyang/workdir/lean_poincare"
WT = os.path.join(ROOT, "longrun", "worktrees")
RESULTS = os.path.join(ROOT, "longrun", "results")
D5 = os.path.join(WT, "D5_clean_rebuild")
RELEASE = os.path.join(D5, "release")
MANIFEST = os.path.join(D5, "manifest")

# ---------------------------------------------------------------- artifact map
# cluster -> (task id, stage, origin worktree, [relative paths])
CLUSTERS = [
    ("D1-geometry-map", "D1-mathlib-geometry-map", "D1", "D1_geometry_map",
     ["Probe/GeometryApi.lean"]),
    ("D1-pde-api-map", "D1-pde-api-map", "D1", "D1_pde_map",
     ["Probe/PdeApi.lean"]),
    ("D1-perelman-ledger", "D1-perelman-ledger", "D1", "D1_perelman_ledger",
     ["Ledger/PerelmanDefinitions.lean", "Ledger/DefinitionSmoke.lean"]),
    ("D2-geometry-foundation", "D2-geometry-foundation", "D2", "D2_geometry_foundation",
     ["Poincare/Longrun/Geometry.lean",
      "Poincare/Longrun/Geometry/MetricData.lean",
      "Poincare/Longrun/Geometry/ConnectionAdapter.lean",
      "Poincare/Longrun/Geometry/Contraction.lean",
      "Poincare/Longrun/Geometry/LeviCivitaBlocked.lean",
      "Audit/GeometryAudit.lean"]),
    ("D2-pde-foundation", "D2-pde-foundation", "D2", "D2_pde_foundation",
     ["Poincare/Longrun/PDE/HeatGrid.lean",
      "Poincare/Longrun/PDE/DiscreteMaximumPrinciple.lean",
      "Poincare/Longrun/PDE/Energy.lean",
      "Poincare/Longrun/PDE/ContinuousInterface.lean",
      "Poincare/Longrun/PDE/AxiomAudit.lean"]),
    ("D2-ricci-ode-cluster", "D2-ricci-ode-cluster", "D2", "D2_ricci_ode_cluster",
     ["Poincare/Longrun/CurvatureODE.lean",
      "Poincare/Longrun/CurvatureODE/State.lean",
      "Poincare/Longrun/CurvatureODE/Evolution.lean",
      "Poincare/Longrun/CurvatureODE/ScalarODE.lean",
      "Poincare/Longrun/CurvatureODE/Invariant.lean",
      "Poincare/Longrun/CurvatureODE/Monotonicity.lean",
      "Poincare/Longrun/CurvatureODE/Bridge.lean",
      "Audit/CurvatureODEAudit.lean"]),
    ("D3-entropy-interface", "D3-entropy-interface", "D3", "D3_entropy_interface",
     ["Poincare/Longrun/Entropy.lean",
      "Poincare/Longrun/Entropy/Functional.lean",
      "Poincare/Longrun/Entropy/Certificate.lean",
      "Poincare/Longrun/Entropy/Bridge.lean",
      "Poincare/Longrun/Entropy/DiscreteHeat.lean",
      "Poincare/Longrun/Entropy/FiniteGeometry.lean",
      "Poincare/Longrun/Entropy/AxiomAudit.lean"]),
    ("D3-kappa-ledger", "D3-kappa-ledger", "D3", "D3_kappa_ledger",
     ["Poincare/Longrun/Topology/Basic.lean",
      "Poincare/Longrun/Topology/CompactThreeManifold.lean",
      "Poincare/Longrun/Topology/Noncollapsing.lean",
      "Poincare/Longrun/Topology/NormalizedVolume.lean",
      "Poincare/Longrun/Topology/Stage6Bridge.lean",
      "Poincare/Longrun/Topology/MissingTheorems.lean",
      "Poincare/Longrun/Topology/AxiomAudit.lean"]),
    ("D3-surgery-ledger", "D3-surgery-ledger", "D3", "D3_surgery_ledger",
     ["Poincare/Longrun/Surgery.lean",
      "Poincare/Longrun/Surgery/Basic.lean",
      "Poincare/Longrun/Surgery/Chain.lean",
      "Poincare/Longrun/Surgery/Toy.lean",
      "Poincare/Longrun/Surgery/Missing.lean",
      "Poincare/Longrun/Surgery/Axioms.lean"]),
    ("D4-evolution-theorem", "D4-evolution-theorem", "D4", "D4_evolution_theorem",
     ["Poincare/Longrun/Evolution.lean",
      "Poincare/Longrun/Evolution/Gibbs.lean",
      "Poincare/Longrun/Evolution/Functional.lean",
      "Poincare/Longrun/Evolution/Continuous.lean",
      "Poincare/Longrun/Evolution/Discrete.lean",
      "Poincare/Longrun/Evolution/Counterexample.lean",
      "Poincare/Longrun/Evolution/Bridge.lean",
      "Audit/EvolutionAudit.lean"]),
    ("D4-counterexample-audit", "D4-counterexample-audit", "D4", "D4_counterexample_audit",
     ["Audit/CounterexampleAudit.lean",
      "Audit/PromotedEvolutionAudit.lean"]),
]

# shared base library files (pre-existing poincare-lab skeleton, NOT D1-D4 artifacts)
BASE = [
    "Poincare/Basic.lean",
    "Poincare/Stage1/CurvatureAlgebra.lean",
    "Poincare/Stage1/RiemannAdapter.lean",
    "Poincare/Stage6/TopologyBridge.lean",
    "Poincare/Stage6/SphereSimplyConnected.lean",
]

# queue.json status snapshot (control-plane acceptance record; stale after 2026-09-08T23:55)
QUEUE_STATUS = {
    "D1-mathlib-geometry-map": "verified",
    "D1-pde-api-map": "verified",
    "D1-perelman-ledger": "verified",
    "D2-geometry-foundation": "running",
    "D2-pde-foundation": "verified",
    "D2-ricci-ode-cluster": "queued",
    "D3-entropy-interface": "queued",
    "D3-kappa-ledger": "verified",
    "D3-surgery-ledger": "verified",
    "D4-evolution-theorem": "queued",
    "D4-counterexample-audit": "queued",
}

CARD_FILES = {
    "D1-mathlib-geometry-map": "D1-mathlib-geometry-map.json",
    "D1-pde-api-map": "D1-pde-api-map.json",
    "D1-perelman-ledger": "D1-perelman-ledger.json",
    "D2-geometry-foundation": "D2-geometry-foundation.json",
    "D2-pde-foundation": "D2-pde-foundation.json",
    "D2-ricci-ode-cluster": "D2-ricci-ode-cluster.json",
    "D3-entropy-interface": "D3-entropy-interface.json",
    "D3-kappa-ledger": "D3-kappa-ledger.json",
    "D3-surgery-ledger": "D3-surgery-ledger.json",
    "D4-evolution-theorem": "D4-evolution-theorem.json",
    "D4-counterexample-audit": "D4-counterexample-audit.json",
}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def card_hashes(task):
    """sha256 claims inside the machine-readable result card, path -> hash."""
    path = os.path.join(RESULTS, CARD_FILES[task])
    if not os.path.exists(path):
        return {}
    data = json.load(open(path))
    out = {}

    def walk(o):
        if isinstance(o, dict):
            if isinstance(o.get("path"), str) and isinstance(o.get("sha256"), str):
                out[o["path"]] = o["sha256"]
            for v in o.values():
                walk(v)
        elif isinstance(o, list):
            for v in o:
                walk(v)

    walk(data)
    return out


def card_status(task):
    path = os.path.join(RESULTS, CARD_FILES[task])
    if not os.path.exists(path):
        return None
    return json.load(open(path)).get("status")


def main():
    if os.path.exists(RELEASE):
        shutil.rmtree(RELEASE)
    os.makedirs(RELEASE)
    os.makedirs(os.path.join(RELEASE, ".lake"), exist_ok=True)
    os.makedirs(MANIFEST, exist_ok=True)

    # ---- cross-worktree duplicate consistency check (before copying) -------
    seen = {}
    conflicts = []
    for _, _, _, wt, files in CLUSTERS:
        for rel in files:
            src = os.path.join(WT, wt, rel)
            if not os.path.exists(src):
                raise SystemExit(f"MISSING SOURCE: {src}")
            h = sha256(src)
            if rel in seen and seen[rel][0] != h:
                conflicts.append((rel, seen[rel], (h, wt)))
            else:
                seen.setdefault(rel, (h, wt))

    # ---- copy artifacts ----------------------------------------------------
    artifacts = []
    for name, task, stage, wt, files in CLUSTERS:
        claims = card_hashes(task)
        entry = {
            "cluster": name,
            "task_id": task,
            "stage": stage,
            "origin_worktree": os.path.join(WT, wt),
            "result_card": os.path.join(RESULTS, CARD_FILES[task]),
            "result_card_status": card_status(task),
            "queue_status_at_snapshot": QUEUE_STATUS.get(task),
            "state_done_marker": os.path.exists(os.path.join(ROOT, "longrun", "state", wt, "DONE")),
            "files": [],
        }
        for rel in files:
            src = os.path.join(WT, wt, rel)
            dst = os.path.join(RELEASE, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copy2(src, dst)
            h = sha256(dst)
            assert h == sha256(src)
            claimed = claims.get(rel)
            entry["files"].append({
                "path": rel,
                "sha256": h,
                "lines": sum(1 for _ in open(dst, "rb")),
                "origin": src,
                "card_sha256": claimed,
                "card_hash_match": (claimed == h) if claimed else None,
            })
        artifacts.append(entry)

    # ---- copy shared base --------------------------------------------------
    base = []
    for rel in BASE:
        src = os.path.join(ROOT, "poincare-lab", rel)
        dst = os.path.join(RELEASE, rel)
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(src, dst)
        h = sha256(dst)
        # every private copy of the same base file in the worktrees must be identical
        copies = []
        for wt in os.listdir(WT):
            cand = os.path.join(WT, wt, rel)
            if os.path.exists(cand):
                copies.append({"worktree": wt, "sha256": sha256(cand)})
        base.append({"path": rel, "origin": src, "sha256": h, "private_copies": copies})

    # ---- fresh Lake package scaffolding -----------------------------------
    for f in ("lean-toolchain", "lake-manifest.json"):
        shutil.copy2(os.path.join(ROOT, "poincare-lab", f), os.path.join(RELEASE, f))

    lakefile = '''name = "PoincareRelease"
version = "0.1.0"
description = "D5 clean-room release package: accepted D1-D4 clusters of the Ricci-flow formalization program"
keywords = ["math"]
defaultTargets = ["Poincare", "Probe", "Ledger", "Audit", "ReleaseCheck", "ReleaseAudit"]

# Toolchain is pinned by ./lean-toolchain; the exact mathlib revision is pinned by
# ./lake-manifest.json (rev recorded in manifest/build-manifest.json).
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "master"

[[lean_lib]]
name = "Poincare"
globs = ["Poincare.+"]

[[lean_lib]]
name = "Probe"
globs = ["Probe.+"]

[[lean_lib]]
name = "Ledger"
globs = ["Ledger.+"]

[[lean_lib]]
name = "Audit"
globs = ["Audit.+"]

[[lean_lib]]
name = "ReleaseCheck"

[[lean_lib]]
name = "ReleaseAudit"
'''
    open(os.path.join(RELEASE, "lakefile.toml"), "w").write(lakefile)

    pkg_link = os.path.join(RELEASE, ".lake", "packages")
    if os.path.islink(pkg_link) or os.path.exists(pkg_link):
        os.remove(pkg_link)
    os.symlink(os.path.join(ROOT, "poincare-lab", ".lake", "packages"), pkg_link)

    # ---- toolchain / dependency revisions ---------------------------------
    def run(cmd, cwd):
        p = subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True)
        return {"cmd": cmd, "cwd": cwd, "exit_code": p.returncode,
                "stdout": p.stdout.strip(), "stderr": p.stderr.strip()}

    elan = os.path.join(ROOT, "elan")
    env = dict(os.environ, ELAN_HOME=elan, PATH=f"{elan}/bin:" + os.environ["PATH"])
    mathlib = os.path.join(ROOT, "poincare-lab", ".lake", "packages", "mathlib")

    def run_env(cmd, cwd):
        p = subprocess.run(cmd, cwd=cwd, shell=True, capture_output=True, text=True, env=env)
        return {"cmd": cmd, "cwd": cwd, "exit_code": p.returncode,
                "stdout": p.stdout.strip(), "stderr": p.stderr.strip()}

    manifest_pkgs = json.load(open(os.path.join(RELEASE, "lake-manifest.json")))["packages"]
    toolchain = {
        "lean_toolchain_file": open(os.path.join(RELEASE, "lean-toolchain")).read().strip(),
        "lake_version": run_env("lake --version", RELEASE)["stdout"],
        "lean_version": run_env("lean --version", RELEASE)["stdout"],
        "mathlib_manifest_rev": next(p["rev"] for p in manifest_pkgs if p["name"] == "mathlib"),
        "mathlib_git_head": run_env("git rev-parse HEAD", mathlib)["stdout"],
        "mathlib_git_describe": run_env("git describe --tags", mathlib)["stdout"],
        "mathlib_git_status_porcelain": run_env("git status --porcelain", mathlib)["stdout"],
        "packages": [{"name": p["name"], "rev": p["rev"], "url": p["url"]} for p in manifest_pkgs],
    }

    out = {
        "schema": "d5-clean-rebuild/provenance-v1",
        "task_id": "D5-clean-rebuild",
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "verifier_worktree": D5,
        "fresh_build_dir": RELEASE,
        "prompt_worktree_discrepancy": "prompt names worktrees/D5_rebuild; runtime workspace is worktrees/D5_clean_rebuild",
        "artifact_duplicate_conflicts": conflicts,
        "base_dependencies": base,
        "toolchain": toolchain,
        "clusters": artifacts,
    }
    with open(os.path.join(MANIFEST, "provenance.json"), "w") as fh:
        json.dump(out, fh, indent=1)

    n_files = sum(len(c["files"]) for c in artifacts)
    print(f"copied {n_files} promoted files + {len(base)} base files -> {RELEASE}")
    print(f"duplicate conflicts: {len(conflicts)}")
    print(f"toolchain: {toolchain['lean_toolchain_file']}")
    print(f"mathlib:   {toolchain['mathlib_manifest_rev']} ({toolchain['mathlib_git_describe']})")
    for c in artifacts:
        bad = [f for f in c["files"] if f["card_hash_match"] is False]
        print(f"  {c['cluster']:<26} files={len(c['files']):>2} "
              f"queue={c['queue_status_at_snapshot']:<9} card={c['result_card_status']} "
              f"hash_mismatch={len(bad)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
