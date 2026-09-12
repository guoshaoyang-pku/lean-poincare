#!/usr/bin/env python3
"""SEMREV-L3 round-4 evidence hash manifest.

Hashes every artifact this invocation relies on: the parent revision, the staged
byte-identical copy, the six consumed snapshot sources, and all round-4 reviewer
evidence (probe sources, logs, gate JSONs, tools). Writes evidence/evidence-hashes.r4.txt.
"""
import hashlib
import subprocess
from pathlib import Path

WT = Path(__file__).resolve().parent.parent.parent          # review worktree root
REVIEW = WT / "review"
PARENT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/leaders/L3-analytic-critical-path")


def sha(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


rows = []


def add(label: str, path: Path):
    if path.exists():
        rows.append((sha(path), label))
    else:
        rows.append(("MISSING", label))


def section(title: str):
    rows.append((None, f"== {title} =="))


section("review artifacts (round 4)")
for rel in ["checkpoint.json",
            "longrun/results/SEMREV-L3-analytic-critical-path.md",
            "longrun/results/SEMREV-L3-analytic-critical-path.json"]:
    add(rel, WT / rel)

section("reviewed parent artifact (round 2, re-hashed byte-identical in rounds 3 and 4)")
add("parent:longrun/results/L3-analytic-critical-path.md", PARENT / "longrun/results/L3-analytic-critical-path.md")
add("parent:longrun/results/L3-analytic-critical-path.json", PARENT / "longrun/results/L3-analytic-critical-path.json")
add("parent:checkpoint.json", PARENT / "checkpoint.json")
add("parent:audit-evidence/authored-hashes.txt", PARENT / "audit-evidence/authored-hashes.txt")

section("staged copy pins and authored L3 files")
for rel in ["release/lean-toolchain", "release/lake-manifest.json", "release/lakefile.toml"]:
    add(rel, REVIEW / rel)
for f in ["All", "Audit", "BanachDeriv", "Basic", "ClassicalBridge", "UniformBridge"]:
    add(f"release/Poincare/L3/HeatTimeDeriv/{f}.lean",
        REVIEW / f"release/Poincare/L3/HeatTimeDeriv/{f}.lean")

section("consumed snapshot sources (staged package)")
for rel in ["Poincare/D12/ParabolicLocal/Obligations.lean",
            "Poincare/D12/ParabolicLocal/GaussianConv.lean",
            "Poincare/D12/ParabolicLocal/GaussianSemigroup.lean",
            "Poincare/D10/HeatKernelEuclidean/HeatEquation.lean",
            "Poincare/D12/HeatSemigroup/StrongContinuityL1.lean",
            "Poincare/D12/HeatSemigroup/Basic.lean"]:
    add(f"release/{rel}", REVIEW / "release" / rel)

section("D13 blocker ledger (U6/U8/U12 records re-read in round 4)")
add("D13-critical-path-review/manifest/blockers.json",
    Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-critical-path-review/manifest/blockers.json"))

section("round-4 Lean probes (reviewer instrumentation)")
for f in sorted((REVIEW / "probe").glob("*.lean")):
    add(f"probe/{f.name}", f)
for f in sorted((REVIEW / "negcontrol").glob("*.lean")):
    add(f"negcontrol/{f.name}", f)

section("round-4 evidence logs and gate JSON")
for f in sorted((REVIEW / "evidence").glob("r4-*")):
    add(f"evidence/{f.name}", f)
add("evidence/semrev-forbidden-scan.r4.json", REVIEW / "evidence/semrev-forbidden-scan.r4.json")
add("evidence/semrev-evidence.json", REVIEW / "evidence/semrev-evidence.json")
add("audit-evidence/l3-check.r4.json", REVIEW / "audit-evidence/l3-check.r4.json")

section("round-4 tooling")
add("tools/round4_verify.sh", REVIEW / "tools/round4_verify.sh")
add("tools/round4_evidence_hashes.py", REVIEW / "tools/round4_evidence_hashes.py")
add("tools/l3_check_parent.py", REVIEW / "tools/l3_check_parent.py")
add("tools/semrev_check.py", REVIEW / "tools/semrev_check.py")
add("parent-authored-hashes.txt", REVIEW / "parent-authored-hashes.txt")

out = REVIEW / "evidence" / "evidence-hashes.r4.txt"
with open(out, "w") as f:
    for h, label in rows:
        if h is None:
            f.write(f"\n{label}\n")
        else:
            f.write(f"{h}  {label}\n")

n = sum(1 for h, _ in rows if h is not None)
miss = [l for h, l in rows if h == "MISSING"]
print(f"wrote {out} with {n} hash rows; missing={len(miss)}")
for m in miss:
    print("MISSING:", m)
raise SystemExit(1 if miss else 0)
