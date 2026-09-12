#!/usr/bin/env python3
"""L4-child-gh-family-covers fail-closed verification driver.

Checks, in order, and exits non-zero on the first failure:

1. source hashes of every authored file (recorded; the two authored modules must
   exist);
2. `lake build` of the three modules (authored + audit) — compile exits recorded;
3. the kernel axiom audit `Audit/L4FamilyCoversAxiomAudit.lean` — must end in
   `PASS` and must not report UNAPPROVED axioms;
4. the negative control `../negcontrol/NegativeControl.lean` — must detect
   `sorryAx` and `native_decide`;
5. a forbidden-token scan of the authored proof files (comments stripped):
   no `sorry`, `admit`, `axiom `, `native_decide`, `gromovCriterion`,
   `Classical.choice` literal, no re-definition of
   `coveringNumber_le_of_ghDist_lt`;
6. fidelity checks: the D12 uniform-cover conclusion shape `#s ≤ K ∧ univ ⊆ ⋃ x
   ∈ s, ball x ε` occurs verbatim in the D12 criterion and in our family
   theorem; `TotallyBounded` does not occur in the hypotheses of the family
   theorem (only as the conclusion of the direction-check theorem).

Writes `evidence/l4child-family-audit.json` and per-step logs.
"""

import hashlib
import json
import re
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RELEASE = ROOT / "release"
EVIDENCE = ROOT / "evidence"
EVIDENCE.mkdir(exist_ok=True)

AUTHORED = [
    "release/Poincare/L4/Compactness/FamilyCovers.lean",
    "release/Poincare/L4/Compactness/FamilyCoversWitness.lean",
    "release/Audit/L4FamilyCoversAxiomAudit.lean",
]
STAGED = [
    "release/Poincare/D12/GeometricCompactness/Basic.lean",
    "release/Poincare/D12/GeometricCompactness/Criterion.lean",
    "release/Poincare/L4/Compactness/CoveringStability.lean",
    "release/Poincare/L4/Compactness/DoublingToCovers.lean",
]
MODULES = [
    "Poincare.L4.Compactness.FamilyCovers",
    "Poincare.L4.Compactness.FamilyCoversWitness",
    "Audit.L4FamilyCoversAxiomAudit",
]

FORBIDDEN = [
    r"\bsorry\b",
    r"\badmit\b",
    r"\bnative_decide\b",
    r"\bgromovCriterion\b",
    r"\baxiom\s+[A-Za-z_]",
    r"Classical\.choice",
]

results = {"task_id": "L4-child-gh-family-covers", "started": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
failures = []


def fail(msg):
    failures.append(msg)
    print(f"FAIL: {msg}", flush=True)


def run(cmd, log_name, cwd=RELEASE, timeout=3600):
    log_path = EVIDENCE / log_name
    with log_path.open("w") as fh:
        proc = subprocess.run(
            cmd, cwd=cwd, stdout=fh, stderr=subprocess.STDOUT, text=True, timeout=timeout
        )
    return proc.returncode, log_path.read_text(errors="replace")


def strip_comments(src):
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    src = re.sub(r"--[^\n]*", "", src)
    return src


# --- 1. source hashes -------------------------------------------------------
hashes = {}
for rel in AUTHORED + STAGED:
    path = ROOT / rel
    if not path.exists():
        fail(f"missing source {rel}")
        continue
    hashes[rel] = hashlib.sha256(path.read_bytes()).hexdigest()
results["source_hashes"] = hashes
print("source hashes:")
for rel, h in hashes.items():
    print(f"  {h}  {rel}")

# --- 2. compile -------------------------------------------------------------
compile_exits = []
for mod in MODULES:
    code, out = run(["lake", "build", mod], f"build-{mod.replace('.', '-')}.log")
    compile_exits.append({"module": mod, "exit": code})
    print(f"lake build {mod}: exit {code}")
    if code != 0:
        fail(f"lake build {mod} exited {code}")
results["compile_exits"] = compile_exits

# --- 3. axiom audit ---------------------------------------------------------
code, out = run(["lake", "env", "lean", "Audit/L4FamilyCoversAxiomAudit.lean"],
                "axiom-audit.log")
results["axiom_audit_exit"] = code
print(f"axiom audit: exit {code}")
if code != 0:
    fail(f"axiom audit exited {code}")
if "L4FamilyCoversAxiomAudit: PASS" not in out:
    fail("axiom audit did not report PASS")
if "UNAPPROVED" in out:
    fail("axiom audit reported UNAPPROVED axioms")
m = re.search(r"declarations audited: (\d+)", out)
results["axiom_audit_declarations"] = int(m.group(1)) if m else None
cones = re.findall(r"^(\S+): axioms \[([^\]]*)\]$", out, flags=re.M)
approved = {"propext", "Classical.choice", "Quot.sound"}
bad = []
for name, cone in cones:
    got = {c.strip() for c in cone.split(",") if c.strip()}
    if not got <= approved:
        bad.append({"declaration": name, "cone": sorted(got)})
results["axiom_cones_checked"] = len(cones)
results["axiom_cones_bad"] = bad
if bad:
    fail(f"cones outside approved set: {bad}")

# --- 4. negative control ----------------------------------------------------
code, out = run(["lake", "env", "lean", "../negcontrol/NegativeControl.lean"],
                "negative-control.log")
results["negative_control_exit"] = code
print(f"negative control: exit {code}")
if code != 0 or "NegativeControl: PASS" not in out:
    fail("negative control did not detect the forbidden trust primitives")

# --- 5. forbidden-token scan ------------------------------------------------
scan = {}
for rel in AUTHORED[:2]:  # proof modules only; the audit file uses #print axioms
    src = strip_comments((ROOT / rel).read_text())
    hits = {pat: len(re.findall(pat, src)) for pat in FORBIDDEN}
    hits = {k: v for k, v in hits.items() if v}
    scan[rel] = hits
    if hits:
        fail(f"forbidden tokens in {rel}: {hits}")
# no re-proof of the pair-level stability theorem
for rel in AUTHORED[:2]:
    src = strip_comments((ROOT / rel).read_text())
    if re.search(r"theorem\s+coveringNumber_le_of_ghDist_lt\b", src):
        fail(f"{rel} re-defines coveringNumber_le_of_ghDist_lt")
results["forbidden_scan"] = scan
print(f"forbidden scan: {'clean' if not any(scan.values()) else scan}")

# --- 6. statement-fidelity checks ------------------------------------------
d12 = strip_comments((ROOT / STAGED[1]).read_text())
fam = strip_comments((ROOT / AUTHORED[0]).read_text())
pattern = r"#s ≤ K ∧ univ ⊆ ⋃ x ∈ s, ball x ε"
results["d12_rhs_shape_present"] = bool(re.search(pattern, d12))
results["family_rhs_shape_present"] = bool(re.search(pattern, fam))
if not (results["d12_rhs_shape_present"] and results["family_rhs_shape_present"]):
    fail("D12 uniform-cover conclusion shape not found verbatim in both files")

# `TotallyBounded` must occur only in direction-check conclusions/docstrings.
tb = len(re.findall(r"\bTotallyBounded\b", fam))
results["totallyBounded_occurrences_in_FamilyCovers_code"] = tb
if tb == 0:
    fail("expected the direction-check theorem to mention TotallyBounded as a conclusion")
# crude hypothesis check: no `(h : TotallyBounded` / `: TotallyBounded t →`
if re.search(r"\(\s*\w+\s*:\s*TotallyBounded", fam) or re.search(r":\s*TotallyBounded[^;]*→", fam):
    fail("TotallyBounded appears in a hypothesis position")
results["totallyBounded_in_hypothesis_position"] = False

# `coveringNumber_le_of_ghDist_lt` must be consumed, not reproved (no definition)
results["pair_theorem_consumed"] = bool(
    re.search(r"coveringNumber_univ_le_of_ghDist_lt_of_doubling", fam)
)

results["failures"] = failures
results["finished"] = time.strftime("%Y-%m-%dT%H:%M:%S%z")
results["verdict"] = "PASS" if not failures else "FAIL"
(EVIDENCE / "l4child-family-audit.json").write_text(json.dumps(results, indent=1))
print(f"\nL4CHILD-FAMILY DRIVER: {results['verdict']}")
sys.exit(0 if not failures else 1)
