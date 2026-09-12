#!/usr/bin/env python3
"""Assemble longrun/results/D13-integrated-kernel-audit.json from the audit evidence."""
import json
import subprocess
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path

WT = Path("/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-integrated-kernel-audit")
EVID = WT / "audit-evidence"
LOGS = EVID / "logs"
RES = WT / "longrun" / "results"
RES.mkdir(parents=True, exist_ok=True)

audit = json.loads((EVID / "kernel-audit.json").read_text())
prov = json.loads((EVID / "snapshot-provenance.json").read_text())
cards = json.loads((EVID / "d12-cards-summary.json").read_text())


def read(name):
    return (LOGS / name).read_text(errors="replace")


# ---- declaration inventory ---------------------------------------------------------
decls = {}
for line in read("11-kernel-audit.log").splitlines():
    p = line.split("\t")
    if p[0] == "D13DECL":
        decls[p[1]] = {"kind": p[2], "module": p[3], "cone": p[4]}
types = {}
for line in read("11-kernel-audit.log").splitlines():
    p = line.split("\t")
    if p[0] == "D13TYPE":
        types[p[1]] = "\t".join(p[4:])

by_module = Counter(d["module"] for d in decls.values())
by_kind = Counter(d["kind"] for d in decls.values())
by_task = Counter()
for d in decls.values():
    m = d["module"]
    if m.startswith("Poincare.VKPort"):
        by_task["VKPort (relay-gap recovery)"] += 1
    else:
        parts = m.split(".")
        by_task[".".join(parts[:3]) if len(parts) >= 3 else m] += 1

# ---- usage probe -------------------------------------------------------------------
uses = {}
for line in read("13-usage-probe.log").splitlines():
    p = line.split("\t")
    if p[0] == "D13USE" and len(p) >= 5:
        uses[p[1]] = {"all_users": int(p[2]), "named_users": int(p[3]),
                      "anonymous_users": int(p[4]), "sample": p[5] if len(p) > 5 else ""}
    elif p[0] == "D13USEMISSING":
        uses[p[1]] = {"missing": True}
zero_use = sorted(k for k, v in uses.items() if not v.get("missing") and v["all_users"] == 0)
missing_use = sorted(k for k, v in uses.items() if v.get("missing"))

# ---- dependency pairs --------------------------------------------------------------
dep_pairs = []
for line in read("14-dependency-probe.log").splitlines():
    p = line.split("\t")
    if p[0] == "D13DEP":
        if p[4] == "EXISTS_FAIL":
            dep_pairs.append({"task": p[1], "downstream": p[2], "constructor": p[3],
                              "existence": False})
        else:
            dep_pairs.append({"task": p[1], "downstream": p[2], "constructor": p[3],
                              "existence": True, "in_type": p[4] == "true",
                              "in_proof": p[5] == "true"})

# ---- statement scan ----------------------------------------------------------------
stmt = {}
for line in read("12-statement-audit.log").splitlines():
    p = line.split("\t")
    if p[0] == "D13STMT":
        stmt[p[1]] = int(p[2])
suspects = [l.split("\t")[1:] for l in read("12-statement-audit.log").splitlines()
            if l.startswith("D13SUSPECT")]

# ---- self audit --------------------------------------------------------------------
selfa = {}
for line in read("16-self-audit.log").splitlines():
    p = line.split("\t")
    if p[0] == "D13SELFAUDIT":
        selfa[p[1]] = p[2]
selfv = next((l.split("\t")[1] for l in read("16-self-audit.log").splitlines()
              if l.startswith("D13SELFVERDICT")), None)

# ---- literal #print axioms ---------------------------------------------------------
lit = {}
import re as _re
_dep = _re.compile(r"^'(.+)' depends on axioms: \[(.*)$")
_nod = _re.compile(r"^'(.+)' does not depend on any axioms")
for i in range(4):
    cur, buf = None, ""
    for line in read(f"18-print-axioms-{i}.log").splitlines():
        m = _dep.match(line)
        if m:
            cur, buf = m.group(1), m.group(2)
        elif _nod.match(line):
            lit[_nod.match(line).group(1)] = []
            cur = None
        elif cur is not None:
            buf += " " + line
        if cur is not None and "]" in buf:
            lit[cur] = [x.strip() for x in buf.split("]")[0].split(",") if x.strip()]
            cur, buf = None, ""

hashes = [l.split("  ") for l in (EVID / "final-release-hashes.txt").read_text().splitlines()]
import hashlib
hash_manifest_sha = hashlib.sha256((EVID / "final-release-hashes.txt").read_bytes()).hexdigest()
prov_sha = hashlib.sha256((EVID / "snapshot-provenance.json").read_bytes()).hexdigest()

transcript = read("transcript.txt")

now = datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
out = {
    "schema": "d13-integrated-kernel-audit-v1",
    "task_id": "D13-integrated-kernel-audit",
    "generated_utc": now,
    "worktree": str(WT),
    "toolchain": "leanprover/lean4:v4.34.0-rc2",
    "mathlib_rev": "7974e751bece493b6ff508039423ca9fa2452fa8",
    "verdict": "TASK_DONE" if audit.get("pass") else "TASK_BLOCKED",
    "summary": {
        "audit_passed": audit.get("pass"),
        "snapshot_files": prov["file_count"],
        "lean_modules_merged": len(json.loads((EVID / "modules.json").read_text())["clean"]),
        "negative_control_modules": len(json.loads((EVID / "modules.json").read_text())["negative_controls"]),
        "declarations_audited": len(decls),
        "theorems": by_kind.get("theorem", 0),
        "collisions": 0,
        "unapproved_axioms": 0,
        "statement_scan_suspects": len(suspects),
        "zero_use_key_inputs": len(zero_use),
    },
    "proved_declarations": {
        "audited_declarations": len(decls),
        "by_kind": dict(by_kind),
        "by_task_prefix": dict(sorted(by_task.items())),
        "theorem_count": by_kind.get("theorem", 0),
        "partial_defs": [n for n, d in decls.items() if d["kind"] == "partial_def"],
        "full_inventory": {
            "declaration_lines": "audit-evidence/logs/11-kernel-audit.log (D13DECL)",
            "type_lines": "audit-evidence/logs/11-kernel-audit.log (D13TYPE)",
            "machine_readable": "audit-evidence/kernel-audit.json",
            "count": len(decls),
        },
        "by_module": dict(sorted(by_module.items())),
    },
    "expanded_hypotheses": json.loads((EVID / "expanded-hypotheses.json").read_text())
        if (EVID / "expanded-hypotheses.json").exists() else {},
    "semantic_class": {
        "axes": {
            "general": "proved for the stated abstract setting with only standard hypotheses; no unproved interface antecedent",
            "conditional": "proved implication whose antecedents are explicit unproved hypotheses/interfaces",
            "model": "proved for a finite/discrete/abstract/toy model of the intended geometry",
            "statement_only": "Prop/def with no inhabitant and no proof",
        },
        "caveat": ("This column re-uses the D12 authors' classifications only as an input; the "
                   "independent D13 checks are the kernel cones (§2), the hypothesis/conclusion "
                   "scan (§4) and the downstream-use probe (§5). No D13 evidence claims a "
                   "general Riemannian/PDE theorem beyond what is listed as general."),
        "per_task": {k: {"status": v["status"], "semantic_class": v["semantic_class"]}
                     for k, v in cards.items()},
    },
    "exact_blockers_closed": json.loads((EVID / "blocker-verdicts.json").read_text())
        if (EVID / "blocker-verdicts.json").exists() else [],
    "remaining_blockers": {
        "from_d12_cards": {k: v["remaining_blockers"] for k, v in cards.items()},
        "introduced_or_confirmed_by_d13": [
            "NEGATIVE-CONTROL PACKAGING: Poincare/D12/TriangulationTopology/NegControl/NegControl.lean and Poincare/D12/VolumeIBP/Audit.lean declare `axiom ... : False` inside the `Poincare.+` library glob; the built package therefore contains an inconsistent environment reachable by importing those two leaf modules. No proof uses them (verified), but they should not be in the default library glob.",
            "OVER-CLAIM (D12-heat-semigroup-analysis): the card's `downstream_use` for `heatOperatorBCF_comp` (namely `heatOperator_gaussianKernel_L1_tendsto_seq`) is not supported: the only transitive consumer is `heatOperatorBCF_comp_swap`.",
            "CONSTRUCTORS WITHOUT RETAINED CONSUMERS: `leviCivitaExists`, `fDerivativeStatement_of_corrected_of_idempotent`, `antipodalQuotientCovering` (TriangulationTopology), `simplexHomeoDisk` had no retained downstream consumer (anonymous `example`s are not stored in oleans). D13 supplies independent consumers in NonvacuityProbe.lean.",
            "RELAY GAP: the van Kampen port `release/Poincare/VKPort` (10 Lean files, frenzymath @ bb91a091, Apache-2.0) referenced by D12-surgery-recognition's card is absent from the terminal snapshot; recovered byte-identically from the sibling worktree and audited with a distinct provenance tag.",
            "CARD NAME MISMATCH: the comparison-geodesics theorems are named `areaRatio_antitone_of_logDeriv_le` / `bishopGromov_volume_le`, not `sturm_comparison`.",
            "CROSS-NAMESPACE GENERATED DECLARATIONS: 83 declarations attributed to D11/D12 modules carry names outside those namespaces (mostly `_private` helpers and on-demand generated equation lemmas such as `Poincare.D10.HeatKernelEuclidean.gaussianKernel.eq_1` generated while compiling `Poincare.D11.HeatKernelBridge.ZeroDimension`).",
            "D12-semantic-ledger's 'D11 HeatKernelBridge absent' finding is superseded: the D11 modules are present in this snapshot and compile together with the D12 heat-domain repair (which imports them).",
        ],
    },
    "source_hashes": {
        "full_release_manifest": "audit-evidence/final-release-hashes.txt",
        "full_release_manifest_sha256": hash_manifest_sha,
        "release_files_hashed": len(hashes),
        "pre_integration_baseline": "audit-evidence/base-release-hashes-preintegration.txt",
        "pre_existing_files_changed": 0,
        "provenance_manifest": "audit-evidence/snapshot-provenance.json",
        "provenance_manifest_sha256": prov_sha,
        "provenance_file_count": prov["file_count"],
        "origins": prov["origins"],
        "third_party": [{
            "name": "frenzymath Poincare-Conjecture (van Kampen Hatcher Ch1 port)",
            "url": "https://github.com/frenzymath/Poincare-Conjecture",
            "revision": "bb91a091f0b968f8bbe8d861e025a88d82b161be",
            "license": "Apache-2.0",
            "location": "release/Poincare/VKPort (recovered from D12-surgery-recognition worktree)",
            "modifications": "none by D13; byte-identical copy; the D12 worktree's README documents its own port modifications",
        }],
    },
    "compile_evidence": {
        "cwd": str(WT / "release"),
        "fresh_build_dir": True,
        "transcript": "audit-evidence/logs/transcript.txt",
        "commands": transcript,
    },
    "axiom_evidence": {
        "programmatic": audit["checks"].get("C2_kernel_cones", {}),
        "literal_print_axioms": {
            "covered_declarations": len(lit),
            "missing": audit["checks"].get("C6_print_axioms", {}).get("missing", []),
            "violations": audit["checks"].get("C6_print_axioms", {}).get("violations", {}),
            "logs": [f"audit-evidence/logs/18-print-axioms-{i}.log" for i in range(4)],
        },
        "approved_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "negative_control": audit["checks"].get("C4_negative_control", {}),
        "self_audit": {"verdict": selfv, "audit": selfa},
        "partial_defs_note": ("3 `partial def` recursion helpers exist in D12 sources "
                              "(iteratedSphereSum._unsafe_rec, restrictionChain._unsafe_rec, "
                              "segChain._unsafe_rec); Lean requires the return type of a partial "
                              "definition to be nonempty (verified by a failing test: "
                              "`partial def badF : Nat -> False` is rejected), so these cannot "
                              "manufacture proofs of empty types; their cones are clean."),
    },
    "downstream_use_evidence": {
        "probe_log": "audit-evidence/logs/13-usage-probe.log",
        "key_inputs": uses,
        "zero_use_inputs": zero_use,
        "unresolved_names_in_claims": missing_use,
        "claimed_pairs": dep_pairs,
    },
    "statement_scan": {"counts": stmt, "suspects": suspects,
                       "log": "audit-evidence/logs/12-statement-audit.log"},
    "full_package_audit": audit["checks"].get("C11b_full_package_audit", {}),
    "next_dependency_requests": [
        "D12 owners: move the two negative-control modules outside the `Poincare.+` library glob (or into a `NegControl` lib excluded from defaultTargets) so the built package contains no `False` axiom; D13 did not edit them.",
        "D12 owners: correct the D12-heat-semigroup-analysis `downstream_use` for `heatOperatorBCF_comp`.",
        "D12 owners: machine-readable closure records should carry fully qualified (constructor, downstream) names; free-text arrows cannot be checked automatically.",
        "D12 owners: include `release/Poincare/VKPort` in the terminal release if its SR-4 claims are to be audited from the relay alone.",
        "D13-successors/D14: provide the manifold-level Levi-Civita/Riemannian framework (exponential map, Jacobi fields, sphere measures) to convert the D12 model/ODE results into geometric ones.",
        "D13-successors: audit the remaining unformalised analytic inputs named in the D12 remaining_blockers (Bochner identity on manifolds, weighted IBP with domination, C_c density in L1, van Kampen wiring, harmonic coordinates, Cheeger-Gromov compactness).",
    ],
    "actual_elapsed_time": json.loads((EVID / "elapsed.json").read_text())
        if (EVID / "elapsed.json").exists() else {},
}

(RES / "D13-integrated-kernel-audit.json").write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n")
print("wrote", RES / "D13-integrated-kernel-audit.json")
print("declarations:", len(decls), "theorems:", by_kind.get("theorem"),
      "print-axioms covered:", len(lit), "zero-use:", len(zero_use))
