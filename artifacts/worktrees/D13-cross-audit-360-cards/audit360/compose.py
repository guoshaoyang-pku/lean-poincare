#!/usr/bin/env python3
"""Compose longrun/results/D13-cross-audit-360-cards.json from the collected
audit artifacts (inventory, probe analysis, build logs)."""
import hashlib
import json
import os
import re
import time

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
SIB = os.path.dirname(WT)
LOGS = os.path.join(HERE, "logs")

CARDS = [
    "D12-connection-curvature",
    "D12-volume-ibp",
    "D12-spectral-sobolev",
    "D12-semantic-ledger",
    "D12-comparison-geodesics",
    "D12-geometric-compactness",
    "D12-surgery-recognition",
]
MISSING = ["D12-tensor-maximum-bochner", "D12-triangulation-topology"]


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


def main():
    inv = json.load(open(os.path.join(HERE, "inventory.json")))
    ar = json.load(open(os.path.join(HERE, "audit_result.json")))
    inv_by_card = {e["card"]: e for e in inv["cards"]}
    out = {
        "schema": "poincare-longrun-result-card-v1",
        "task_id": "D13-cross-audit-360-cards",
        "stage": "D13",
        "lane": "auditor (A3)",
        "generated_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        "status": "TASK_IN_PROGRESS",
        "verdict": ("7/9 360-produced D12 cards independently rebuilt and axiom-audited; "
                    "4/4 claimed blocker closures confirmed; 2/9 cards source-absent on this host"),
        "named_blockers": ["A3"],
        "named_blocker_status": {
            "A3": ("OPEN. A3 = adversarial audit covers only the D4 evolution cluster. This task adds "
                   "D12-card adversarial coverage (source-hash, rebuild, axiom, semantic) but does not "
                   "perform the D2/D3 counterexample search that A3 asks for; the two missing D12 cards "
                   "also leave residual audit gaps.")
        },
        "scope": {
            "cards_requested": 9,
            "cards_available_and_audited": 7,
            "cards_source_absent": MISSING,
            "producer_lanes": {
                "360-1": ["D12-connection-curvature", "D12-volume-ibp",
                          "D12-tensor-maximum-bochner", "D12-spectral-sobolev",
                          "D12-semantic-ledger"],
                "360-2": ["D12-comparison-geodesics", "D12-geometric-compactness",
                          "D12-triangulation-topology", "D12-surgery-recognition"],
            },
        },
        "method": [
            "Recompute every recorded source_sha256 from bytes on disk in the producer worktree (no manifest trusted).",
            "Copy release sources (no .lake caches) into audit360/pkgs/<card>; symlink the shared pinned mathlib cache.",
            "Fresh lake build with pinned leanprover/lean4:v4.34.0-rc2 and mathlib 7974e751.",
            "Resolve every declared name to a fully-qualified Lean name by source scan (namespace aware); generate A3Probe.lean with #check + #print axioms per name.",
            "Fail-closed cone predicate: every cone must be a subset of {propext, Classical.choice, Quot.sound}; validated by a compiled negative control (sorry, native_decide).",
            "Comment/string-aware forbidden-token scan; classify documented negative-control axioms and verify they appear in no cone.",
            "Semantic review of headline statements and of every exact_blockers_closed claim (constructor, statement strength, downstream checked use).",
            "Base/vendored dependency provenance: byte-compare against the D6 release and sibling worktrees; replay the semantic-ledger 37-module snapshot rebuild from its recorded hashes.",
        ],
        "cards": {},
        "proved_declarations": {},
        "expanded_hypotheses": {},
        "semantic_class": {},
        "exact_blockers_closed": {},
        "remaining_blockers": {},
        "source_hashes": {},
        "compile_evidence": {},
        "axiom_evidence": {},
        "next_dependency_requests": [],
    }
    for card in CARDS:
        cj = json.load(open(os.path.join(SIB, card, "longrun", "results", card + ".json")))
        ck = json.load(open(os.path.join(SIB, card, "checkpoint.json")))
        a = ar["cards"][card]
        i = inv_by_card[card]
        extra_audited = 0
        if card == "D12-semantic-ledger" and ar.get("snapshot_rebuild_audit"):
            extra_audited = len(ar["snapshot_rebuild_audit"]["cones"])
        out["cards"][card] = {
            "producer_status": cj.get("status"),
            "producer_checkpoint_status": ck.get("status"),
            "card_json_sha256": i.get("card_json_sha256"),
            "card_md_sha256": i.get("card_md_sha256"),
            "hash_summary": i.get("hash_summary"),
            "build_rc": a["build_rc"],
            "probe_rc": a["probe_rc"],
            "declared": a["declared"],
            "audited": a["audited"] + extra_audited,
            "audited_extra_snapshot_rebuild": extra_audited,
            "cone_violations": len(a["cone_violations"]),
            "forbidden_hits": a["forbidden_hits"],
            "axiom_declarations": a["axiom_declarations"],
            "axiom_declarations_unused_in_cones": a["axiom_declarations_unused_in_cones"],
            "namespace_qualified_names": a["card_namespace_notes"],
            "unresolved_card_names": a["unresolved_in_card"],
            "audit_verdict": a["verdict"],
        }
        decls = [r["fq"] for r in json.load(
            open(os.path.join(HERE, "pkgs", card, "A3Meta.json")))["resolved"]]
        if card == "D12-semantic-ledger" and ar.get("snapshot_rebuild_audit"):
            decls = decls + sorted(ar["snapshot_rebuild_audit"]["cones"].keys())
        out["proved_declarations"][card] = decls
        out["expanded_hypotheses"][card] = cj.get("expanded_hypotheses")
        out["semantic_class"][card] = cj.get("semantic_class")
        out["exact_blockers_closed"][card] = cj.get("exact_blockers_closed")
        rb = cj.get("remaining_blockers") or []
        out["remaining_blockers"][card] = rb if isinstance(rb, (list, dict)) else [rb]
        out["source_hashes"][card] = {
            "producer_recorded": cj.get("source_hashes"),
            "verified_against_disk": i.get("hash_summary"),
            "audited_copy_sha256": json.load(open(os.path.join(HERE, "pkgs", card, "A3Meta.json")))["copy_sha256"],
        }
        jobs = re.findall(r"\[(\d+)/(\d+)\]", open(os.path.join(LOGS, card + ".build.log")).read())
        out["compile_evidence"][card] = {
            "toolchain": open(os.path.join(HERE, "pkgs", card, "lean-toolchain")).read().strip(),
            "mathlib_rev": "7974e751bece493b6ff508039423ca9fa2452fa8",
            "lake_build_rc": a["build_rc"],
            "probe_rc": a["probe_rc"],
            "jobs": jobs[-1] if jobs else None,
            "build_log_sha256": sha256(os.path.join(LOGS, card + ".build.log")),
            "probe_log_sha256": a["probe_log_sha256"],
        }
        fresh_build = os.path.join(LOGS, card + ".fresh.build.log")
        fresh_probe = os.path.join(LOGS, card + ".fresh.probe.log")
        if os.path.isfile(fresh_build) and os.path.isfile(fresh_probe):
            fjobs = re.findall(r"\[(\d+)/(\d+)\]", open(fresh_build).read())
            out["compile_evidence"][card]["cold_rebuild_no_lake_cache"] = {
                "lake_build_rc": open(os.path.join(LOGS, card + ".fresh.build.rc")).read().strip(),
                "probe_rc": open(os.path.join(LOGS, card + ".fresh.probe.rc")).read().strip(),
                "jobs": fjobs[-1] if fjobs else None,
                "probe_declarations": len(re.findall(r"depends on axioms|does not depend", open(fresh_probe).read())),
                "errors": len(re.findall(r": error", open(fresh_probe).read())),
                "build_log_sha256": sha256(fresh_build),
                "probe_log_sha256": sha256(fresh_probe),
            }
        cones = a["cones"]
        hist = {}
        for v in cones.values():
            hist[",".join(sorted(v)) or "(none)"] = hist.get(",".join(sorted(v)) or "(none)", 0) + 1
        out["axiom_evidence"][card] = {
            "audited_declarations": a["audited"] + extra_audited,
            "cone_histogram": hist,
            "cone_violations": a["cone_violations"],
            "forbidden_hits": a["forbidden_hits"],
            "documented_negative_control_axioms": a["axiom_declarations"],
        }
    for c in MISSING:
        out["cards"][c] = {
            "producer_status": "remote_owned (no artifacts on this host)",
            "audit_verdict": "NOT AUDITABLE",
            "card_json_sha256": None,
            "card_md_sha256": None,
            "hash_summary": None,
            "build_rc": None,
            "probe_rc": None,
            "declared": 0,
            "audited": 0,
            "cone_violations": None,
            "forbidden_hits": [],
        }
        out["proved_declarations"][c] = []
        out["expanded_hypotheses"][c] = None
        out["semantic_class"][c] = None
        out["exact_blockers_closed"][c] = None
        out["remaining_blockers"][c] = ["card artifacts absent on this host"]
        out["source_hashes"][c] = None
        out["compile_evidence"][c] = None
        out["axiom_evidence"][c] = None
    full = {}
    for card in CARDS:
        fp = os.path.join(LOGS, card + ".fullaudit.log")
        if os.path.isfile(fp):
            txt = open(fp).read()
            m = re.search(r"A3FULL: (\d+) declarations", txt)
            full[card] = {
                "declarations_under_Poincare_D12": int(m.group(1)) if m else None,
                "pass": "A3FULL: PASS" in txt,
                "bad": len(re.findall(r"A3FULL-BAD:", txt)),
                "log_sha256": sha256(fp),
                "rc": open(os.path.join(LOGS, card + ".fullaudit.rc")).read().strip(),
            }
    out["axiom_evidence"]["full_namespace_audit"] = {
        "method": ("Lean metaprogram enumerating every constant in the compiled environment under the "
                   "Poincare.D12 root and checking its transitive axiom cone against "
                   "{propext, Classical.choice, Quot.sound}; documented unused negative-control axiom skipped."),
        "per_card": full,
        "total_declarations": sum(v["declarations_under_Poincare_D12"] or 0 for v in full.values()),
        "total_bad": sum(v["bad"] for v in full.values()),
    }
    out["axiom_evidence"]["negative_control"] = ar["negative_control"]
    out["axiom_evidence"]["semantic_ledger_snapshot_rebuild"] = ar.get("snapshot_rebuild_audit")
    out["missing_cards"] = [
        {
            "card": c,
            "finding": ("no worktree, release package, card (.md/.json), Lean module or checkpoint exists "
                        "anywhere under /data3/guoshaoyang/workdir/lean_poincare on this host; the card is "
                        "referenced only as a remote_owned queue entry (lane 360-1/360-2) in D12-plan.json. "
                        "Cannot be re-verified; recorded as source-absent, NOT as refuted."),
            "evidence": "exhaustive filename search for *TensorMaximum*/*TriangulationTopology* over the tree, .lake pruned",
        }
        for c in MISSING
    ]
    out["findings"] = [
        {"id": "F1", "severity": "claim-provenance",
         "card": "D12-connection-curvature",
         "finding": ("73/119 entries of proved_declarations are over-qualified with file-derived namespace "
                     "segments that do not exist in the compiled sources, e.g. "
                     "Poincare.D12.ConnectionCurvature.ChartLeviCivita.ChartMetricCoefficients.christoffel_symm "
                     "vs the real Poincare.D12.ConnectionCurvature.ChartMetricCoefficients.christoffel_symm. "
                     "Unique short-name matches in the sources confirm every one of the 119 declarations exists "
                     "and compiles; the defect is in the card inventory, not the mathematics.")},
        {"id": "F2", "severity": "claim-provenance",
         "card": "D12-semantic-ledger",
         "finding": ("2/9 declared names are attributed to audit_probes/D12RealModuleProbe.lean outside the "
                     "release package. Independent replay of the producer's 37-module snapshot rebuild "
                     "(all 37 recorded source hashes verified against D11-bochner-manifold sources) compiles "
                     "the probe and both declarations have cone {propext, Classical.choice, Quot.sound}.")},
        {"id": "F3", "severity": "audit-coverage",
         "card": "D12-tensor-maximum-bochner, D12-triangulation-topology",
         "finding": "Producer artifacts absent on this host; 2/9 cards cannot be re-verified (see missing_cards)."},
        {"id": "F4", "severity": "semantic-minor",
         "card": "D12-comparison-geodesics",
         "finding": ("The model non-vacuity witnesses euclidModel_singular_comparison_ge and "
                     "euclidModel_bishopGromov are reflexive instances (m <= m; V R/V R <= V r/V r), so they "
                     "show hypothesis satisfiability but do not exercise a strict comparison. The general "
                     "Sturm/Riccati/BG theorems themselves are substantive and division-free.")},
        {"id": "F5", "severity": "intentional-negative-control",
         "card": "D12-volume-ibp",
         "finding": ("Poincare/D12/VolumeIBP/Audit.lean declares 'axiom negativeControl : False', documented "
                     "in-file as the audit detector's negative control. It appears in no axiom cone of the 78 "
                     "audited declarations and is not imported by any proved result; recorded, not a violation.")},
        {"id": "F6", "severity": "process-state",
         "card": "all",
         "finding": ("Queue/checkpoint state does not match card verdicts: D12-connection-curvature and "
                     "D12-volume-ibp checkpoints are in_progress while the cards say TASK_DONE; "
                     "D12-geometric-compactness checkpoint is in_progress; D12-semantic-ledger is gate_failed "
                     "in the queue with blockers A1/A2/A3/P1/P5. Card artifacts were frozen 02:02-04:50 on "
                     "2026-09-11 and this audit pins those hashes.")},
        {"id": "F7", "severity": "scope-nuance",
         "card": "D12-connection-curvature",
         "finding": ("chartMetricCompatible_form/chartTorsionFree_form are algebraic identities whose "
                     "right-hand side is the supplied coefficient datum dFormOf (and zero bracket in "
                     "coordinates); the genuine Frechet-derivative statements are nabla_metricCompatible / "
                     "nabla_torsionFree, which are present and audited. The card discloses this boundary.")},
    ]
    out["exact_blockers_closed_audit"] = {
        "D12-connection-curvature": [{
            "blocker": "LeviCivitaExistenceStatement (Poincare.Longrun.Geometry.LeviCivitaBlocked)",
            "verdict": "CONFIRMED",
            "evidence": ("Statement definition unchanged (byte-identical base module vs D6 release): "
                         "∃ nabla, IsLeviCivita m b nabla. levCivitaExists proves it unconditionally with "
                         "the explicit Milnor witness milnorConnection; torsion-freeness and metric "
                         "compatibility are separate theorems. Downstream checked use: meanLeviCivitaData -> "
                         "so3MeanLeviCivita -> ricci_symm / so3_ricci_e00 = 1/2 != 0. The card's correction "
                         "of the historical 'false without invariance' docstring is mathematically right: "
                         "invariance is needed only for the mean connection (milnorConnection_eq_mean_iff)."),
        }],
        "D12-surgery-recognition": [
            {"blocker": "SR-5 sphere_of_spheres",
             "verdict": "CONFIRMED (with decomposition data as explicit V2 input)",
             "evidence": ("ConnectedSumDecomposition.mkV2 derives the D7 sphere_of_spheres field from the "
                          "proved iteratedSphereSum_homeo_sphere (built on sphereConnectSum_homeo_sphere and "
                          "doubleBallHomeoSphere, both explicit homeomorphism constructions). The geometric "
                          "input X ~ iterated sum is carried as ConnectedSumDecompositionV2.sumHomeo data, "
                          "not proved; downstream use stage6Target_of_v2decomposition rebuilds the extinction "
                          "certificate with mkV2.")},
            {"blocker": "covering-space recognition (topological half of SphericalPieceRecognition)",
             "verdict": "CONFIRMED",
             "evidence": ("finiteFreeOrbit_isQuotientCoveringMap proves mathlib's IsQuotientCoveringMap for a "
                          "finite continuous free action on S3 with explicitly constructed evenly covered "
                          "neighbourhoods (positive separation of nontrivial translates); antipodal model is "
                          "a nondegenerate 2-sheeted instance. Downstream: RemainingRecognitionHypothesesV2 / "
                          "stage6Target_of_v2hypotheses.")},
            {"blocker": "coveringTrivial (simply connected space-form quotient has trivial deck group)",
             "verdict": "CONFIRMED",
             "evidence": ("deckTrivial_of_simplyConnected_quotient proves Subsingleton M.Gamma from "
                          "[SimplyConnectedSpace M.quotient.Carrier] via mathlib monodromy (path/homotopy "
                          "lifting); SphericalSpaceFormModel has no triviality field, so the theorem is not "
                          "vacuous. Downstream: sphericalPieceRecognition_of_spaceForm and "
                          "stage6Target_of_v3hypotheses.")},
        ],
    }
    out["next_dependency_requests"] = [
        "Sync or re-run D12-tensor-maximum-bochner and D12-triangulation-topology on this host; without their release packages the 9-card milestone cannot be fully checked.",
        "Producer-side correction of the D12-connection-curvature proved_declarations namespace qualification (73 entries) and of D12-comparison-geodesics grouped name strings.",
        "A3 follow-up: D2/D3 counterexample search is still absent; this audit only adds D12-card coverage.",
        "Add nontrivial (non-reflexive) model witnesses for the singular Riccati comparison and the Bishop-Gromov volume ratio in D12-comparison-geodesics.",
    ]
    import datetime
    start = datetime.datetime.fromisoformat("2026-09-11T12:23:11+08:00")
    elapsed = round((time.time() - start.timestamp()) / 3600.0, 2)
    out["elapsed_hours"] = elapsed
    with open(os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("wrote results json; cards:", list(out["cards"].keys()))
    print("elapsed_hours", elapsed)


if __name__ == "__main__":
    main()
