#!/usr/bin/env python3
"""Round-4 finalization: update checkpoint.json and the result-card JSON with the round-4
independent acceptance + additive closed-form module.  Run after the reviews land."""
import hashlib
import json
import datetime
import os

WT = "/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L4-child-ricci-to-doubling"
os.chdir(WT)


def sha(p):
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""):
            h.update(c)
    return h.hexdigest()


H = {p: sha(p) for p in [
    "release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean",
    "release/Audit/RicciToDoublingHyperbolicClosedFormAudit.lean",
    "tools/round4_acceptance_check.py",
    "tools/round4_numeric_checks.py",
    "tools/round4_forced_rebuild.sh",
    "tools/round4_closedform_audit.sh",
    "evidence/round4-acceptance.json",
    "evidence/round4-numeric-checks.json",
    "evidence/round4-audit-full.log",
    "logs/round4-rebuild.log",
    "logs/round4-closedform-audit.log",
    "logs/round4-closedform-build.log",
    "evidence/round4-symbolic-checks.json",
    "tools/round4_symbolic_checks.py",
    "evidence/round4-review-closedform.md",
    "evidence/round4-review-frozen.md",
]}

cp = json.load(open("checkpoint.json"))
cp["round4_new_artifacts"][0]["sha256"] = H["release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean"]
cp["round4_new_artifacts"][1]["sha256"] = H["release/Audit/RicciToDoublingHyperbolicClosedFormAudit.lean"]
cp["round4_acceptance"] = {
    "round": 4,
    "verdict": "PASS / TASK_DONE (scalar/model + documented conditional metric-measure interface; U9 manifold half open)",
    "frozen_revision_unchanged": True,
    "frozen_hashes": {
        "release/Poincare/L4/Compactness/RicciToDoubling.lean":
            "9b17c673d836fc227e4f6dfca50d0261720b5584883b5cd5985a63c9dc76a1d4",
        "release/Poincare/L4/Compactness/RicciToDoublingHyperbolic.lean":
            "be50ae25b1dee588c21ad237e9aa013af43938888a51200668a3e95ad4790841",
        "release/Audit/RicciToDoublingAudit.lean":
            "3e8510bc5ddf37d7d15e13841d20f30ee3f08ffe77ceca210871d515f72a1417",
        "release/Audit/RicciToDoublingHyperbolicAudit.lean":
            "dc9b26384f279add1108ac5b83b41df7dd960b89357329ce31ee7c03422c7ee3",
    },
    "method": ("forced recompilation of the frozen pair (oleans deleted; BUILD-EXIT=0, zero "
               "warnings, 3454 jobs) and of the new module (CF-BUILD-EXIT=0, 3461 jobs); fresh "
               "fail-closed axiom audits 34 + 15 = 49 cones, all exactly "
               "{propext, Classical.choice, Quot.sound}; round-4 11-gate checker; 387/387 "
               "independent numeric checks; two fresh adversarial reviews"),
    "gates": {
        "hash_freeze_frozen_and_round4": "PASS (4 frozen unchanged + 2 round-4 match checkpoint)",
        "axiom_cones_subset_classical_trio": "PASS (49 declarations, 0 violations, zero warnings)",
        "no_conclusion_equivalent_hypothesis": "PASS (14 headline declarations, arrow-depth-aware)",
        "no_manifold_overclaim": "PASS (0 manifold tokens in 49 declaration types and stripped sources)",
        "classification_labels_51_51": "PASS (13 + 23 frozen and 15 round-4 declarations labelled)",
        "independent_numeric_evidence": "PASS (387/387; closed-form recursion and substitution identity vs quadrature, signed radii/kappa)",
        "no_rauch_conjugate_point_duplication": "PASS",
        "canonical_forbidden_scan": "PASS (0 hard matches over 6 files)",
        "statement_fidelity_to_acceptance_text": "PASS (required closed forms present in compiled signatures)",
        "round4_closedform_consumes_frozen_model": "PASS",
        "closed_form_hypotheses_identical_to_frozen": "PASS (27 = 27 top-level hypotheses, byte-identical, for ratio and doubling)",
        "exact_symbolic_closedform_evidence": "PASS (26/26 sympy checks: J_d = integral of sinh^d and J_d' = sinh^d exactly for d = 0..9; model volume closed form exactly for d = 0..5)",
    },
    "new_module": {
        "file": "release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean",
        "sha256": H["release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean"],
        "declarations": 15,
        "content": ("elementary recursive antiderivative sinhPowIntegral with J_d' = sinh^d and "
                    "∫₀ˢ sinh^d = J_d(s) proved; radialVolume (hypModelA d κ) s = (κ⁻¹)^(d+1) J_d(κ s); "
                    "model ratio J_d(κR)/J_d(κr); closed-form Bishop-Gromov ratio and doubling "
                    "composites with hypotheses identical to the frozen instantiations; d=1,2,3 "
                    "evaluations; removes the round-3 M3 caveat (general-d hyperbolic constant)"),
        "class": "model (scalar ODE) only; no manifold content",
    },
    "evidence": {
        "acceptance": {"file": "evidence/round4-acceptance.json", "sha256": H["evidence/round4-acceptance.json"]},
        "numeric": {"file": "evidence/round4-numeric-checks.json", "sha256": H["evidence/round4-numeric-checks.json"]},
        "symbolic": {"file": "evidence/round4-symbolic-checks.json", "sha256": H["evidence/round4-symbolic-checks.json"]},
        "audit_full": {"file": "evidence/round4-audit-full.log", "sha256": H["evidence/round4-audit-full.log"]},
        "rebuild_log": {"file": "logs/round4-rebuild.log", "sha256": H["logs/round4-rebuild.log"]},
        "closedform_audit_log": {"file": "logs/round4-closedform-audit.log", "sha256": H["logs/round4-closedform-audit.log"]},
        "closedform_build_log": {"file": "logs/round4-closedform-build.log", "sha256": H["logs/round4-closedform-build.log"]},
        "checker": {"file": "tools/round4_acceptance_check.py", "sha256": H["tools/round4_acceptance_check.py"]},
        "numeric_script": {"file": "tools/round4_numeric_checks.py", "sha256": H["tools/round4_numeric_checks.py"]},
    },
    "reviews": {
        "closedform_module": {"file": "evidence/round4-review-closedform.md",
                              "outcome": ("CLEAN, no BLOCKER, no MAJOR, no MINOR mathematical "
                                          "defect; recursion and closed form independently "
                                          "re-derived by hand, exact sympy (d/dx J_d = sinh^d, "
                                          "d <= 8) and mpmath to 1e-73; compiled statements "
                                          "verified by #check (all real s, only kappa != 0); "
                                          "binder lists mechanically identical to the frozen "
                                          "theorems; conclusion derived from the frozen "
                                          "instantiation; 15/15 cones reproduced with a live "
                                          "negative control; all falsification attempts failed; "
                                          "an independent kernel FTC reproof of the closed form "
                                          "compiles; three INFO notes recorded (floating-point "
                                          "conditioning of the recursion near x = 0 for large d, "
                                          "the deliberate d=1,kappa=1 consistency corollary, and "
                                          "the audit-helper labelling convention)")},
        "frozen_set": {"file": "evidence/round4-review-frozen.md",
                       "outcome": ("OVERALL PASS, no BLOCKER, no MAJOR; all six hashes recomputed "
                                   "twice, 49/49 cones exactly the classical trio, three audits "
                                   "reproduced byte-identically via lean --stdin, zero "
                                   "conclusion-equivalent hypotheses, zero manifold tokens in "
                                   "code, frozen integrity confirmed (empty declaration-name "
                                   "intersection, no shadowing), forced-token scan clean, "
                                   "non-vacuity witnesses and snowflake arithmetic re-verified; "
                                   "two MINOR documentation-level findings recorded")},
    },
    "numeric_caveat": ("INFO from the closed-form review: the two-step recursion is an exact closed "
                       "form but a numerically ill-conditioned evaluation recipe near x = 0 for "
                       "large d (leading-order cancellation).  The Lean theorems are symbolic and "
                       "exact; the caveat concerns naive floating-point evaluation of the recursion "
                       "only, not the formalized statements."),
    "m3_caveat_disposition": ("CLOSED by the additive round-4 module: the general-d hyperbolic "
                              "model volume/ratio is now an explicit elementary recursive closed "
                              "form; the previously recorded M1, M2, M4 remain documentation-only "
                              "wording items in the frozen files, which were deliberately not "
                              "edited so that the recorded hashes stay valid."),
}
cp["acceptance_self_assessment"]["req1_explicit_model_and_closed_form_ratio"] = (
    "DONE both signs, now fully elementary hyperbolic: Euclidean k >= 0 closed form (R/r)^(d+1); "
    "hyperbolic k >= -d*kappa^2 with explicit model and, in the round-4 additive module, the "
    "elementary recursive closed form radialVolume (hypModelA d kappa) s = (kappa^-1)^(d+1) J_d(kappa s) "
    "and ratio J_d(kappa R)/J_d(kappa r) for every d (J_d' = sinh^d proved; d=1,2,3 evaluated)")
cp["not_claimed"] = [
    "no Riemannian manifold, no Riemannian volume measure, no geodesic sphere density identification, no coarea formula",
    "no derivation of the Riccati inequality from a Ricci curvature bound",
    "no centrewise two-sided comparability of a manifold ball measure",
    "U9 is not closed (manifold half remains open)",
    "the round-4 closed form is a scalar/model statement about the hyperbolic comparison ODE, not a manifold volume formula",
]
cp["updated_at"] = datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")
json.dump(cp, open("checkpoint.json", "w"), indent=1)

# ---- result-card JSON ----
rc = json.load(open("longrun/results/L4-child-ricci-to-doubling.json"))
rc["artifacts"] = rc.get("artifacts", []) + [
    {"file": "release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean",
     "sha256": H["release/Poincare/L4/Compactness/RicciToDoublingHyperbolicClosedForm.lean"],
     "declarations": 15, "round": 4,
     "content": "elementary recursive closed form of the hyperbolic model volume/ratio; removes the M3 caveat"},
    {"file": "release/Audit/RicciToDoublingHyperbolicClosedFormAudit.lean",
     "sha256": H["release/Audit/RicciToDoublingHyperbolicClosedFormAudit.lean"],
     "round": 4, "content": "fail-closed signature + axiom audit for the 15 round-4 declarations"},
]
rc["acceptance"]["req1_explicit_model_closed_form_ratio"]["hyperbolic_closed_form_round4"] = (
    "sinhPowIntegral d with J_d' = sinh^d and int_0^s sinh^d = J_d(s); "
    "radialVolume (hypModelA d kappa) s = (kappa^-1)^(d+1) * J_d(kappa*s); "
    "ratio J_d(kappa R)/J_d(kappa r) for every d (d=1,2,3 evaluated); "
    "hyp_volume_ratio_le_of_ricci_ge_closedForm / hyp_volume_doubling_closedForm with the same "
    "27 hypotheses as the frozen instantiations")
rc["verification"]["round4"] = cp["round4_acceptance"]
rc["verdict"] = "TASK_DONE"
rc["scope"] = (rc.get("scope", "") +
               " Round 4 adds an additive scalar/model module: explicit elementary recursive "
               "closed form of the hyperbolic model volume and ratio; frozen files untouched.")
rc["updated_at"] = datetime.datetime.utcnow().strftime("%Y-%m-%dT%H:%M:%SZ")
json.dump(rc, open("longrun/results/L4-child-ricci-to-doubling.json", "w"), indent=1)
print("checkpoint + result-card JSON updated")
print(json.dumps({k: v for k, v in H.items()}, indent=1))
