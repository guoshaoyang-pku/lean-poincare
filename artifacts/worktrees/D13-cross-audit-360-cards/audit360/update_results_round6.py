#!/usr/bin/env python3
"""Round-6 (invocation 5) updater for the D13 cross-audit result card JSON.

Adds the round-6 evidence blocks, refreshes the header and merges the round-6
cold-rebuild evidence into `compile_evidence`.  Idempotent: rerunning replaces
the round-6 blocks with freshly computed values.
"""
import datetime
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")


def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


d = json.load(open(RES))
r6 = json.load(open(os.path.join(HERE, "round6_summary.json")))
cold = json.load(open(os.path.join(HERE, "cold_rebuilds_round6.json")))
fs = json.load(open(os.path.join(HERE, "forbidden_scan_round6.json")))
freeze = json.load(open(os.path.join(HERE, "card_freeze_round6.json")))

now = datetime.datetime.now().isoformat(timespec="seconds")
d["generated_at"] = now
d["status"] = "TASK_BLOCKED"
d["elapsed_hours"] = 0.42
d["cumulative_task_hours"] = 3.15
d["verdict"] = (
    "Round 6 (invocation 5): 7/9 cards re-verified a fifth consecutive time with "
    "byte-identical outputs (342 cones, 1103 declarations PASS; build/probe/full-audit "
    "byte-identical to round 5, kind screen byte-identical to the round-5 screen); all "
    "seven available cards are now additionally cold-rebuilt from source with no "
    ".lake/build (round 1: connection-curvature, surgery-recognition; round 6: the other "
    "five), cold build rc 0 and cold probe rc 0 in every case; a sixth independent closure "
    "consumer was added for the connection-curvature closure at a concrete NON-bi-invariant "
    "2D model, where the Milnor connection differs from the mean connection and the mean "
    "connection is not metric-compatible, plus the new uniqueness corollary "
    "d.nabla = milnorConnection; producer card files are still frozen (14/14 unchanged); "
    "the wider forbidden-token scan is clean apart from the documented volume-ibp "
    "negative-control axiom (no sorry/admit/native_decide/opaque/extern/implemented_by/"
    "unsafe def/proof_wanted anywhere in producer files); deep statement reviews of "
    "D12-spectral-sobolev and D12-connection-curvature are REVIEWED-CORRECT. 2/9 cards "
    "remain source-absent with no transport route (the reverse tunnel 127.0.0.1:10022 is "
    "refused and relay_push.sh cannot deliver) -> the 9-card milestone is still blocked."
)

d["reverification_round6"] = {
    "sweep": r6["logs"] + " (audit360/run_round6.sh)",
    "summary": "audit360/round6_summary.json",
    "summary_sha256": sha(os.path.join(HERE, "round6_summary.json")),
    "cards": {c: {"build_rc": v["build_rc"], "probe_rc": v["probe_rc"],
                  "fullaudit_rc": v["fullaudit_rc"], "kind_rc": v["kind_rc"],
                  "probe_declarations": v.get("probe_cone_lines"),
                  "fullaudit_declarations": v.get("fullaudit_declarations"),
                  "fullaudit_verdict": v.get("fullaudit_verdict"),
                  "identical_to_round5": {
                      "build": v["build_identical_to_round5"],
                      "probe": v["probe_identical_to_round5"],
                      "fullaudit": v["fullaudit_identical_to_round5"],
                      "kind": v["kind_identical_to_round5"]}}
              for c, v in r6["cards"].items()},
    "total_cones": r6["total_cones"],
    "total_declarations": r6["total_declarations"],
    "all_core_rc_zero": r6["all_core_rc_zero"],
    "all_core_identical_to_round5": r6["all_core_identical_to_round5"],
    "negative_control": r6["negative_control"].strip(),
    "snapshot_build_rc": r6["snapshot_build_rc"],
    "snapshot_probe_rc": r6["snapshot_probe_rc"],
    "a3d2d3_build_rc": r6["a3d2d3_build_rc"],
    "a3d2d3_probe_rc": r6["a3d2d3_probe_rc"],
    "a3d2d3_round3_rc": r6["a3d2d3_round3_rc"],
    "expected_nonzero_probes": {
        "D12-semantic-ledger:A3Extra/D12RealModuleProbe.lean": (
            "rc 1 (also rc 1 in round 5): module Poincare.D7.HeatKernel.Basic is not part "
            "of that release package; the valid replay is the snapshot package probe, rc 0"),
        "D12-geometric-compactness:A3ExtraR3/TrivialCheck.lean": (
            "rc 1 by design: the file IS the rfl attempt on diam_rep_of_toGHSpace; its "
            "failure is the round-3 evidence that the statement is not definitionally trivial"),
    },
}

d["cold_rebuilds_round6"] = cold
for card, v in cold["cards"].items():
    d["compile_evidence"].setdefault(card, {})["cold_rebuild_no_lake_cache_round6"] = v

r6_consumer = {
    "file": "audit360/pkgs/D12-connection-curvature/A3ExtraR6/ClosureUseNoninvariant.lean",
    "sha256": sha(os.path.join(WT, "audit360", "pkgs", "D12-connection-curvature",
                               "A3ExtraR6", "ClosureUseNoninvariant.lean")),
    "log": "audit360/logs-round6/D12-connection-curvature.extraR6.ClosureUseNoninvariant.log",
    "log_sha256": sha(os.path.join(HERE, "logs-round6",
                                   "D12-connection-curvature.extraR6.ClosureUseNoninvariant.log")),
    "compile_rc": int(open(os.path.join(HERE, "logs-round6",
                                        "D12-connection-curvature.extraR6.ClosureUseNoninvariant.rc")
                           ).read().strip().split("=")[-1]),
    "declarations": [
        "A3R6.a3_not_bracketInvariant",
        "A3R6.a3_noninvariant_leviCivita",
        "A3R6.a3_milnor_ne_mean",
        "A3R6.a3_mean_not_metricCompatible",
        "A3R6.a3_leviCivita_unique",
    ],
    "cones": "{propext, Classical.choice, Quot.sound} for all five #print axioms lines",
    "description": (
        "New adversarial consumer of the claimed LeviCivitaExistenceStatement closure. "
        "It builds a concrete 2-dimensional model (standard dot product; bracket "
        "[X,Y] = (X0*Y1 - X1*Y0) * (e0+e1)) that is NOT bracket-invariant, proves the "
        "closure holds there (leviCivitaExists), proves the Milnor connection differs from "
        "the mean connection and that the mean connection is NOT metric-compatible in this "
        "model, and proves the new uniqueness corollary that every Levi-Civita connection "
        "for a fixed (m,b) equals the Milnor connection. This is exactly the case where the "
        "historical BLOCKED docstring claimed an invariance hypothesis was needed."),
}
d["new_independent_closure_consumers_round6"] = {"D12-connection-curvature": r6_consumer}
d["a3_round6_declarations"] = {
    name: {"cone": "Classical.choice,Quot.sound,propext"} for name in r6_consumer["declarations"]
}

d["semantic_review_round6"] = {
    "D12-spectral-sobolev": (
        "REVIEWED-CORRECT (statement fidelity, 1-torus model). heatWeight = exp(-(2*pi*n/T)^2*t) "
        "is the correct circle heat eigenvalue; heatEvolve is defined by the Fourier-basis "
        "representation (not by the identity it satisfies); heatSeries_hasSum is a genuine "
        "HasSum of the infinite series over Z; fourierCoeff_heatEvolve gives c_n(H_t f) = "
        "w_n c_n(f); heatEvolve_zero/heatEvolve_add/norm contraction/strong continuity at "
        "t -> 0+ are the semigroup axioms; heatEvolve_fourierLp gives exact eigenfunctions. "
        "poincare_wirtinger is the sharp Poincare-Wirtinger inequality on the circle for C^1 "
        "mean-zero functions (the mean-zero condition fourierCoeffOn hab f 0 = 0 is equivalent "
        "to the interval mean by fourierCoeffOn_zero_eq_mean), and poincare_constant_sharp "
        "proves optimality from the sine-wave saturating witness (both integrals = pi). "
        "Scope is correctly restricted to dimension 1; no general compact-manifold transfer "
        "is claimed."),
    "D12-connection-curvature": (
        "REVIEWED-CORRECT (statement fidelity, left-invariant algebraic model). The Milnor "
        "connection is the group-invariant connection formula; torsion-freeness follows from "
        "bracket skew-symmetry, metric compatibility from skew-symmetry plus symmetry of the "
        "metric form (independently rederived by hand: the cross terms cancel and the two "
        "remaining terms are <[X,Y],Z> - <Z,[X,Y]> = 0). leviCivitaExists proves the previously "
        "BLOCKED LeviCivitaExistenceStatement unconditionally, and milnorConnection_eq_mean_iff "
        "shows invariance is exactly the condition for the MEAN connection to be Levi-Civita. "
        "ricci_symm is non-circular: CurvatureOperator's first-Bianchi/skew fields are "
        "constructed by AbstractConnection.toCurvatureOperator from the PROVED curvature_skew "
        "and curvature_bianchi (torsion-freeness + Jacobi), not assumed. The chart layer's "
        "nabla_torsionFree and nabla_metricCompatible are genuine Frechet-derivative statements "
        "(the latter via the three-factor product rule and the derived dFamily). Scope notes: "
        "IsMetricCompatible is the invariant-metric algebraic condition; SmoothChartData.gInv "
        "smoothness is coefficient data; the chart Lie bracket is defined by the coordinate "
        "formula; the x-dependent smoothness bridge for arbitrary (non-constant-coefficient) "
        "metrics remains the recorded open item."),
}

d["forbidden_scan_round6"] = {
    "artifact": "audit360/forbidden_scan_round6.json",
    "sha256": sha(os.path.join(HERE, "forbidden_scan_round6.json")),
    "tokens": fs["tokens"],
    "total_hits": fs["total_hits"],
    "packages_scanned": len(fs["packages"]),
    "lean_files_scanned": sum(v["lean_files"] for v in fs["packages"].values()),
    "non_A3_hits": [h for c, v in fs["packages"].items() for h in v["hits"]
                    if not h["file"].startswith("A3")],
    "interpretation": (
        "Zero hits for sorry/admit/native_decide/proof_wanted/opaque/extern/implemented_by/"
        "unsafe-def/maxHeartbeats-0 in producer files. The only producer hit is the documented "
        "volume-ibp negative-control `axiom negativeControl : False`, which is in no axiom cone. "
        "The 56 `partial` hits are the audit's own metaprogram A3UnusedHyp*.lean (structural "
        "recursion over Expr); they prove nothing and appear in no cone."),
}

d["card_freeze_round6"] = freeze
d["missing_cards_recheck_round6"] = {
    "checked_at": now,
    "result": ("D12-tensor-maximum-bochner and D12-triangulation-topology remain source-absent: "
               "no worktree, release package, card, Lean module, state directory or PUSHED/DONE "
               "marker anywhere under /data3/guoshaoyang; queue status still remote_owned "
               "(hosts 360-1 / 360-2); the reverse-tunnel transport in bin/relay_push.sh "
               "(ssh -p 10022 guoshaoyang@127.0.0.1) cannot deliver because port 10022 is "
               "refused; tailscale shows no 360-1/360-2 peer; no NFS/CIFS/SSHFS mounts. "
               "Conclusion unchanged: not auditable here, not refuted."),
    "transport_evidence": {
        "relay_script": "longrun/bin/relay_push.sh",
        "reverse_tunnel_port": "127.0.0.1:10022",
        "port_state": "connection refused (re-tested 2026-09-11 14:47, 14:52)",
        "queue_status": "remote_owned",
    },
}

# round-6 artifact hashes (the verifier itself is included; its recorded hash is
# refreshed in round5_artifacts as well, mirroring the round-5 self-audit note)
r6_artifacts = [
    "run_round6.sh", "round6_summary.py", "round6_summary.json",
    "run_cold_round6.sh", "cold_rebuilds_round6.py", "cold_rebuilds_round6.json",
    "forbidden_scan6.py", "forbidden_scan_round6.json",
    "card_freeze_round6.py", "card_freeze_round6.json",
    "update_results_round6.py", "verify_own_hashes.py",
]
d["round6_artifacts"] = {name: sha(os.path.join(HERE, name)) for name in r6_artifacts}
d["round6_artifacts"]["D12-connection-curvature.extraR6.ClosureUseNoninvariant.log"] = \
    r6_consumer["log_sha256"]
d.setdefault("round5_artifacts", {})["verify_own_hashes.py"] = \
    d["round6_artifacts"]["verify_own_hashes.py"]

json.dump(d, open(RES, "w"), indent=1)
print("updated", RES)
print("r6 consumer sha", r6_consumer["sha256"])
print("round6 artifacts", len(d["round6_artifacts"]))
