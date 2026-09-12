#!/usr/bin/env python3
"""Final close-out updater (round 10, invocation 7).

Adds: round-10 sweep block, round-10 artifacts, final state / deliverable field
map, and the §18 close-out section to the markdown card.
"""
import datetime
import hashlib
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
WT = os.path.dirname(HERE)
RES_JSON = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.json")
RES_MD = os.path.join(WT, "longrun", "results", "D13-cross-audit-360-cards.md")


def sha(p):
    return hashlib.sha256(open(p, "rb").read()).hexdigest()


def h(name):
    return sha(os.path.join(HERE, name))


d = json.load(open(RES_JSON))
r10 = json.load(open(os.path.join(HERE, "round10_summary.json")))
miss10 = json.load(open(os.path.join(HERE, "missing_cards_recheck_round10.json")))
d["generated_at"] = datetime.datetime.now().isoformat(timespec="seconds")
d["elapsed_hours"] = 2.1
d["cumulative_task_hours"] = 5.05

d["round10_artifacts"] = {
    "run_round10.sh": h("run_round10.sh"),
    "round10_summary.py": h("round10_summary.py"),
    "round10_summary.json": h("round10_summary.json"),
    "missing_cards_recheck_round10.py": h("missing_cards_recheck_round10.py"),
    "missing_cards_recheck_round10.json": h("missing_cards_recheck_round10.json"),
    "taut_screen_round9.json": h("taut_screen_round9.json"),
    "taut_screen_full_round9.json": h("taut_screen_full_round9.json"),
    "taut_screen_d2d3_round9.json": h("taut_screen_d2d3_round9.json"),
}

d["reverification_round10"] = {
    "sweep": r10["logs"] + " (audit360/run_round10.sh)",
    "summary": "audit360/round10_summary.json",
    "summary_sha256": h("round10_summary.json"),
    "cards": {c: {"build_rc": v["build_rc"], "probe_rc": v["probe_rc"],
                  "fullaudit_rc": v["fullaudit_rc"], "kind_rc": v["kind_rc"],
                  "probe_declarations": v.get("probe_cone_lines"),
                  "fullaudit_declarations": v.get("fullaudit_declarations"),
                  "fullaudit_verdict": v.get("fullaudit_verdict"),
                  "identical_to_round8": {
                      "build": v["build_identical_to_round8"],
                      "probe": v["probe_identical_to_round8"],
                      "fullaudit": v["fullaudit_identical_to_round8"],
                      "kind": v["kind_identical_to_round8"]}}
              for c, v in r10["cards"].items()},
    "total_cones": r10["total_cones"],
    "total_declarations": r10["total_declarations"],
    "all_core_rc_zero": r10["all_core_rc_zero"],
    "all_core_identical_to_round8": r10["all_core_identical_to_round8"],
    "negative_control": r10["negative_control"].strip(),
    "snapshot_build_rc": r10["snapshot_build_rc"],
    "snapshot_probe_rc": r10["snapshot_probe_rc"],
    "a3d2d3_build_rc": r10["a3d2d3_build_rc"],
    "a3d2d3_probe_rc": r10["a3d2d3_probe_rc"],
    "a3d2d3_round3_rc": r10["a3d2d3_round3_rc"],
    "round9_screens_reproduced": (
        "the declared-set, full-namespace Prop-gated and D2/D3 tautology screens were re-run "
        "after the sweep: rc 0 and byte-identical artifacts (hash-compared)"),
}

d["missing_cards_recheck_round10"] = {
    "artifact": "audit360/missing_cards_recheck_round10.json",
    "sha256": h("missing_cards_recheck_round10.json"),
    "script_sha256": h("missing_cards_recheck_round10.py"),
    "checked_at": miss10["checked_at"],
    "transport": {k: v for k, v in miss10["transport"].items() if k != "dispatcher_log_tail"},
    "cards": {c: {"queue": e["queue"], "named_hits": len(e["named_hits"]),
                  "any_path_exists": any(v["exists"] for v in e["paths"].values())}
              for c, e in miss10["cards"].items()},
    "verdict": miss10["verdict"],
}

d["final_state"] = {
    "milestone": "9-card independent re-verification",
    "status": "TASK_BLOCKED",
    "cards_fully_reverified": 7,
    "cards_not_auditable": ["D12-tensor-maximum-bochner", "D12-triangulation-topology"],
    "reason": d["missing_cards_recheck_round10"]["verdict"],
    "sweeps": "rounds 1-10; rounds 2-10 byte-identical for the seven available cards "
              "(342 cones, 1103 full-namespace declarations PASS each round)",
    "named_blocker_A3_status": "stale-as-stated / partially addressed: the D2/D3 defects "
                               "(LinearDecayCertificate emptiness, trivial "
                               "CovariantDerivativeCurvatureStatement, degenerate "
                               "TensorRicciFlowODEBridge, statement defects, plus the new "
                               "A3-D2D3-9 restatement) remain unrepaired on the producer "
                               "side; 2/9 D12 cards remain unaudited",
    "deliverable_field_map": {
        "proved_declarations": "JSON .proved_declarations (342 names, 7 cards; hash-verified "
                               "producer sources + kernel resolution)",
        "expanded_hypotheses": "JSON .expanded_hypotheses / MD §4, §11.8 (F12b), §16.3",
        "semantic_class": "JSON .semantic_class + .semantic_class_corrections / MD §6, §14.4, §16.3",
        "exact_blockers_closed": "JSON .exact_blockers_closed + .exact_blockers_closed_audit / "
                                 "MD §5, §15.2-15.3, §16.2, §16.4, §17.3",
        "remaining_blockers": "JSON .remaining_blockers / MD §10, §16.5, §17.3",
        "source_hashes": "JSON .source_hashes (producer-recorded, audited copies, F15 umbrella) / "
                         "MD §1, §15.6, §17.5",
        "compile_evidence": "JSON .compile_evidence + .reverification_round2..10 + cold rebuilds / "
                            "MD §2, §15.1, §16.1, §18.1",
        "axiom_evidence": "JSON .axiom_evidence + negative control + forbidden scans / "
                          "MD §3, §14.5, §16.1, §18.1",
        "next_dependency_requests": "JSON .next_dependency_requests / MD §10, §16.5, §18.3",
        "elapsed_time": "JSON .elapsed_hours/.cumulative_task_hours / MD header",
    },
}

d["verdict"] = (
    "Round 10 (final close-out, invocation 7): the seven available D12 cards were rebuilt and "
    "re-audited an eighth consecutive time with byte-identical outputs (342 per-declaration "
    "axiom cones, 1103 full-namespace declarations PASS, negative control flags sorryAx and "
    "native_decide, snapshot and D2/D3 probes rc 0).  Across this invocation the audit added: "
    "(1) the round-7 fold-in (canonical 31-entry blocker-register cross-check, audit-of-the-"
    "auditor self-control with injected axiom/sorry/tautology defects, the F18 vacuity-screen "
    "blind spot); (2) round-8 evidence (7th byte-identical sweep, F18/F19 flag classification, "
    "a closure-consumption/wiring screen with 0 orphans, two new kernel probes — pp-artifact "
    "evidence for diam_rep_of_toGHSpace and canonical-type/factorization/van-Kampen-"
    "independence evidence for the SR-5 closure); (3) round-9 kernel assumption-as-conclusion "
    "screens (declared set, full 1104-constant Prop-gated namespace: 0 flags with the control "
    "flagged in all 7 packages, and the 1307-constant D2/D3 environment: 2 true positives, "
    "including the new finding A3-D2D3-9); (4) a pinned-upstream snapshot integrity check and "
    "an independent drift check.  7/9 cards are fully re-verified; 2/9 cards "
    "(D12-tensor-maximum-bochner, D12-triangulation-topology) remain source-absent on this "
    "host with no transport route (tcp 127.0.0.1:10022 refused, no tailscale 360 peer, no "
    "mounts, 0 named hits, re-checked 2026-09-11T16:43), so the 9-card milestone is BLOCKED, "
    "not refuted.  No unimplemented assumption is counted as a proof, no closure is claimed "
    "without a constructed downstream checked use, and no Perelman-level statement is claimed."
)

json.dump(d, open(RES_JSON, "w"), indent=1)
print("JSON updated")

# ---------------- markdown --------------------------------------------------
text = open(RES_MD).read()
if "## 18. " in text:
    text = text[:text.find("\n## 18. ")]
section = f"""
## 18. Final close-out (round 10, invocation 7)

### 18.1 Round-10 sweep — eighth consecutive byte-identical sweep

`audit360/run_round10.sh` → `audit360/logs-round10/`, summary
`audit360/round10_summary.json` (sha256 `{sha(os.path.join(HERE, 'round10_summary.json'))}`).
All seven available cards: `lake build`, `A3Probe`, `A3FullAudit`, `A3KindAudit` rc 0;
**342 cones, 1103 declarations, `A3FULL: PASS`**; every log byte-identical to round 8
(which was identical to round 7); negative control flags `sorryAx` and the private
`native_decide` axiom; snapshot build/probe rc 0; `a3d2d3` build/probe/round-3 rc 0; both
round-8 kernel probes (`PpArtifactCheck.lean`, `RegisterIdentity.lean`) rc 0.  The round-9
screens were re-run afterwards and their artifacts hash-compare equal to the recorded ones.

### 18.2 Final self-audit

| verifier | scope | result |
|---|---|---|
| `audit360/verify_own_hashes.py` | producer sources (4 schemas), audited copies, rounds 1-6 artifacts | 775 hashes, 0 mismatches, 0 unresolved |
| `audit360/verify_round8_hashes.py` | round-7/8 artifacts, probes, F18/F19 inputs, F15 umbrella | 612 hashes, 0 mismatches, 0 unresolved |
| `audit360/verify_round9_hashes.py` | round-9 screens, artifacts, D2/D3 finding | 27 hashes, 0 mismatches, 0 unresolved |
| `audit360/verify_round10_hashes.py` | round-10 close-out artifacts | see `audit360/self_audit_round10.json` |

The producer card files stayed frozen throughout (14/14 unchanged vs the round-4 freeze in
every re-check), and the pinned Frenzymath snapshot is intact (§17.5).

### 18.3 Deliverable field map

| required field | where | content |
|---|---|---|
| `proved_declarations` | JSON `.proved_declarations`; MD §2, §3 | 342 card-declared names across the 7 available cards; hash-verified producer sources, kernel-resolved, per-name axiom cones |
| `expanded_hypotheses` | JSON `.expanded_hypotheses`; MD §4, §11.8, §16.3 | expanded hypothesis bundles per card, with F12a phantom parameters and F12b redundant hypotheses recorded |
| `semantic_class` | JSON `.semantic_class` + `.semantic_class_corrections`; MD §6, §14.4, §16.3 | GENERAL / MODEL / CONDITIONAL / STATEMENT-ONLY classification per headline result, with corrections |
| `exact_blockers_closed` | JSON `.exact_blockers_closed` + `.exact_blockers_closed_audit`; MD §5, §15.2-15.3, §16.2, §16.4 | CC: LeviCivita existence **CONFIRMED** (canonical type identity + 7 independent consumers); SR: SR-5 **CONFIRMED**, I5/I6 **CONFIRMED-LOCAL**; wiring screen 0 orphans |
| `remaining_blockers` | JSON `.remaining_blockers`; MD §10, §16.5, §17.3 | per-card open items, mapped to the 31-entry canonical register; 2/9 cards unauditable |
| `source_hashes` | JSON `.source_hashes`; MD §1, §15.6, §17.5 | producer-recorded hashes (all schemas), audited-copy hashes incl. the F15 umbrella, upstream snapshot digest |
| `compile_evidence` | JSON `.compile_evidence` + `.reverification_round2..10`; MD §2, §15.1, §16.1, §18.1 | builds, cold rebuilds, probes, full-namespace audits, kind screens, drift check |
| `axiom_evidence` | JSON `.axiom_evidence`; MD §3, §14.5, §16.1 | per-declaration cones, negative controls (sorryAx, native_decide), forbidden-token scans |
| `next_dependency_requests` | JSON `.next_dependency_requests`; MD §10, §16.5, §18.4 | transport request first, then producer-side corrections |
| `elapsed` | JSON `.elapsed_hours`, `.cumulative_task_hours`; MD header | this invocation ≈2.1 h, cumulative ≈5.05 h |

### 18.4 Status and the exact blocker

**TASK_BLOCKED — 7/9 cards fully re-verified; 2/9 not auditable on this host.**

* `D12-tensor-maximum-bochner` (host 360-1) and `D12-triangulation-topology` (host 360-2)
  have no worktree, release package, card, Lean module, state directory or marker anywhere
  under the poincare root; 0 files named after either card under `/data3/guoshaoyang`
  (re-checked {miss10['checked_at']}).
* Transport: `tcp 127.0.0.1:10022` **refused**, `tailscale status` shows no 360-1/360-2
  peer, no NFS/CIFS/SSHFS mounts; `longrun/bin/relay_push.sh` (sha256
  `8328b9067e107ea97026bc3459c44fb15796f2ac1e45cb37fece9bc2c681e63f`) runs on the 360 host
  and cannot be driven from here.  The precursor D11 cards on this host are **not**
  substitutes and are not counted.
* This is a transport blocker, not a mathematical one.  No TASK_DONE is claimed; the
  milestone is not fully checked.

**A3 (named blocker):** *stale-as-stated / partially addressed.*  The audit now has seven
independent evidence layers on the D2/D3 lane (prior `VERIFIER-D7` card, compiled probe,
proof-cone screen, unused-binder screen, wide type screens, the kernel assumption-as-
conclusion screen with the new A3-D2D3-9 finding, and the canonical register mapping), but
the producer-side defects remain unrepaired and 2/9 cards cannot be audited here.
"""
open(RES_MD, "w").write(text.rstrip("\n") + "\n" + section.strip("\n") + "\n")
print("MD updated; sha256:", sha(RES_MD))
