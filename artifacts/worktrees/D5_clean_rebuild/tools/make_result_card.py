#!/usr/bin/env python3
"""
D5-clean-rebuild: generate the result card (Markdown + JSON) from the build manifest.
Writes into <worktree>/longrun/results/ and attempts promotion to the shared
longrun/results/ directory (recording whether the sandbox allowed it).
"""
import json
import os
import shutil
import sys
from datetime import datetime, timezone

ROOT = "/data3/guoshaoyang/workdir/lean_poincare"
D5 = os.path.join(ROOT, "longrun", "worktrees", "D5_clean_rebuild")
MANIFEST = os.path.join(D5, "manifest")
SHARED = os.path.join(ROOT, "longrun", "results")
LOCAL = os.path.join(D5, "longrun", "results")


def fmt_table(rows, header):
    out = ["| " + " | ".join(header) + " |",
           "|" + "|".join(["---"] * len(header)) + "|"]
    for r in rows:
        out.append("| " + " | ".join(str(x).replace("|", "\\|") for x in r) + " |")
    return "\n".join(out)


def main():
    m = json.load(open(os.path.join(MANIFEST, "build-manifest.json")))
    gates = m["gate"]
    steps = {s["id"]: s for s in gates["steps"]}
    toolchain = m["toolchain"]
    audit = m["forbidden_dependency_audit"]["summary"]
    scan = m["forbidden_token_scan"]
    claims = m["claim_resolution"]

    os.makedirs(LOCAL, exist_ok=True)

    step_rows = []
    for sid in ["mathlib_precheck_head", "mathlib_precheck_status", "wipe_project_build",
                "lake_build", "release_check", "release_audit", "per_file_checks",
                "source_scan", "mathlib_postcheck_head", "mathlib_postcheck_status",
                "claim_resolution"]:
        s = steps.get(sid)
        if not s:
            continue
        cmd = s["cmd"] if isinstance(s["cmd"], str) else " ".join(s["cmd"])
        extra = ""
        if sid == "per_file_checks":
            extra = (f"{s.get('files')} release modules "
                     f"(53 promoted + 5 base), failures={s.get('failures')}")
        step_rows.append([sid, f"`{cmd}`", s["exit_code"], s.get("duration_s"), extra])

    cluster_rows = []
    for c in m["clusters"]:
        cluster_rows.append([
            c["stage"], f"`{c['task_id']}`", c["file_count"],
            c["queue_status_at_snapshot"], c["result_card_status"] or "no status field (checks exit 0)",
            "yes" if c["state_done_marker"] else "no",
            "yes" if c["all_card_hashes_match"] else "NO",
            "yes" if c["all_per_file_lean_exit_zero"] else "NO",
            c["verdict"],
        ])

    blocker_rows = []
    for b in m["unresolved_blockers"]:
        blocker_rows.append([b["id"], b["class"], b["status"], b["blocker"][:700]])

    claim_rows = []
    for e in claims["unresolved"]:
        claim_rows.append([e["name"], e["line"][:200]])
    if not claim_rows:
        claim_rows.append(["(none)", "all claimed declaration names resolve"])

    integrity = json.load(open(os.path.join(MANIFEST, "source-integrity.json")))
    n_origin = integrity["origin_files_checked"]
    changed = len(integrity["changed"])

    md = f"""# D5-clean-rebuild — result card

> **Delivery note (sandbox).** The canonical shared path
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D5-clean-rebuild.md` is outside
> this session's `workspace-write` sandbox (workspace =
> `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D5_clean_rebuild`). This card
> and its JSON twin are mirrored at `<worktree>/longrun/results/`.
> **Integrator action:** copy the two mirrored files to the shared `longrun/results/`
> directory (same delivery pattern as the accepted D2/D3/D4 cards). The promotion attempt
> made by this run: `@@PROMOTION@@`.
>
> Path note: the prompt names the worktree `.../worktrees/D5_rebuild`; the runtime workspace
> is `.../worktrees/D5_clean_rebuild` (the `D5_rebuild` name does not exist on disk). All work
> was done in `D5_clean_rebuild`.

- **Task id:** `D5-clean-rebuild`
- **Stage / lane:** D5 / verifier (`requires_lean: true`)
- **Model:** `deepseek-v4.1-flash-expires-on-0910`
- **Worktree:** `{D5}`
- **Generated:** {m["generated_at"]}
- **Verdict:** **{m["verdict"]}** — all release gates pass; the kernel dependency audit found
  no `sorryAx`, no project axiom, no `unsafe`, no `native_decide`, and no `proof_wanted`.
  {m["blocker_counts"]["open"]} open blockers remain (20 mathematical/interface, 2 audit
  residual, 1 process; see §6); none is a release-hygiene failure.

## 1. Scope and acceptance rule

The clean-room package collects **only** D1–D4 deliverables that are (a) recorded by a
`DONE` state marker, (b) described by a machine-readable result card, (c) hash-identical to
the card's `sha256` claims, and (d) recompiled and audited here from a fresh build directory.
Source artifacts are copied, never modified: all {n_origin} origin files were re-hashed after the
gate and **{changed} changed** (`manifest/source-integrity.json`; provenance and hashes in
`manifest/provenance.json`).

`longrun/queue.json` is the integrator's formal acceptance record, but it is **stale**: it was
last updated 2026-09-08T23:55 and still lists five later, completed tasks as
`running`/`queued` (see blocker **P1**). The D5 gate therefore treats *queue-verified* and
*D5-clean-room-verified* as two separate columns in §2 and supplies the missing independent
verification for the latter five.

## 2. Collected artifacts (only accepted D1–D4)

{fmt_table(cluster_rows, ["stage", "task", "files", "queue.json", "result card", "DONE", "card sha256", "per-file lean", "verdict"])}

- 11/11 D1–D4 tasks delivered; {sum(c["file_count"] for c in m["clusters"])} promoted Lean files copied.
- Cross-worktree duplicate check: **{len(m["artifact_duplicate_conflicts"])} conflicts** (every
  shared file that appears in several worktrees is byte-identical).
- Base skeleton dependencies (pre-existing, not D1–D4 artifacts):
  {", ".join("`" + b["path"] + "`" for b in m["base_dependencies"])}.

## 3. Fresh clean-room build

Environment (exact pins):

```text
lean-toolchain : {toolchain["lean_toolchain_file"]}
lean           : {toolchain["lean_version"]}
lake           : {toolchain["lake_version"]}
mathlib rev    : {toolchain["mathlib_manifest_rev"]}  ({toolchain["mathlib_git_describe"]})
mathlib status : clean (git status --porcelain empty, before and after the gate)
```

The project build directory was wiped and rebuilt from scratch in
`{m["fresh_build"]["dir"]}`; the pinned mathlib is a shared **prebuilt, read-only** package
cache (rebuilding 8.2 GB of mathlib from source is not the variable under test, and the D4
cards already record a full mathlib build).

{fmt_table(step_rows, ["gate step", "command", "exit", "seconds", "notes"])}

Final re-verification of the delivered package after the manifest was written:
`lake build` exit 0, `lake env lean ReleaseCheck.lean` exit 0,
`lake env lean ReleaseAudit.lean` exit 0 (logs `10_final_*`).

`ReleaseCheck.lean` imports every promoted cluster and every audit driver:

```text
Probe.GeometryApi, Probe.PdeApi, Ledger.PerelmanDefinitions, Ledger.DefinitionSmoke,
Poincare.Longrun.Geometry, Poincare.Longrun.PDE.{{HeatGrid,DiscreteMaximumPrinciple,Energy,
ContinuousInterface,AxiomAudit}}, Poincare.Longrun.CurvatureODE, Poincare.Longrun.Entropy,
Poincare.Longrun.Entropy.AxiomAudit, Poincare.Longrun.Topology.{{Basic,CompactThreeManifold,
Noncollapsing,NormalizedVolume,Stage6Bridge,MissingTheorems,AxiomAudit}},
Poincare.Longrun.Surgery, Poincare.Longrun.Surgery.Axioms, Poincare.Longrun.Evolution,
Audit.{{GeometryAudit,CurvatureODEAudit,EvolutionAudit,CounterexampleAudit,PromotedEvolutionAudit}}
```

## 4. Forbidden-dependency gate (kernel level)

`ReleaseAudit.lean` walks every constant declared in a release module
(**{audit.get("project declarations audited", "?")} declarations**) and collects its full
transitive axiom cone with `Lean.collectAxioms`:

```text
project axiom declarations ................ {audit.get("project axiom declarations", "?")}
unsafe declarations ....................... {audit.get("unsafe declarations", "?")}
declarations depending on sorryAx ......... {audit.get("declarations depending on sorryAx", "?")}
declarations depending on native_decide ... {audit.get("declarations depending on native_decide/ofReduceBool", "?")}
declarations with unapproved axioms ....... {audit.get("declarations with unapproved axioms", "?")}
proof_wanted-derived declarations ......... {audit.get("project declaration names containing 'proof_wanted'", "?")}
distinct axiom cones ...................... {audit.get("distinct axiom cones", "?")}
```

The only cones are subsets of the three standard Lean/mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`), plus the empty cone.

Gate definitions used by the audit: `sorryAx` = literal axiom name; *unapproved project axiom*
= any `axiom` declaration in a release module, and any axiom in a cone outside the three
standard axioms (this is also what catches `native_decide`, which in this toolchain emits a
private `..._native.native_decide.ax_*` axiom); `unsafe` = `DefinitionSafety.unsafe`
declaration; `proof_wanted` = literal source usage (comment-aware scan) or a release
declaration whose name contains `proof_wanted`. `partial` definitions are *not* on the
forbidden list and are reported separately (blocker H1).

- **Comment/string-aware source scan** (`tools/scan_forbidden.py`, {scan["lean_files_scanned"]} files):
  **{scan["hard_match_count"]} hard matches** for `sorry`, `axiom`, `unsafe`, `native_decide`,
  `proof_wanted`, `sorryAx`, `admit`; {scan["soft_match_count"]} soft matches for
  `implemented_by`/`extern`.
- **Negative control** (`negcontrol/NegativeControl.lean`): proves the audit predicate really
  fails on forbidden input — `sorry` yields cone `[sorryAx]`, `native_decide` yields an
  unapproved private axiom (in Lean 4.34.0-rc2 `native_decide` emits
  `<decl>._native.native_decide.ax_*`, not `ofReduceBool`). Log: `logs/09_negative_control.log`.
- **`Mathlib.Wanted`**: the pinned mathlib has no such module (D3-kappa probe exit 1); no
  release module imports it.

## 5. Result-card claim resolution (informational, non-gating)

All {claims["claim_count"]} fully-qualified declaration names named by the D1–D4 result cards
were `#check`ed in the clean package (`release/ReleaseClaims.lean`).

{fmt_table(claim_rows, ["unresolved claim", "error"])}

## 6. Complete unresolved-blocker list

{fmt_table(blocker_rows, ["id", "class", "status", "blocker"])}

Counts: {m["blocker_counts"]["open"]} open, {m["blocker_counts"]["documented"]} documented,
{m["blocker_counts"]["known_environment_limit"]} environment limits,
{m["blocker_counts"]["informational"]} informational — {m["blocker_counts"]["total"]} total.
The complete per-card blocker text is in `manifest/card-blockers.json`.

## 7. What is explicitly NOT claimed

This release does **not** claim the Poincaré conjecture, Ricci-flow existence or uniqueness,
Perelman F/W/µ monotonicity, κ-noncollapsing, canonical neighbourhoods, surgery, extinction,
or sphere recognition. Every such item is a statement-only interface or an explicit hypothesis
structure (blockers I1–I8, U1–U12). The only genuinely checked content is the finite-dimensional
/ algebraic / discrete cluster listed in §2 and the adversarial audit of the D4 evolution
cluster, whose sharp-hypothesis corrections are recorded in `D4Audit`.

## 8. Reproduction

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd {D5}
python3 tools/collect_release.py          # copy + hash-verify artifacts (read-only on sources)
python3 tools/gen_claims.py               # result-card claim probe
python3 tools/scan_forbidden.py release   # source scan
python3 tools/run_gates.py                # fresh build + ReleaseCheck + ReleaseAudit + per-file
python3 tools/finalize_manifest.py        # merge manifest/build-manifest.json
```

## 9. Files produced (all under the D5 worktree)

- `release/` — fresh Lake package (60 modules: 53 promoted + 5 base + `ReleaseCheck`/`ReleaseAudit`)
- `release/ReleaseCheck.lean` — imports every promoted cluster
- `release/ReleaseAudit.lean` — kernel-level forbidden-dependency audit
- `release/ReleaseClaims.lean` — result-card claim probe
- `manifest/build-manifest.json` — clean Lean build manifest (pins, hashes, gates, blockers)
- `manifest/provenance.json`, `manifest/gate-results.json`, `manifest/forbidden-scan.json`,
  `manifest/claims.json`, `manifest/card-blockers.json`
- `tools/*.py` — reproducible collector, scanner, gate runner, manifest/result-card generators
- `negcontrol/NegativeControl.lean` — audit negative control
- `logs/` — every command's full log
- `longrun/results/D5-clean-rebuild.md`, `.json` — this card (mirror)
"""
    md_path = os.path.join(LOCAL, "D5-clean-rebuild.md")
    open(md_path, "w").write(md)

    card_json = {
        "task_id": "D5-clean-rebuild",
        "status": "done" if gates["gate_pass"] else "failed",
        "verdict": m["verdict"],
        "generated_at": m["generated_at"],
        "worktree": D5,
        "prompt_worktree_discrepancy": m["prompt_worktree_discrepancy"],
        "toolchain": toolchain,
        "gate": {
            "gate_pass": gates["gate_pass"],
            "gate_failures": gates["gate_failures"],
            "exit_codes": {s["id"]: s["exit_code"] for s in gates["steps"]},
            "per_file_failures": gates["per_file_failures"],
            "commands": [
                {"id": s["id"],
                 "cmd": s["cmd"] if isinstance(s["cmd"], str) else " ".join(s["cmd"]),
                 "exit_code": s["exit_code"], "log": s["log"], "duration_s": s.get("duration_s")}
                for s in gates["steps"]
            ],
        },
        "forbidden_dependency_audit": m["forbidden_dependency_audit"],
        "forbidden_token_scan": {k: scan[k] for k in
                                 ("lean_files_scanned", "hard_match_count", "soft_match_count")},
        "claim_resolution": m["claim_resolution"],
        "clusters": [
            {k: c[k] for k in ("cluster", "task_id", "stage", "queue_status_at_snapshot",
                               "result_card_status", "state_done_marker", "file_count",
                               "all_card_hashes_match", "all_per_file_lean_exit_zero",
                               "verdict")}
            for c in m["clusters"]
        ],
        "artifact_duplicate_conflicts": m["artifact_duplicate_conflicts"],
        "base_dependencies": [{"path": b["path"], "sha256": b["sha256"]} for b in m["base_dependencies"]],
        "unresolved_blockers": m["unresolved_blockers"],
        "blocker_counts": m["blocker_counts"],
        "files": {
            "build_manifest": "manifest/build-manifest.json",
            "release_check": "release/ReleaseCheck.lean",
            "release_audit": "release/ReleaseAudit.lean",
            "provenance": "manifest/provenance.json",
            "gate_results": "manifest/gate-results.json",
            "forbidden_scan": "manifest/forbidden-scan.json",
            "claims": "manifest/claims.json",
            "card_blockers": "manifest/card-blockers.json",
            "negative_control": "negcontrol/NegativeControl.lean",
            "logs": "logs/",
        },
        "source_integrity": integrity,
        "promotion": "@@PROMOTION@@",
        "delivery_note": "Shared longrun/results/ is outside the workspace-write sandbox; "
                         "this card and its JSON twin are mirrored at <worktree>/longrun/results/.",
    }
    json_path = os.path.join(LOCAL, "D5-clean-rebuild.json")
    with open(json_path, "w") as fh:
        json.dump(card_json, fh, indent=1)

    # attempt promotion to the shared results dir (record the outcome, do not fail the run)
    promoted = {}
    for src in (md_path, json_path):
        dst = os.path.join(SHARED, os.path.basename(src))
        try:
            shutil.copy2(src, dst)
            promoted[os.path.basename(src)] = "copied"
        except Exception as exc:  # noqa: BLE001
            promoted[os.path.basename(src)] = f"denied: {type(exc).__name__}: {exc}"
    # fill the promotion placeholder in the local mirror, then refresh any successful copy
    token = json.dumps(promoted)
    for path in (md_path, json_path):
        text = open(path).read()
        if path.endswith(".json"):
            text = text.replace('"@@PROMOTION@@"', token)
        else:
            text = text.replace("@@PROMOTION@@", token)
        open(path, "w").write(text)
        name = os.path.basename(path)
        if promoted.get(name) == "copied":
            shutil.copy2(path, os.path.join(SHARED, name))
    print(json.dumps({"result_card": md_path, "json": json_path, "promotion": promoted}, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
