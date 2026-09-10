#!/usr/bin/env python3
import argparse
import json
from pathlib import Path
import shutil
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--host", required=True, choices=["ophis-gpu", "360-1", "360-2"])
parser.add_argument("--render-only", action="store_true")
args = parser.parse_args()
root = Path(__file__).resolve().parent.parent
plan = json.loads((root / "D12-plan.json").read_text())
tasks = []
all_ids = [item["id"] for item in plan["tasks"]]
for item in plan["tasks"] + plan["followup"]:
    task_id = item["id"]
    owned = item["host"] == args.host
    if not owned and args.host != "ophis-gpu":
        continue
    followup = task_id.startswith("D13-")
    task = {"id": task_id, "stage": task_id.split("-")[0], "host": item["host"], "lane": "auditor" if followup or "ledger" in task_id else "builder", "status": "queued", "deps": [], "requires_lean": True, "max_hours": 72, "max_rounds": 24, "blockers": item.get("blockers", []), "acceptance": "compiled_only_until_independent_semantic_review"}
    if followup:
        task["after_terminal"] = all_ids if task_id == "D13-integrated-kernel-audit" else ["D13-integrated-kernel-audit"]
    tasks.append(task)
    if not owned:
        continue
    module = item.get("module", "IntegratedAudit" if "kernel" in task_id else "CriticalPathReview")
    worktree = root / "worktrees" / task_id
    prompt = f"""Task id: {task_id}
Worktree: {worktree}
Model: {plan['model']}; use the configured minimal preset and max effort. Never switch model silently.

You own a long-horizon research-and-implementation track, not a one-response toy demonstration. Decide the proof architecture yourself within this scope. Work incrementally for up to 72 wall-clock hours, with four-hour invocations, hourly durable checkpoints and a maximum of 24 invocations. The 72 hours is a resource cap, not a claimed proof ETA. Do not sleep to fill time. Complete early only when the intended milestone is genuinely proved and audited, or report the exact irreducible blocker with useful partial Lean lemmas.

Objective:
{item['objective']}

Work only in this isolated worktree. The existing release/ directory is the Lean package. Build from release/, not the parent. Read D7/D10/D11 sources, available result cards, the pinned mathlib source and LONG_PLAN.json. The snapshot may include preliminary dependencies: rebuild before relying on them. Do NOT re-scaffold, delete imported modules, modify tests, change the toolchain, edit global queues/settings, overwrite another worker, or commit/push. Add authored Lean files under release/Poincare/{task['stage']}/{module}/ and a task-local audit module. If an upstream definition is wrong, create a versioned corrected definition plus proved compatibility in your directory instead of silently changing the target. Published claims remain historical unless your fresh checks cover them.

Milestones:
- By the first checkpoint: exact target statement, dependency search, choice of approach, and a compiling first lemma or reproducible failing Lean goal.
- At 12 hours: a useful nontrivial lemma with full type and proof dependencies; classify it as model, conditional or general.
- At 24 hours: downstream use or a concrete subproblem split with the exact missing statement; preserve progress in checkpoint.json.
- At 72 hours: independently reproducible deliverable or honest blocked report. A missing theorem is not a new axiom.

Hard acceptance rules:
No sorry, axiom, admit, unsafe, native_decide, proof_wanted, fake propositions, zero operators masquerading as geometry, or hypotheses equivalent to the conclusion. Do not weaken the objective to pass the gate. A Lean proof of H -> C does not establish H. Standard regularity/domain hypotheses are allowed but must be expanded and justified for the claimed application. Prove a concrete nondegenerate example when necessary to test non-vacuity. Research classical mathematics is not the same as discovering a new mathematical theorem.

Run lake build with the relevant targets and lake env lean on authored files. Provide #print axioms plus a fail-closed programmatic axiom audit for every new declaration, allowing only propext, Classical.choice, Quot.sound. Report fresh source hashes, full declarations and compile commands/cwd/exits. Separate kernel trust, compilation, statement correctness and closure of a named blocker. No claimed blocker closure without a constructor of that missing input and a downstream checked use.

Reuse compatible open-source libraries where useful. Record exact source URL/revision, license and modifications. Do not copy admitted proofs or claim that an absent symbol name proves the underlying mathematics is absent. No upstream pull requests or external messages without supervisor approval.

Collaboration: consume the preloaded source snapshot and write explicit dependency requests in checkpoint.json. Never poll the dispatcher waiting for your own acceptance. Later audit workers consume your task artifacts after relay. No shared mutable proof files.

Deliver longrun/results/{task_id}.md and .json inside this worktree. JSON must contain proved_declarations, expanded_hypotheses, semantic_class, exact_blockers_closed, remaining_blockers, source_hashes, compile_evidence, axiom_evidence, next_dependency_requests and actual elapsed time. An empty closed-blockers list is legitimate. End your own markdown result card with exactly TASK_DONE if all intended milestone claims hold, or TASK_BLOCKED if only partial results are obtained. A TASK_DONE card is only a request for independent acceptance, never a claim that Perelman is proved.
"""
    (root / "prompts" / f"{task_id}.md").write_text(prompt)
    if args.render_only:
        continue
    if not worktree.exists():
        worktree.mkdir()
        baseline = root / "worktrees/D6_weekly_release"
        subprocess.run(["rsync", "-a", "--exclude=.lake/", "--exclude=.git/", "--exclude=logs/", str(baseline) + "/", str(worktree) + "/"], check=True)
        overlay = root / "integrated_overlay"
        if overlay.is_dir():
            subprocess.run(["rsync", "-a", "--exclude=.lake/", "--exclude=.git/", str(overlay) + "/", str(worktree) + "/"], check=True)
        lake = worktree / "release/.lake"
        lake.mkdir(exist_ok=True)
        packages = baseline / "release/.lake/packages"
        if not packages.is_dir():
            raise RuntimeError("Baseline mathlib packages missing")
        (lake / "packages").symlink_to(packages, target_is_directory=True)
    shutil.copy2(root / "D12-plan.json", worktree / "LONG_PLAN.json")
    print("PREPARED", task_id, flush=True)
inbox = root / "inbox"
inbox.mkdir(exist_ok=True)
output = inbox / "D12-longplan.json"
temporary = output.with_suffix(".tmp")
temporary.write_text(json.dumps({"tasks": tasks, "max_concurrent": plan.get("capacity_by_host", {}).get(args.host, 6)}, indent=2) + "\n")
temporary.replace(output)
print("QUEUED", len(tasks), "host", args.host, flush=True)
