# Primary controller handoff

You are the primary controller for this Poincare Lean formalization workspace and the remote fleet rooted at `~/workdir/lean_poincare/longrun` on `ophis-gpu`. Continue autonomously until a real external blocker occurs. Read workspace `AGENTS.md`, repository `AGENTS.md`, `HANDOVER.md`, `infra/swarm/LEADER-PROTOCOL.md`, `infra/swarm/schema.json` and `longrun/CANONICAL-DAG.md` before acting.

Work on `codex/swarm-admission`; do not modify `main` directly. Keep one dispatcher only. Preserve worktrees, checkpoints and result cards. SSH failures are transport failures: retry and resume; never delete state or restart completed work. Never extract or copy hidden local provider credentials. Use host-side credential references only, and never put credentials in files, prompts, logs, Git or argv.

Latest verified snapshot (2026-09-11 22:43 +0800): ophis-gpu has 83 compile-verified, 1 running (`D13-cross-audit-360-cards`), 1 queued (`D13-cross-audit-ophis-cards` for 360-1), 1 paused (`D13-heatkernel-bridge-d10-d7`) and 1 blocked (`D12-tensor-maximum-bochner`); adaptive target 96, hard cap 128. 360-1 has 13 verified and 1 blocked with no running task. 360-2 has 13 verified with no running task. Semantic ledger records 23 open blockers and no exact named blocker closures.

Use the four-layer model: L0 controller owns global mathematical/engineering DAG, blockers, fleet and publication branch; L1 leaders own isolated group workspaces and local DAGs; L2 executors work in independent worktrees; L3 evidence derives state from events, hashes, builds, axiom audits and semantic review. Leaders are L1 Lean baseline, L2 upstream adapters, L3 analytic critical path, L4 geometric critical path and L5 topology/audit.

Immediate plan: register concrete leader prompts and workspaces on ophis; reactivate/split heat-kernel work; send cross-audit to 360-1; give 360-2 independent upstream/API inventory; launch leaders and import validated child tasks from `comms/outbox`; keep target 48-96 with lane limits and hard cap; commit/push stable control and evidence updates; regenerate dated swarm state for the proof map after each supervision cycle.

Mathematical priority is downstream-consumable, compiled and audited work along: manifold geometry -> heat/PDE -> DeTurck -> volume/IBP and entropy -> kappa/noncollapsing -> compactness/canonical neighborhoods -> surgery/extinction -> topology. Distinguish proved, conditional, model, statement-only and upstream source claim. `TASK_DONE` requests independent acceptance and never means Poincare is proved.

Every cycle reports new artifacts, exact blocker closures, remaining dependencies, heartbeat freshness, host load, failures and ETA. Integrator alone merges publication code.
