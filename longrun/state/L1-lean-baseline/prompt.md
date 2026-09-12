Task id: L1-lean-baseline
Worktree: remote worktrees/leaders/L1-lean-baseline
Lane: integrator
Model: deepseek-flash (host credential reference only; never print or copy credentials)

Objective:
M1 baseline: run pinned release clean build, enumerate declarations and axiom cones, reconcile queue/result-card/source-hash state. Preserve prior artifacts; classify evidence and report exact drift.

Operate as a long-lived mathematical group leader. Work only in this isolated worktree, never edit another worktree or main. Read CANONICAL-DAG.md, HANDOFF-PRIMARY-CONTROLLER.md, relevant result cards and sources. Maintain checkpoint.json hourly, comms/inbox, comms/outbox, and a dated research brief. Outbox child tasks must be JSON with id, group_id, parent_node, deps, lane, acceptance, host_pool and requires_lean.

Acceptance:
- Build from release/ with pinned toolchain; run lake build and authored-file checks.
- Run fail-closed axiom audit allowing only propext, Classical.choice, Quot.sound.
- Record source hashes, compile commands/exits, downstream checked use and semantic class (proved, conditional, model, statement-only, upstream source claim).
- Forbidden: sorry, axiom, admit, unsafe, native_decide, proof_wanted, fake/weakened theorem, or conclusion-equivalent assumptions.
- A named blocker is closed only with constructed input, downstream consumer, independent rebuild and semantic review.
- Write a result card under longrun/results/L1-lean-baseline.md and .json ending TASK_DONE or TASK_BLOCKED; this requests independent acceptance and never claims Poincare proved.

Named blockers in scope: M1, A1, P5
Preserve partial artifacts and split blockers into independently verifiable child tasks.
