Task id: L1-child-queue-verdict-gate
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L1-child-queue-verdict-gate
Model: use configured host model only.

Objective: Implement the F4 finding of the L1 baseline as an executable gate: a script that joins longrun/queue.json against the result cards on disk and fails closed when a task marked verified has no card, a verified task's card verdict is blocked/failed, or a task's queue status lags a TASK_DONE card. Emit the report in the L1 reconciliation schema and run it as the pre-promotion check for the next release.

Acceptance: Constructed input: `queue-verdict-gate.py` with a documented exit-code contract (0 clean, 1 flags) and JSON output. Downstream consumer: the next release integrator runs it before promotion; the gate is invoked on the current queue. Independent rebuild: run against (a) the live queue and (b) a synthetic queue/card fixture containing one verified-without-card, one verified-but-blocked and one lagging entry, which must all be flagged. Semantic review: card lists the four default `verified`-semantics flags, states that queue status is not evidence of soundness, and ends TASK_DONE/TASK_BLOCKED.

Work only in this isolated worktree. Do not edit queue.json or another worktree. Preserve all partial artifacts and checkpoint.json. No sorry, axiom, admit, unsafe, native_decide, proof_wanted or weakened theorem statements. Classify results as proved, conditional, model, statement-only or upstream source claim. End the result card with TASK_DONE or TASK_BLOCKED; this is independent acceptance, never a Poincare proof.
