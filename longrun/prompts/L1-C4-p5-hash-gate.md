Task id: L1-C4-p5-hash-gate
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L1-C4-p5-hash-gate
Model: use configured host model only.

Objective: Turn the P5 source-hash re-check into an executable fail-closed release gate

Acceptance: Constructed input: a script `release-hash-gate.py` that takes a previous 64-hex hash manifest and a release root and fails closed on any changed/removed pre-existing file, emitting added/changed/removed lists as JSON. Downstream consumer: the L1 result card's manifest and the next release integrator's acceptance command. Independent rebuild: run the gate against the current release (must report 462/462 match vs the D13 manifest) and against a mutated temporary copy (must fail and name the mutated file). Semantic review: a card documents that P5 (re-run the hash check on every future release) now has an executable gate; P5 itself stays open as a recurring obligation. Card ends TASK_DONE/TASK_BLOCKED.

Work only in this isolated worktree. Do not edit queue.json or another worktree. Preserve all partial artifacts and checkpoint.json. No sorry, axiom, admit, unsafe, native_decide, proof_wanted or weakened theorem statements. Classify results as proved, conditional, model, statement-only or upstream source claim. End the result card with TASK_DONE or TASK_BLOCKED; this is independent acceptance, never a Poincare proof.
