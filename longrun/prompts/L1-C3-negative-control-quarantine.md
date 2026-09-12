Task id: L1-C3-negative-control-quarantine
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L1-C3-negative-control-quarantine
Model: use configured host model only; do not invoke until quota recovery is recorded.

Objective: Quarantine the two in-package negative-control axioms so the release passes a strict no-axiom scan

Acceptance: Constructed input: relocate the two intentional negative controls (`d12NegControlBadAxiom` + `d12NegControlBadTheorem`, `negativeControl`) out of the release library globs into an audit-only directory (or an explicitly manifested exclusion file), with the detector self-test still exercising them. Downstream consumer: the L1 forbidden scan and the L1/G1+G2 axiom audit re-run against the moved layout. Independent rebuild: fresh `lake build` in release/ exits 0 and the union-import partition still audits every module. Semantic review: a card under longrun/results/ documents that (a) declaration-form forbidden hits in release/ are now 0, (b) the negative-control detector still fires on the quarantined copies, (c) no proof declaration's cone changed. Card ends TASK_DONE/TASK_BLOCKED.

Work only in this isolated worktree. Do not edit queue.json or another worktree. Preserve partial artifacts and checkpoint.json. Authored Lean must contain no sorry, axiom, admit, unsafe, native_decide, proof_wanted or weakened theorem. Classify results as proved, conditional, model, statement-only or upstream source claim. Run compile and axiom gates when admitted. End the card with TASK_DONE or TASK_BLOCKED; this is independent acceptance, never a Poincare proof.
