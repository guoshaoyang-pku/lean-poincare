Task id: L1-C1-independent-axiom-replay
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/L1-C1-independent-axiom-replay
Model: use configured host model only; do not invoke until quota recovery is recorded.

Objective: Independent replay of the L1 baseline axiom/dependency audit via a different tool path

Acceptance: Fresh worktree, pinned toolchain leanprover/lean4:v4.34.0-rc2 and mathlib 7974e751bece493b6ff508039423ca9fa2452fa8. (a) Rebuild release/ clean and confirm exit 0. (b) Reconstruct the import-disjoint partition independently (or re-derive the collision set from .ilean first principles) and re-audit every built module with an independent collector path (e.g. per-declaration `#print axioms` text parsing rather than Lean.collectAxioms). (c) Report per-declaration cones for at least 99% of the L1 inventory; every mismatch must be listed with its expected/observed cone. (d) Confirm exactly 3 expected negative-control flags and 0 unexpected unapproved axioms, or report the delta. (e) Card under longrun/results/ ending TASK_DONE/TASK_BLOCKED; no Poincare claim. The replay must not read L1's axiom-audit.json as an oracle for its own verdicts.

Work only in this isolated worktree. Do not edit queue.json or another worktree. Preserve partial artifacts and checkpoint.json. Authored Lean must contain no sorry, axiom, admit, unsafe, native_decide, proof_wanted or weakened theorem. Classify results as proved, conditional, model, statement-only or upstream source claim. Run compile and axiom gates when admitted. End the card with TASK_DONE or TASK_BLOCKED; this is independent acceptance, never a Poincare proof.
