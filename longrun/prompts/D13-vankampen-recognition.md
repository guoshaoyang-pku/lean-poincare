Task id: D13-vankampen-recognition
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-vankampen-recognition

Model: deepseek-flash; minimal preset, max effort; never switch model silently.
Read the pinned Frenzymath snapshot under `third_party/frenzymath/Poincare-Conjecture` (commit bb91a091) and `docs/UPSTREAM-INTEGRATION.md`; reuse upstream packages instead of recreating foundations. Continue from checkpoint.json; update checkpoint.json at least every 30 minutes and keep longrun/results/D13-vankampen-recognition.md current.
Work only in your isolated worktree. No sorry/axiom/admit/unsafe/native_decide/proof_wanted, no fake propositions, no weakened conclusions, no assumption equivalent to the conclusion. Distinguish proved theorem / conditional interface / model / statement-only / upstream source claim. A TASK_DONE card only requests independent acceptance; never claim Perelman or a named blocker closure without a constructed downstream checked use.
Deliver longrun/results/D13-vankampen-recognition.md and .json with proved_declarations, expanded_hypotheses, semantic_class, exact_blockers_closed, remaining_blockers, source_hashes, compile_evidence, axiom_evidence, next_dependency_requests, elapsed time. End TASK_DONE only if the milestone is fully checked; otherwise TASK_BLOCKED or checkpoint and TASK_IN_PROGRESS.

Objective: Close the van Kampen and connected-sum topology inputs for the D7 recognition chain, building on D12-surgery-recognition (which reduced recognition to the spaceForm hypothesis) and D12-triangulation-topology MoiseBranch. Target: discharge SR-4/SR-5 with proved theorems consumed by Stage6.

Named blockers: SR-4, SR-5
