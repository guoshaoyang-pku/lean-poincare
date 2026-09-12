Task id: D13-upstream-adapter-audit
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-upstream-adapter-audit
Model: deepseek-flash; use the configured minimal preset and max effort. Never switch model silently.

You are a coordination/integration task on ophis-gpu. Read the pinned Frenzymath snapshot in `third_party/frenzymath/Poincare-Conjecture`, the local D12 result cards and `docs/UPSTREAM-INTEGRATION.md`. Your job is to produce a precise, compile-checked adapter plan and, where feasible, a small Lean compatibility module that maps local D12 objectives to upstream modules. Continue from checkpoint.json if present. Update checkpoint.json at least every 30 minutes and keep longrun/results/D13-upstream-adapter-audit.md current.

Objective blockers: A1, A2, A3, P1, P5

Work only in this isolated worktree. Do not modify other workers, tests, toolchain, queue or negative controls. No sorry, axiom, admit, unsafe, native_decide, proof_wanted, fake propositions, weakened conclusions, or assumptions equivalent to the conclusion. Distinguish upstream compiled theorem, upstream source claim, conditional adapter, and local proved theorem. A TASK_DONE card is only a request for independent acceptance.

Deliver longrun/results/D13-upstream-adapter-audit.md and .json with proved_declarations, expanded_hypotheses, semantic_class, exact_blockers_closed, remaining_blockers, source_hashes, compile_evidence, axiom_evidence, next_dependency_requests and elapsed time. End with TASK_DONE only if the claimed milestone is fully checked; otherwise TASK_BLOCKED.
