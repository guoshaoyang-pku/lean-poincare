Task id: D13-cross-audit-ophis-cards
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards

Model: deepseek-flash; minimal preset, max effort; never switch model silently.
Read the pinned Frenzymath snapshot under `third_party/frenzymath/Poincare-Conjecture` (commit bb91a091) and `docs/UPSTREAM-INTEGRATION.md`; reuse upstream packages instead of recreating foundations. Continue from checkpoint.json; update checkpoint.json at least every 30 minutes and keep longrun/results/D13-cross-audit-ophis-cards.md current.
Work only in your isolated worktree. No sorry/axiom/admit/unsafe/native_decide/proof_wanted, no fake propositions, no weakened conclusions, no assumption equivalent to the conclusion. Distinguish proved theorem / conditional interface / model / statement-only / upstream source claim. A TASK_DONE card only requests independent acceptance; never claim Perelman or a named blocker closure without a constructed downstream checked use.
Deliver longrun/results/D13-cross-audit-ophis-cards.md and .json with proved_declarations, expanded_hypotheses, semantic_class, exact_blockers_closed, remaining_blockers, source_hashes, compile_evidence, axiom_evidence, next_dependency_requests, elapsed time. End TASK_DONE only if the milestone is fully checked; otherwise TASK_BLOCKED or checkpoint and TASK_IN_PROGRESS.

Objective: Independently re-verify the ophis-produced D12 result cards (heat-semigroup, parabolic-local-existence, entropy-variation, kappa-variational, heat-domain-repair): rebuild each named module set from its card source hashes, re-run the axiom audits and negative controls, and confirm/refute the exact_blockers_closed lists. Adversarial audit lane (A3).

Named blockers: A3
