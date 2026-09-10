Task id: D12-semantic-ledger
Worktree: /Users/guoshaoyang/Desktop/workdir/math/lean_poincare/longrun/worktrees/D12-semantic-ledger
Model: deepseek-v4-pro; use the configured minimal preset and max effort. Never switch model silently.

You own a long-horizon research-and-implementation track, not a one-response toy demonstration. Decide the proof architecture yourself within this scope. Work incrementally for up to 72 wall-clock hours, with four-hour invocations, hourly durable checkpoints and a maximum of 24 invocations. The 72 hours is a resource cap, not a claimed proof ETA. Do not sleep to fill time. Complete early only when the intended milestone is genuinely proved and audited, or report the exact irreducible blocker with useful partial Lean lemmas.

Objective:
Independent adversarial audit of the available D1-D11 snapshot. Enumerate each claimed main-chain theorem, expand all certificate/record fields, classify as model, conditional, statement-only, or genuine general theorem. Validate D11 heat test-function defect and D7 recognition assumptions. Recount blockers from evidence: do not repeat '22 blockers' or claim research-level new mathematical discoveries. Produce machine-readable ledger with full declaration types, source hashes, axiom cones, precise dependencies and which inputs were actually constructed. Add a Lean audit module that checks relevant declarations; never weaken or modify builder sources. Existing historical audit manifests must not be presented as current.

Work only in this isolated worktree. The existing release/ directory is the Lean package. Build from release/, not the parent. Read D7/D10/D11 sources, available result cards, the pinned mathlib source and LONG_PLAN.json. The snapshot may include preliminary dependencies: rebuild before relying on them. Do NOT re-scaffold, delete imported modules, modify tests, change the toolchain, edit global queues/settings, overwrite another worker, or commit/push. Add authored Lean files under release/Poincare/D12/SemanticLedger/ and a task-local audit module. If an upstream definition is wrong, create a versioned corrected definition plus proved compatibility in your directory instead of silently changing the target. Published claims remain historical unless your fresh checks cover them.

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

Deliver longrun/results/D12-semantic-ledger.md and .json inside this worktree. JSON must contain proved_declarations, expanded_hypotheses, semantic_class, exact_blockers_closed, remaining_blockers, source_hashes, compile_evidence, axiom_evidence, next_dependency_requests and actual elapsed time. An empty closed-blockers list is legitimate. End your own markdown result card with exactly TASK_DONE if all intended milestone claims hold, or TASK_BLOCKED if only partial results are obtained. A TASK_DONE card is only a request for independent acceptance, never a claim that Perelman is proved.
