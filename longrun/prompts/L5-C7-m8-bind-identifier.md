Task id: L5-C7-m8-bind-identifier
Group: L5-topology-audit
Worktree: worktrees/L5-C7-m8-bind-identifier
Lane: integrator
Model: none required (provider-independent control-plane task)

Objective:
Reconcile the orphaned M8 identifier. The L5 leader registry names M8, while the blocker manifest previously had no explicit M8 entry. Inspect longrun/CANONICAL-DAG.md, longrun/leader-registry.json, manifest/blockers.json, manifest/blockers.md, and the L5 semantic review card.

Acceptance:
- Produce a result card under longrun/results/L5-C7-m8-bind-identifier.md and .json.
- Bind M8 to a canonical manifest entry with id, class, status, evidence and next dependency requests, or document a justified rename/removal.
- Preserve M8 as open and statement-only: it is the topological-recognition/Poincare-conclusion node and has no unconditional formal proof.
- Keep exact_blockers_closed empty. The registry reconciliation is an engineering/control-plane result, not a mathematical blocker closure.
- Record source paths and hashes for changed control-plane files, and report that no Lean source was changed and no credentials were accessed.
- End the markdown card with TASK_DONE only after the files are internally consistent; otherwise end TASK_BLOCKED and preserve partial evidence.

Dependencies (preserve as provenance; do not collapse to fake queue IDs):
- longrun/manifest/blockers.json (D5/D6)
- longrun/leader-registry.json

Forbidden:
Do not edit main, weaken theorem semantics, add axioms/sorry/admit/unsafe/native_decide/proof_wanted, claim Poincare completion, or relabel the remote queue row as verified without independent acceptance.
