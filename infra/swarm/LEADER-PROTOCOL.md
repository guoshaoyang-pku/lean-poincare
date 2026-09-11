# Mathematical group-leader protocol

A leader is a long-lived research task with its own workspace under `worktrees/leaders/<id>`. It does not edit another worker's worktree or `main`. It maintains `checkpoint.json`, a `comms/` directory, and a dated research brief every 30 minutes.

Each leader owns a narrow mathematical lane and may create child task descriptions in `comms/outbox/`; the dispatcher imports only tasks with explicit IDs, dependencies, acceptance criteria and a named worktree. Leaders must separate proved, conditional, model and statement-only results.

The integrator is the only process allowed to merge source into the publication branch. A leader may commit and push its own branch/checkpoint, but never force-push or rewrite another branch.

## Initial leaders

- `L1-lean-baseline`: clean build, declaration/axiom manifest, queue/evidence reconciliation.
- `L2-upstream-adapters`: build and classify Frenzymath packages on their pinned toolchain.
- `L3-analytic-critical-path`: heat kernel, parabolic regularity, DeTurck producer.
- `L4-geometric-critical-path`: manifold volume/IBP, geodesics, compactness.
- `L5-topology-audit`: recognition, triangulation, surgery interfaces and adversarial audit.

Leaders use the configured dsh credential reference on the host. Credentials are never copied into worktrees, prompts or Git.
