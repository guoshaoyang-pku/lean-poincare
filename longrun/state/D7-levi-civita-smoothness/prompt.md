You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-levi-civita-smoothness
Task id: D7-levi-civita-smoothness

Scaffold first: inside your worktree run `cp -al ../D7-riemann-curvature-tensor/. .` if that worktree exists and passed its gate, otherwise `cp -al ../D6_weekly_release/. .` (hard-link copy). Do not modify copied files; add only new files under `Poincare/D7/LeviCivita/`.

Goal: smoothness and functoriality layer for the Levi-Civita connection:

1. Probe mathlib's current Levi-Civita declarations (PR #36845 lineage) and record exactly which smoothness statements exist.
2. For the D7 curvature data, prove kernel-checked: the mean connection of two metric-compatible connections is metric-compatible; the difference tensor of two torsion-free connections is symmetric; smoothness of the connection coefficients interface under a stated chart-smoothness hypothesis.
3. State-only Props for full Levi-Civita existence on a smooth Riemannian manifold and for `CovariantDerivative.curvature` matching the D7 (1,3) tensor, each with exact missing mathlib dependencies.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.

Compile every authored file with `lake env lean` (exit 0), record `#print axioms`, write `longrun/results/D7-levi-civita-smoothness.md` + `.json`.

Last line: TASK_DONE or TASK_BLOCKED with the card path.
