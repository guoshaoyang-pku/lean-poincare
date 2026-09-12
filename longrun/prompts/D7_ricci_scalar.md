You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-ricci-scalar-curvature
Task id: D7-ricci-scalar-curvature

Scaffold first: inside your worktree run `cp -al ../D7-riemann-curvature-tensor/. .` if that worktree exists and passed its gate, otherwise `cp -al ../D6_weekly_release/. .` (hard-link copy). Do not modify copied files; add only new files under `Poincare/D7/RicciScalar/`.

Goal: Ricci and scalar curvature as genuine contractions of the D7 Riemann tensor:

1. Define Ricci as the trace of the (1,3) curvature over a finite-dimensional basis and scalar curvature as the metric trace of Ricci; prove basis-independence of both traces.
2. Prove kernel-checked: symmetry of Ricci for a metric-compatible torsion-free connection data; compatibility with the D2 release `CurvatureOperator.ricci`; scalar curvature of a product interface equals the sum of factor scalars for a stated product structure.
3. Provide the variation interface: state-only Props for `d/dt scal(g(t))` under a stated flow equation, with exact missing dependencies (evolution of Levi-Civita, commutation of time derivative and trace).
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.

Compile every authored file with `lake env lean` (exit 0), record `#print axioms`, write `longrun/results/D7-ricci-scalar-curvature.md` + `.json`.

Last line: TASK_DONE or TASK_BLOCKED with the card path.
