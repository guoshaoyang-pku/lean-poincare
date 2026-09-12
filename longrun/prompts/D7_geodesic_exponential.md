You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-geodesic-exponential
Task id: D7-geodesic-exponential

Scaffold first: inside your worktree run `cp -al ../D6_weekly_release/. .` (hard-link copy). Do not modify copied files; add only new files under `Poincare/D7/Geodesic/`.

Goal: geodesic / exponential-map layer:

1. Probe mathlib for `Geodesic`, `exp`, second-order ODE existence on manifolds; record exactly what exists with paths.
2. Where mathlib has geodesics but no exponential map or no existence theorem, define an explicit `GeodesicData` interface (connection, initial point/velocity, solution curve) with all hypotheses visible.
3. Prove kernel-checked toy theorems: uniqueness of geodesics with given initial data in a flat/affine model; constant-speed property under metric compatibility for the interface; and that reparametrization by an affine map preserves the geodesic equation for the interface.
4. State-only (clearly named) interfaces for: existence of geodesics on complete manifolds, Hopf–Rinow, and exponential map being a local diffeomorphism; each with its exact missing dependency listed.
5. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.

Compile every authored file with `lake env lean` (exit 0), record `#print axioms`, write `longrun/results/D7-geodesic-exponential.md` + `.json`.

Last line: TASK_DONE or TASK_BLOCKED with the card path.
