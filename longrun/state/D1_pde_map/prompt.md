You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D1_pde_map
Task id: D1-pde-api-map

Build a compilable `Probe/PdeApi.lean` against the pinned mathlib. Probe exact APIs for:

- continuous/differentiable functions;
- first and second derivatives;
- interval compactness and extrema;
- finite grids, recurrences, and order structures;
- any existing maximum-principle or heat-equation declarations.

Write at least four checked toy lemmas, including one strict finite-grid maximum principle. If the continuous PDE API is absent, write a compilable interface with explicit hypotheses and a separate finite-grid theorem. No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.

Run `lake env lean Probe/PdeApi.lean` with exit code 0. Write:
- `longrun/results/D1-pde-api-map.md`
- `longrun/results/D1-pde-api-map.json`

Do not edit shared `Poincare/` files.