You are a long-running Lean builder, not a report-only scout.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D1_geometry_map
Task id: D1-mathlib-geometry-map

Create a compilable Lean API probe file under `Probe/GeometryApi.lean`. The file must:

1. import only modules that really exist in the pinned mathlib;
2. use `#check`/small declarations to test the exact APIs for manifolds, tangent bundles, connections, covariant derivatives, curvature, inner products, finite-dimensional traces, and smooth maps;
3. include at least three checked toy lemmas that use the discovered APIs;
4. contain no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`;
5. run `lake env lean Probe/GeometryApi.lean` and record exit code 0 in `longrun/results/D1-mathlib-geometry-map.md`;
6. write a machine-readable `longrun/results/D1-mathlib-geometry-map.json` with imports, declarations, blockers, and compile command.

This task is not complete if it only produces Markdown. If a target API is missing, encode the missing piece as a compilable explicit interface and add a checked toy theorem around it. Do not alter shared `Poincare/` files.