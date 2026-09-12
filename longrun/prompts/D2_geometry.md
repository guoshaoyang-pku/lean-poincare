You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_geometry_foundation
Task id: D2-geometry-foundation

Consume the accepted D1 geometry result card. Build a compilable Stage 1/geometry cluster under `Poincare/Longrun/Geometry/`:

- a metric/inner-product data structure with explicit finite-dimensional assumptions;
- an abstract connection/curvature adapter compatible with the existing `Poincare.Stage1.CurvatureAlgebra`;
- at least two nontrivial checked lemmas about the adapter or contractions;
- an explicit `BLOCKED` interface for any missing Levi-Civita theorem.

Run a clean `lake env lean` on every authored file and `#print axioms` on the principal declarations. Never use `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`. Write a result card with exact commands and exit codes. Do not overwrite existing Stage1 files.