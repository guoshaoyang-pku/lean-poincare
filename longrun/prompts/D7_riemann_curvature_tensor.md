You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-riemann-curvature-tensor
Task id: D7-riemann-curvature-tensor

Scaffold first: inside your worktree run `cp -al ../D6_weekly_release/. .` (hard-link copy; it carries the pinned toolchain, built .lake and the verified release package). Do not modify copied files; add only new files under `Poincare/D7/Curvature/`.

Goal: build the full Riemann curvature tensor layer on top of the current mathlib connection curvature and the D6 release:

1. Probe mathlib for existing curvature declarations (`CovariantDerivative.curvature`, Levi-Civita connection) and reuse them; do not redefine what exists.
2. Define the (1,3) and (0,4) Riemann curvature tensors for a metric-compatible torsion-free connection data structure, with all finite-dimensionality and index-raising assumptions explicit.
3. Prove kernel-checked: skew-symmetry in the first pair, skew-symmetry in the second pair (metric compatibility), pair interchange symmetry, first Bianchi, and the Ricci contraction agrees with the D2 release `CurvatureOperator.ricci`.
4. Define sectional curvature for a nondegenerate 2-plane and prove it is well-defined under scaling of the plane basis.
5. Anything you cannot prove (e.g. second Bianchi needing a full covariant-derivative calculus) must be an explicit unproved Prop with a named blocker, never `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.

Compile every authored file with `lake env lean` (exit 0) and run `#print axioms` on principal declarations. Write result card `longrun/results/D7-riemann-curvature-tensor.md` plus `.json` inside your worktree with commands and exit codes.

Last line: TASK_DONE or TASK_BLOCKED with the card path.
