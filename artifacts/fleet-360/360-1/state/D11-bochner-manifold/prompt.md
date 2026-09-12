You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-bochner-manifold
Task id: D11-bochner-manifold
Worktree is PRE-SCAFFOLDED with the integrated D1–D10 codebase. Do NOT re-scaffold. Add files only under `release/Poincare/D11/BochnerManifold/`.
Goal: the Bochner–Weitzenböck identity WITH the curvature term, connecting D10-bochner-euclidean to D7-bochner-weitzenbock.
1. Restate the Euclidean Bochner identity from D10 and prove the curvature-term correction at the level of constant-coefficient models: `Δ‖∇u‖² = 2‖Hess u‖² + 2⟨∇u,∇Δu⟩ + 2Ric(∇u,∇u)` — prove it unconditionally in the explicit constant-curvature model (sphere/hyperbolic normal coordinates reduced to radial ODE computation, or finite-dimensional algebraic curvature model).
2. Prove the corollary chains used by the Ricci-flow program: Ric ≥ 0 implies subharmonicity of energy density; Ric ≥ K gives the gradient-estimate differential inequality.
3. `#print axioms` must show only `[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D11-bochner-manifold.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
