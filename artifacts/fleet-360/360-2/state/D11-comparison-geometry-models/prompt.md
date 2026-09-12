You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-comparison-geometry-models
Task id: D11-comparison-geometry-models
Worktree is PRE-SCAFFOLDED with the integrated D1–D10 codebase. Do NOT re-scaffold. Add files only under `release/Poincare/D11/ComparisonModels/`.
Goal: model-space comparison geometry, building on D10-jacobi-constant-curvature.
1. Define the three constant-curvature model metrics in polar form `dr² + j_K(r)² g_{S^{n-1}}` with the D10 Jacobi solutions j_K; verify the warped-product metric axioms reduce to the ODE conditions already proved.
2. Prove unconditionally the Bishop–Gromov volume comparison at the ODE level: `r ↦ vol(B_K(r))/vol(B_K^model(r))` is monotone non-increasing — for explicit j_K this is a real-analytic monotonicity statement; prove via derivative sign computation.
3. Prove the Laplacian comparison `Δr ≤ (n-1) j_K'(r)/j_K(r)` in the model case (explicit radial computation, unconditional).
4. `#print axioms` only `[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D11-comparison-geometry-models.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
