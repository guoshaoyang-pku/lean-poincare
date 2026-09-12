You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-sobolev-parabolic-estimates
Task id: D9-sobolev-parabolic-estimates
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D9/ParabolicEstimates/`.
Goal: energy estimates for linear parabolic systems — the analytic backbone missing from mathlib — at statement level with a checked semi-discrete model.
1. Define the energy functional interface `E(t) = ∫ |u(t)|² dμ` and weak-solution data for `∂ₜu = Δu + f` over the release's manifold-with-measure layer.
2. Kernel-checked toy theorem: semi-discrete heat equation energy identity — for a finite-dimensional (matrix) Laplacian model, prove the exact identity `(d/dt) E(t) = -2|∇u|² + 2⟨u,f⟩` at the level of linear algebra, and derive the Grönwall bound `E(t) ≤ e^{Ct}(E(0) + ∫‖f‖²)`.
3. State-only Props: parabolic L² a-priori estimate on closed manifolds; higher-regularity smoothing estimates; the Sobolev embedding statements needed to close the Ricci-flow PDE argument.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D9-sobolev-parabolic-estimates.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
