You are a long-running Lean builder.
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-maximum-principle-tensor
Task id: D11-maximum-principle-tensor
Worktree is PRE-SCAFFOLDED with the integrated D1–D10 codebase. Do NOT re-scaffold. Add files only under `release/Poincare/D11/TensorMaximumPrinciple/`.
Goal: Hamilton's tensor maximum principle, building on D10-maximum-principle-rn and D9-parabolic-maximum-principle.
1. Define the tensor reaction-diffusion system interface and the PC (positive-cone / null-eigenvector) condition on the reaction term.
2. Prove the finite-dimensional (matrix ODE) version unconditionally: for a symmetric-matrix-valued ODE system satisfying the PC condition, the positive-semidefinite cone is preserved — full proof via eigenvalue perturbation at the first touching time.
3. Attack the Euclidean PDE version using the D10 scalar maximum principle componentwise; prove what closes, isolate the narrowest missing analysis as named Props.
4. `#print axioms` must show only `[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D11-maximum-principle-tensor.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
