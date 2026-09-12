You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-tensor-laplacian
Task id: D7-tensor-laplacian
Scaffold: `cp -al ../D7-hamilton-short-time/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/TensorLaplacian/`.
Goal: tensor Laplacian and evolution identities.
1. Define rough Laplacian interface on tensor data over the D7 connection layer.
2. Prove kernel-checked: commutation formula in a finite-dimensional model under a stated curvature certificate; and the scalar-curvature evolution identity `∂ₜ scal = Δ scal + 2|Ric|²` as an exact identity between interface fields under a stated flow equation.
3. State-only Props for the smooth commutation formulas with missing dependencies.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-tensor-laplacian.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
