You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-bochner-formula
Task id: D7-bochner-formula
Scaffold: `cp -al ../D7-divergence-ibp/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Bochner/`.
Goal: Bochner/Weitzenbock layer.
1. Define `BochnerCertificate`: 1-form Laplacian = rough Laplacian + Ricci contraction, as explicit fields.
2. Prove kernel-checked: the Euclidean instance (Ricci = 0) where the identity reduces to Laplacian commutation; and a gradient-estimate toy: under a `Ricci ≥ 0` certificate field, `Δ(|∇f|²) ≥ 2|Hess f|²` holds in the stated finite-dimensional model.
3. State-only Prop for the smooth Bochner formula with missing dependencies.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-bochner-formula.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
