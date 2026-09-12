You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-jacobi-constant-curvature
Task id: D10-jacobi-constant-curvature
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D10/JacobiConstantCurvature/`.
Goal: Jacobi fields and comparison estimates in constant sectional curvature, with FULL unconditional proofs.
1. Define the scalar Jacobi ODE `j'' + K·j = 0` with parameter K, and its explicit solutions: sin(√K t)/√K for K>0, t for K=0, sinh(√-K t)/√-K for K<0.
2. Prove unconditionally: each explicit formula satisfies the ODE with initial conditions j(0)=0, j'(0)=1 (verify by `deriv` computation in Lean, all steps checked).
3. Prove unconditionally the Rauch-type comparison at the ODE level: if K₁ ≤ K₂ then the corresponding solutions satisfy j₂ ≤ j₁ up to the first zero of j₂ (Sturm comparison for these explicit functions; prove via monotonicity of explicit formulas where possible, else isolate the narrowest missing analysis lemma as a named hypothesis).
4. Record `#print axioms`; unconditional theorems must show ONLY `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D10-jacobi-constant-curvature.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
