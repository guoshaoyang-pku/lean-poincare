You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-gh-compactness
Task id: D7-gh-compactness
Scaffold: `cp -al ../D7-kappa-noncollapsing-conditional/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Compactness/`.
Goal: pointed Gromov-Hausdorff / Cheeger-Gromov compactness interface.
1. Define `GHConvergenceData` and a precompactness certificate for families of pointed metric spaces.
2. Prove kernel-checked: a toy compactness theorem for finite metric-space families by explicit enumeration; total-boundedness consequences of the certificate fields.
3. State-only Props for Cheeger-Gromov convergence of manifold families with missing dependencies.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-gh-compactness.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
