You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-orientability-volume-form
Task id: D7-orientability-volume-form
Scaffold: `cp -al ../D7-ricci-scalar-curvature/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Volume/`.
Goal: orientability + volume-form algebra layer.
1. Define `VolumeFormData` on an oriented finite-dimensional inner-product space; prove kernel-checked scaling law `vol(c•g) = c^(n/2) vol(g)` via an explicit determinant interface, and orientation-reversal sign law.
2. Prove a checked finite-dimensional change-of-variables lemma for linear maps with nonzero determinant.
3. State-only Props: existence and smoothness of the Riemannian volume form on an oriented smooth manifold; list exact missing mathlib dependencies (manifold measure theory).
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-orientability-volume-form.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
