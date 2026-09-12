You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-gaussian-toolbox
Task id: D10-gaussian-toolbox
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D10/GaussianToolbox/`.
Goal: a fully-proved Gaussian integral toolbox — the computational substrate for heat-kernel and PDE work.
1. Prove unconditionally from mathlib's Gaussian integral: moments `∫ x^{2n} exp(-x²) dx` for small n (0,1,2,3) with exact closed forms; scaling `∫ exp(-a x²) dx = √(π/a)` for a>0.
2. Prove unconditionally: 1D convolution of two Gaussians is a Gaussian with added variances (full computation; if a measure-theoretic lemma is missing, isolate the narrowest one as a named hypothesis and finish everything else).
3. Prove unconditionally: the n-dimensional Gaussian factors as a product of 1D integrals (Fubini via mathlib), total mass 1.
4. Record `#print axioms`; unconditional theorems must show ONLY `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D10-gaussian-toolbox.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
