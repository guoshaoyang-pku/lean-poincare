You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D9-ancient-kappa-solutions
Task id: D9-ancient-kappa-solutions
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D9/AncientKappa/`.
Goal: ancient solutions, κ-solutions, and soliton interfaces for the singularity-analysis part of the Ricci-flow program.
1. Define interfaces: ancient solution (flow on `(-∞, 0]` with bounded curvature on compact subintervals), κ-noncollapsing at all scales, gradient shrinking soliton structure as interface fields.
2. Kernel-checked toy theorem: the Gaussian shrinking soliton on `R^n` — verify the soliton equation `Ric + Hess(f) = (1/2)g` for `f = |x|²/4` by explicit Euclidean computation (Hessian computed exactly in Lean; `Ric = 0` for flat space available or stated via interface).
3. State-only Props: classification of 3-dimensional κ-solutions (round cylinder and its quotients, Bryant steady soliton, asymptotic soliton statement); Perelman's compactness theorem for the space of κ-solutions; the canonical-neighborhood linkage statement.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D9-ancient-kappa-solutions.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
