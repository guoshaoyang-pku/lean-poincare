You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-reduced-length-volume
Task id: D7-reduced-length-volume
Scaffold: `cp -al ../D7-hamilton-short-time/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Reduced/`.
Goal: reduced length / reduced volume layer.
1. Define L-length functional data over a stated metric-flow interface, with minimizer existence as an explicit hypothesis where needed.
2. Prove kernel-checked: algebraic monotonicity consequences of the reduced-volume certificate fields; and an explicit computation of reduced length for the finite-dimensional Gaussian shrinking soliton model.
3. State-only Props for minimizer existence and Jacobian comparison with missing dependencies.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-reduced-length-volume.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
