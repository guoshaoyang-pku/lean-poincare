You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-discrete-continuous-limit
Task id: D7-discrete-continuous-limit
Scaffold: `cp -al ../D7-heat-kernel-existence/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Limit/`.
Goal: discrete-to-continuous consistency bridge.
1. Define a consistency certificate between the D2 finite-grid heat evolution and the continuous heat interface.
2. Prove kernel-checked: an explicit error-recursion bound on the discrete slab with computable constants (finite-dimensional); stability of the recursion under a stated CFL condition.
3. State-only convergence theorem with exact missing dependencies (compactness, regularity).
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-discrete-continuous-limit.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
