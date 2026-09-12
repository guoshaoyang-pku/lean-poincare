You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-heat-kernel-existence
Task id: D7-heat-kernel-existence
Scaffold: `cp -al ../D7-conjugate-heat-interface/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/HeatKernel/`.
Goal: heat kernel interface layer.
1. Define `HeatKernelData` with Gaussian upper/lower bound fields and semigroup properties as explicit fields.
2. Prove kernel-checked: uniqueness of a heat kernel satisfying stated bounds on a finite grid; monotonicity of discrete heat content.
3. State-only Prop for heat kernel existence on closed manifolds with missing dependencies (parabolic regularity, Sobolev).
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-heat-kernel-existence.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
