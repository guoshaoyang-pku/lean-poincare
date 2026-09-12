You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-conjugate-heat-interface
Task id: D7-conjugate-heat-interface
Scaffold: `cp -al ../D7-divergence-ibp/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/ConjugateHeat/`.
Goal: conjugate heat equation layer.
1. Define `ConjugateHeatData`: backward heat operator with scalar-curvature term, over a stated metric-flow interface.
2. Prove kernel-checked: formal adjointness of heat and conjugate-heat operators at the algebraic level under an explicit IBP certificate; a discrete conjugate-heat slab monotonicity toy.
3. State-only Prop for conjugate heat kernel existence with missing dependencies.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-conjugate-heat-interface.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
