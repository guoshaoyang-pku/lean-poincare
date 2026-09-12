You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-surgery-neck-extinction
Task id: D7-surgery-neck-extinction
Scaffold: `cp -al ../D7-canonical-neighborhood/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/SurgeryFlow/`.
Goal: surgery with necks and extinction, interface level.
1. Define `SurgeryProcedureData` consuming canonical neighborhoods; extend the D3 surgery ledger.
2. Prove kernel-checked: surgery times form a discrete set with no accumulation point under a stated curvature-bound interface; extinction for the finite toy complexity relation (reuse D3 `toyRel` results).
3. State-only Props for full neck analysis, a-priori curvature estimates and extinction theorem with named missing inputs.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-surgery-neck-extinction.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
