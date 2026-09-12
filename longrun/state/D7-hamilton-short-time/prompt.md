You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-hamilton-short-time
Task id: D7-hamilton-short-time
Scaffold: `cp -al ../D7-ricci-scalar-curvature/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/ShortTime/`.
Goal: Hamilton 1982 short-time existence layer, kept honest.
1. Define `RicciFlowData` and `DeTurckCertificate` (gauge vector field, modified flow equation) with all fields explicit.
2. Prove kernel-checked: equivalence of Ricci flow and Ricci-DeTurck flow at the algebraic level under the stated gauge transform, in a finite-dimensional matrix-ODE model; uniqueness of the ODE system under a Lipschitz interface.
3. State-only Props: parabolic short-time existence for the DeTurck flow and its conversion back to Ricci flow; list missing dependencies (quasilinear parabolic theory).
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-hamilton-short-time.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
