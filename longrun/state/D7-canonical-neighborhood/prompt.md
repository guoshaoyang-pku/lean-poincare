You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-canonical-neighborhood
Task id: D7-canonical-neighborhood
Scaffold: `cp -al ../D7-gh-compactness/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Canonical/`.
Goal: canonical neighborhood interface.
1. Define epsilon-neck, cap and `CanonicalNeighborhoodCertificate` data over the D7 curvature and compactness layers.
2. Prove kernel-checked: instance checks for the stated model spaces (round sphere and round cylinder interfaces); a classification toy showing the certificate excludes a stated degenerate model.
3. State-only Prop for Perelman's canonical neighborhood theorem with named missing inputs.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-canonical-neighborhood.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
