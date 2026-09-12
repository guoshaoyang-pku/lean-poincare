You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-perelman-conditional-monotonicity
Task id: D7-perelman-conditional-monotonicity
Scaffold: `cp -al ../D7-reduced-length-volume/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Monotonicity/`.
Goal: conditional Perelman F/W monotonicity assembly.
1. Consume the D7 Bochner, conjugate-heat and reduced-volume certificates; assemble a conditional monotonicity theorem for F and W using the D3 `EntropyData` composition lemmas.
2. Prove kernel-checked: monotonicity under the explicit certificate hypotheses; identify precisely which hypotheses remain open and name each.
3. No new axioms; open inputs stay as hypotheses.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-perelman-conditional-monotonicity.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
