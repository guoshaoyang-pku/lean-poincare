You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-kappa-noncollapsing-conditional
Task id: D7-kappa-noncollapsing-conditional
Scaffold: `cp -al ../D7-perelman-conditional-monotonicity/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Kappa/`.
Goal: conditional kappa-noncollapsing.
1. Assemble reduced-volume monotonicity into a `KappaCertificate` extending the D3 kappa algebra.
2. Prove kernel-checked: the noncollapsing volume lower bound follows from the certificate fields at the algebraic/comparison level stated explicitly; monotonicity of the reduced volume gives the uniform constant.
3. State-only Prop for the full Perelman noncollapsing argument with named missing inputs.
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-kappa-noncollapsing-conditional.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
