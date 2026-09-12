You are a long-running Lean builder.
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D10-maximum-principle-rn
Task id: D10-maximum-principle-rn
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `release/Poincare/D10/MaximumPrincipleRN/`.
Goal: the weak maximum principle for the heat equation on bounded domains of ℝⁿ, attacking a FULL unconditional proof.
1. Define subsolutions of the heat equation on `Ω × (0,T]` with Ω bounded, and the parabolic boundary.
2. Attempt the full classical proof (the `u - εt` trick): a subsolution attains its maximum on the parabolic boundary. Prove every analytic step available in mathlib; if a specific analytic lemma is genuinely missing, isolate it as a narrowly-scoped named hypothesis (never the whole theorem) and prove everything downstream of it.
3. Kernel-checked fallback theorem (required regardless): the ODE/semidiscrete comparison lemma in finite dimensions, fully proved.
4. Record `#print axioms`; unconditional theorems must show ONLY `[propext, Classical.choice, Quot.sound]`.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D10-maximum-principle-rn.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
