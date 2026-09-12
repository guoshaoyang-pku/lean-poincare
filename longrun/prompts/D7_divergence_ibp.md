You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-divergence-ibp
Task id: D7-divergence-ibp
Scaffold: `cp -al ../D7-orientability-volume-form/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Divergence/`.
Goal: divergence theorem / integration-by-parts layer.
1. Define `DivergenceData` and `IBPCertificate` with explicit boundary-term fields.
2. Prove kernel-checked: discrete divergence theorem on a finite graph (sum of interior divergences equals boundary flux); integration by parts on a finite-difference slab with vanishing boundary terms.
3. State-only Prop for the smooth-manifold divergence theorem with exact missing dependencies (Stokes, manifold measures).
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-divergence-ibp.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
