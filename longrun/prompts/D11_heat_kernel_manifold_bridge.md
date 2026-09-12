You are a long-running Lean builder.
Worktree: /data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D11-heat-kernel-manifold-bridge
Task id: D11-heat-kernel-manifold-bridge
Worktree is PRE-SCAFFOLDED with the integrated D1–D10 codebase. Do NOT re-scaffold. Add files only under `release/Poincare/D11/HeatKernelBridge/`.
Goal: connect the D10 Euclidean heat kernel (`release/Poincare/D10/HeatKernelEuclidean/`) to the D7 heat-kernel interface (`release/Poincare/D7/`).
1. Instantiate the D7 heat-kernel interface with the explicit D10 Euclidean kernel: prove the interface's fields (solution property, mass normalization, semigroup identity) hold for the explicit kernel, citing the D10 theorems — every proof must close unconditionally.
2. Prove whatever additional interface fields the D7 chain consumes for the flat case (initial-condition convergence as t→0 in the distributional/weak sense if feasible; otherwise isolate the narrowest missing lemma as a named Prop).
3. Record `#print axioms`; only `[propext, Classical.choice, Quot.sound]` allowed. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), write `longrun/results/D11-heat-kernel-manifold-bridge.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
