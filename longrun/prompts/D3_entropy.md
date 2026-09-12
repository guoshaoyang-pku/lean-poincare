You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_entropy_interface
Task id: D3-entropy-interface

Consume accepted D2 geometry and PDE result cards. Build `Poincare/Longrun/Entropy/`:

- define a measure/metric-flow-compatible interface for an F/W-style functional;
- define a monotonicity certificate with all analytic assumptions explicit;
- prove at least two checked algebraic consequences of the certificate;
- write a statement-only bridge marking the missing integration-by-parts/regularity theorems.

Every authored `.lean` file must pass `lake env lean`; include `#print axioms`; no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`. Write a result card. Do not call the interface a Perelman proof.