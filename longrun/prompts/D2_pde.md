You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D2_pde_foundation
Task id: D2-pde-foundation

Consume the accepted D1 PDE probe. Build `Poincare/Longrun/PDE/` with:

- a finite-grid heat evolution structure;
- a fully checked discrete maximum principle;
- a monotonicity/energy toy theorem whose assumptions and sign conventions are explicit;
- a named statement-only interface for the continuous maximum principle, plus a separate checked toy theorem.

Every Lean file must compile with `lake env lean`; record `#print axioms`; do not use `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`. Write a result card and do not modify shared Stage1/Stage2 files.