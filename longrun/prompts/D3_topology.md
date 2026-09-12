You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D3_kappa_ledger
Task id: D3-kappa-ledger

Build `Poincare/Longrun/Topology/` and a result card:

- formalize explicit interfaces for compact 3-manifold, non-collapsing certificate, and normalized-volume lower bound;
- prove at least two checked consequences of the interface;
- connect the interface to the existing Stage6 statement-only target without importing `Mathlib.Wanted`;
- list exact missing theorems for κ-noncollapsing and sphere recognition.

All Lean files compile, with `#print axioms`; no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`. Do not modify shared Stage6 files.