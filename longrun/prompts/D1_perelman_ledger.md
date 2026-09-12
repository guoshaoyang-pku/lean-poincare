You are a long-running Lean builder and theorem-ledger author.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D1_perelman_ledger
Task id: D1-perelman-ledger

Use Morgan–Tian and Perelman’s papers as mathematical sources, but every deliverable must include Lean code. Create:

1. `Ledger/PerelmanDefinitions.lean`: compilable explicit interfaces for metric flow data, volume form, scalar curvature, F/W-style functionals, and monotonicity hypotheses. Use structures and propositions with all assumptions visible; do not assert false existence.
2. `Ledger/DefinitionSmoke.lean`: imports the definitions and proves at least three nontrivial type-level/toy lemmas.
3. `longrun/results/D1-perelman-ledger.md`: theorem ledger mapping major Perelman steps to Lean interfaces, dependencies, and blockers.
4. `longrun/results/D1-perelman-ledger.json`: machine-readable theorem DAG.

Run `lake env lean` on both Lean files and record exit code 0 and `#print axioms` for the toy declarations. No `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`. Do not edit shared `Poincare/` files.