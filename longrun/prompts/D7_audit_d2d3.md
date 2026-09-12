You are an adversarial Lean verifier.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/VERIFIER-D7-adversarial-audit-d2d3
Task id: VERIFIER-D7-adversarial-audit-d2d3

Scaffold first: inside your worktree run `cp -al ../D6_weekly_release/. .` (hard-link copy). Do not modify copied files; add only new files under `AuditD2D3/`.

Goal: independently attack the promoted D2 and D3 clusters (geometry identities, discrete maximum principle, ODE invariants, entropy certificates, kappa algebra, surgery ledger):

1. For each headline theorem, write a verifier file that imports only the release interfaces and re-proves or re-derives the statement from first principles where feasible.
2. Search for counterexamples to weakened hypotheses (small finite grids, 1- and 2-dimensional states, degenerate metrics, zero volumes); every counterexample must be a compiling Lean example.
3. Flag vacuous statements (hypotheses never satisfiable) with a compiling proof of unsatisfiability, or prove non-vacuity with an explicit witness.
4. Check sign and index conventions against standard references and record mismatches.
5. Verifier files compile with `lake env lean` (exit 0); no `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.

Write `longrun/results/VERIFIER-D7-adversarial-audit-d2d3.md` + `.json` with per-theorem verdicts: CONFIRMED / OVERSTRONG / VACUOUS / CONVENTION_MISMATCH / COUNTEREXAMPLE, each with evidence file paths.

Last line: TASK_DONE or TASK_BLOCKED with the card path.
