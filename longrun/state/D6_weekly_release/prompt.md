You are the integrator for the one-week release.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D6_release
Task id: D6-weekly-release

Consume only accepted D5 artifacts. Produce:

- a weekly release manifest;
- a theorem/dependency ledger;
- a list of verified Lean declarations;
- a list of explicit blockers for the full Perelman proof;
- the next 20 queued builder tasks.

Every claimed theorem must point to a compiling `.lean` file and axiom report. Do not claim the Poincare conjecture, Ricci-flow existence, Perelman monotonicity, or surgery are proved unless the kernel and clean-room verifier demonstrate it. Write a release result card.