You are a long-running Lean builder.

Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-evolution-sharp-restatement
Task id: D7-evolution-sharp-restatement

Scaffold first: inside your worktree run `cp -al ../D6_weekly_release/. .` (hard-link copy). Do not modify copied files; add only new files under `Poincare/D7/EvolutionSharp/`.

Goal: consume the D4 adversarial audit. The audit found three promoted theorems with overstrong hypotheses and provided sharp replacements (`D4Audit.gibbsTerm_strictAnti_of_one_le`, `D4Audit.gibbsTerm_step_lt_of_one_le`, `D4Audit.perelmanF_step_lt_of_one_le`).

1. Restate the D4 evolution cluster theorems under the weakest hypotheses the audit proved sufficient.
2. Prove kernel-checked implication lemmas: old statement follows from new statement plus the discarded hypothesis, and the new statement strictly generalizes (exhibit a witness satisfying new but not old).
3. Update the certificate instantiations so the D3 entropy certificates still compose with the sharpened theorems.
4. Keep every analytic boundary explicit; no hidden assumptions.
5. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.

Compile every authored file with `lake env lean` (exit 0), record `#print axioms`, write `longrun/results/D7-evolution-sharp-restatement.md` + `.json`.

Last line: TASK_DONE or TASK_BLOCKED with the card path.
