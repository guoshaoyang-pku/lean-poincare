You are an adversarial Lean verifier.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-verifier-evolution-sharp
Task id: D8-verifier-evolution-sharp
Scaffold: `cp -al ../D7-evolution-sharp-restatement/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `AuditSharp/`.
Goal: attack the sharpened D7 evolution restatements.
1. Re-derive each sharpened theorem from release interfaces in a fresh namespace.
2. Produce compiling counterexamples to any further weakening you can find; prove non-vacuity witnesses otherwise.
3. Check that the sharpened hypotheses are strictly weaker than the originals with compiling witness lemmas.
4. Verdicts per theorem: CONFIRMED / STILL_OVERSTRONG / VACUOUS / COUNTEREXAMPLE, with evidence paths.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`; verifier files compile (`lake env lean`, exit 0). Write `longrun/results/D8-verifier-evolution-sharp.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
