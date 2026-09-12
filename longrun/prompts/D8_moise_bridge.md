You are a long-running Lean builder working on statement fidelity.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-moise-statement-bridge
Task id: D8-moise-statement-bridge
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D8/Fidelity/`.
Goal: close the statement-fidelity gap between the smooth-category end-game and the topological Poincare statement.
1. Survey (web/GitHub API) what is known formally about 3-dimensional smoothing theory (Moise, Munkres, Hirsch); record sources with URLs.
2. Define `MoiseData`: a certificate that a compact topological 3-manifold admits a unique smooth structure up to the stated equivalence.
3. Prove kernel-checked: the logical implication "smooth-category extinction conclusion + MoiseData ⇒ topological-category statement" at type level, connecting to the Stage6 target; plus one checked toy lemma about equivalence relations used.
4. State-only Props for Moise's theorem itself with named missing dependencies.
5. Write a fidelity card mapping the informal conjecture wording to the formal statement term-by-term.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`. Compile all authored files (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D8-moise-statement-bridge.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
