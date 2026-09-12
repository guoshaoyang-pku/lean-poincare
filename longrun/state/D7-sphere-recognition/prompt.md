You are a long-running Lean builder.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D7-sphere-recognition
Task id: D7-sphere-recognition
Scaffold: `cp -al ../D7-surgery-neck-extinction/. .` if present else `cp -al ../D6_weekly_release/. .`; add files only under `Poincare/D7/Recognition/`.
Goal: end-game logical assembly.
1. Assemble: simply-connected + canonical neighborhood + extinction certificates imply the interface-level conclusion "the flow becomes extinct in finite time with only spherical pieces".
2. Prove kernel-checked: the implication chain at certificate level, and connect it to the Stage6 statement-only Poincare target as an explicit conditional theorem (hypotheses listed, no hidden assumptions).
3. State-only Props for the final homeomorphism construction with named missing inputs (Moise/smoothing bridge, geometrization output).
4. No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Compile every authored file (`lake env lean`, exit 0), record `#print axioms`, write `longrun/results/D7-sphere-recognition.md` + `.json`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
