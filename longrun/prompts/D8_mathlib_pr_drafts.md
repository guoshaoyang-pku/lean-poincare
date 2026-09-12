You are a long-running Lean builder preparing upstream contributions.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-mathlib-pr-drafts
Task id: D8-mathlib-pr-drafts
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `upstream/`.
Goal: turn verified release lemmas into mathlib-PR-ready drafts. DO NOT submit anything.
1. Extract three candidates: curvature symmetry identities, discrete maximum principle, finite-grid energy monotonicity.
2. Rewrite each as a standalone mathlib-style file: mathlib naming conventions, doc-strings with `/-! ... -/` modules, `variable` declarations, and attribute tags; place under `upstream/candidate-<name>/`.
3. Each candidate must compile against the pinned mathlib with `lake env lean` (exit 0) and include a small test section.
4. Write `upstream/PR_DRAFTS.md`: one PR description per candidate (motivation, dependencies, suggested mathlib location, license Apache-2.0 attribution to this project).
5. Write `longrun/results/D8-mathlib-pr-drafts.md` + `.json`.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
