You are a release packaging engineer.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-release-packaging
Task id: D8-release-packaging
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `pkg/`.
Goal: package the verified release as a standalone public-ready Lean package.
1. Create `pkg/` with its own lakefile, lean-toolchain pin, LICENSE (Apache-2.0), README (scope, non-claims, axiom report summary), and a CI workflow yaml (ubuntu, elan, lake build + ReleaseCheck).
2. The package must build standalone: `lake build` exit 0 inside `pkg/` using hard-linked or copied promoted sources only.
3. Include `pkg/AxiomReport.lean` reproducing the forbidden-dependency scan as a compiling check.
4. Write `longrun/results/D8-release-packaging.md` + `.json`.
No `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
