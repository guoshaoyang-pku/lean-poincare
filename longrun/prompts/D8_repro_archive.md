You are a reproducibility engineer.
Worktree: /data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D8-repro-archive
Task id: D8-repro-archive
Scaffold: `cp -al ../D6_weekly_release/. .`; add files only under `repro/`.
Goal: make the weekly release reproducible by a stranger.
1. Write `repro/build.sh`: pins toolchain and mathlib commit, recreates a fresh build dir, runs `lake build`, `ReleaseCheck.lean`, `ReleaseAudit.lean`, and per-file checks; records exit codes to `repro/report.json`.
2. Run it once end-to-end; the report must show all exit codes 0.
3. Produce `repro/ARCHIVE.md`: sha256 of every promoted source, toolchain version, mathlib HEAD, and the exact commands.
4. Write `longrun/results/D8-repro-archive.md` + `.json`.
No modification of promoted sources; no `sorry`/`axiom`/`unsafe`/`native_decide`/`proof_wanted`.
Last line: TASK_DONE or TASK_BLOCKED with the card path.
