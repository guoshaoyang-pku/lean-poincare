# D6 delivery note (sandbox)

The integrator promotion targets are outside this session's `workspace-write` sandbox:

- `/data3/guoshaoyang/workdir/lean_poincare/longrun/queue.json`
- `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D6-weekly-release.md`
- `/data3/guoshaoyang/workdir/lean_poincare/longrun/results/D6-weekly-release.json`

The promotion attempt (`cp`) returned exit 1, `Permission denied`; the one-shot escalation
to `danger-full-access` was rejected because no approval channel is available. The files are
therefore mirrored here for the supervisor to promote:

- `longrun/queue.updated.json` — proposed queue update (D5 verified; stale D2/D3/D4 entries
  corrected; 20 D7 builder tasks + 1 verifier task appended)
- `longrun/results/D6-weekly-release.md` / `.json` — release result card

Everything else (release package, manifests, ledger, blockers, tasks, logs) is under the D6
worktree and is self-contained.
