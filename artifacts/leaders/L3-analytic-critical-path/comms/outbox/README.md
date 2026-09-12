# Outbox — L3-analytic-critical-path (round 2, 2026-09-11)

Result card: `longrun/results/L3-analytic-critical-path.md` / `.json` (`TASK_DONE`, requesting
independent acceptance). No named blocker (U6/U8/U12) is closed; `exact_blockers_closed = []`.

Child tasks proposed by this round (JSON schema: id, group_id, parent_node, deps, lane,
acceptance, host_pool, requires_lean):

| file | blocker | state |
|---|---|---|
| `L3-U6b-spatial-laplacian.json` | U6 (spatial C²) | open — `SpatialLaplacianBridge` is statement-only |
| `L3-U6a-duhamel-fterm.json` | U6 (Duhamel upgrade) | open — the semigroup time derivative is now proved; only the `F`-term Leibniz rule remains |
| `L3-U6c-manifold-heat-plan.json` | U6 (manifold layer) | open — plan task |
| `L3-U8a-quasilinear-plan.json` | U8 | open — highest-value unblocking item per the D13 review |

## IMPORTANT: `L3-U6a-uniform-bridge` is already discharged

The dispatcher imported the round-1-outbox proposal `L3-U6a-uniform-bridge` into `queue.json`
(id `L3-U6a-uniform-bridge`, status queued) before this round finished it. **That task's
acceptance is already met in this worktree:**

- `Poincare.L3.HeatTimeDeriv.uniformMildToClassicalBridge_holds (n) :
  UniformMildToClassicalBridge n` — `release/Poincare/L3/HeatTimeDeriv/UniformBridge.lean`
  (sha256 `95ac4d69…001`);
- `Poincare.L3.HeatTimeDeriv.hasDerivAt_heatConv_BCF (n) {t} (ht) (f) :
  HasDerivAt (fun s => heatConv n s f.val) (timeDerivBCF n ht f) t` — the requested downstream
  consumer in the `BCFn` sup norm, `release/Poincare/L3/HeatTimeDeriv/BanachDeriv.lean`
  (sha256 `339d79b5…a0d`).

A future assignee should re-use those modules (relay them) rather than reprove the statement; the
new `L3-U6a-duhamel-fterm` task is the actual remaining work.
