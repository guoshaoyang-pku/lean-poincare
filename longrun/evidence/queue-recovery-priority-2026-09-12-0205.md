# Queue recovery priority — 2026-09-12 02:05 +0800

The 01:49 readiness audit contains 40 queued records. All 40 are non-runnable under the dispatcher contract because every row lacks a task-specific prompt and dedicated worktree. Of these, 29 also carry invalid dependency references and 7 carry unresolved pending dependencies (two have both). No task is relabeled runnable by this report.

## Recovery order after quota restoration

1. **Independent audit lane (lowest mathematical dependency risk):** `L1-C1-independent-axiom-replay`, `L1-C3-negative-control-quarantine`, `L1-C4-p5-hash-gate`, `L1-child-declaration-ledger-export`, `L1-child-partial-def-soundness-review`, `L1-child-queue-verdict-gate`. Repair each to use queue task IDs in `deps`, assign an isolated worktree, and write a concrete prompt with an acceptance command.
2. **Already-produced artifact reviews:** resume `L4-child-d13-semantic-audit`, then `SEMREV-L4-C3-doubling-to-covers` from preserved checkpoints before admitting new children.
3. **Analytic consumers:** `L3-U6a/b/c`, `L3-U8a`, `L3-U6a-duhamel-fterm`, `L3-child-conjugate-heat-euclidean`, `L3-child-l1-initial-condition`; only after exact upstream task IDs are established.
4. **Geometric/topology interfaces:** `L4-C2-manifold-atlas-bridge`, `L4-child-conjugate-point-bound`, `L4-child-pointed-gh-transport`, `L4-child-ricci-to-doubling`, then L5 M8/I6/I7 children after dependency repair.
5. **Upstream adapter inventory:** M2 adapter consumers and pin-bridge decision, with source-claim classifications preserved.

This ordering consumes no provider calls while quota is unavailable. It preserves all original queue rows and artifacts, and it avoids turning prose dependencies into false readiness. Admission should remain `min=1,target=1,hard_cap=128` until a host-side API/balance probe succeeds and at least one repaired task passes compile plus axiom audit.
