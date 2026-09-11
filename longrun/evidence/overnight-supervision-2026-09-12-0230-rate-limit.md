# Overnight supervision checkpoint — 2026-09-12 02:30 +0800

After the observed DeepSeek concurrency-rate-limit event, the ophis adaptive target is now **6** (previously 8), with hard cap 128 and recursive admission paused. The change is recorded in the live queue controller note and was applied atomically; all task state is preserved.

The most recent queue snapshot is unchanged at 141 records: 92 compile-verified, 5 running, 40 queued, 2 paused and 2 blocked. The single dispatcher remains alive. No task was reset, deleted or duplicated.

The preceding promotion window remains valid: D13 heat-kernel bridge, L4-C4 Rauch, L4-C3 doubling-to-covers, D13 cross-audit, L5 semantic review and C4 semantic review all passed compile gates. L4-C1 remains an honest pinned-mathlib API blocker. C3 semantic review and L4 D13 semantic audit remain active/repairing from preserved checkpoints.

The rate-limit is classified as transport/API admission failure, not a mathematical or Lean failure. Lowering target is the appropriate control while verified promotion is temporarily flat. If promotion resumes and the API error clears, target can be raised gradually; otherwise it remains at 6.
