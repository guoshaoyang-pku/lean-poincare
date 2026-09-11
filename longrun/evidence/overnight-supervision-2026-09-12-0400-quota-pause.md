# Overnight supervision checkpoint — 2026-09-12 04:00 +0800

Repeated API quota failures were confirmed across `L1-lean-baseline` (`RATE_LIMIT`, concurrency 21>20), `L2-upstream-adapters` (`QUOTA: Insufficient Balance`), `L4-geometric-critical-path` and `SEMREV-L4-C3-doubling-to-covers`. These are external API/account failures, not Lean or mathematical failures.

To prevent repeated failed calls, those four wrappers were stopped with SIGTERM after writing a task-local `PAUSED` marker and preserving their checkpoints, logs and worktrees. The queue policy was atomically lowered to `min=1`, `target=1`, hard cap 128; recursive admission remains paused. No task or artifact was deleted or reset.

The last authoritative queue state before this control action was 141 task records: 92 compile-verified, 5 running, 40 queued, 2 paused and 2 blocked. The previous positive window (86→92 verified) remains fully evidenced, but no fresh promotion is expected until the host-side quota is restored.

No exact named blocker closed. Existing mathematical status and scope classifications are unchanged. 360-1/360-2 SSH transport failures remain recorded and their state is preserved.

Recovery rule: after a successful host-side API/balance probe, remove only the task-local quota pause markers as appropriate, resume from checkpoints, and raise admission gradually from 1.
