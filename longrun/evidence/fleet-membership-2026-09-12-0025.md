# Fleet membership and control assessment — 2026-09-12 00:25 +0800

## Group and model facts

The canonical registry has five mathematical groups and five long-lived leaders: L1 Lean baseline, L2 upstream adapters, L3 analytic critical path, L4 geometric critical path, and L5 topology/audit. The inspected leader registry and host queue identify `deepseek-flash` as the configured remote model. No inspected configuration establishes `codex astra ultra` on the remote fleet; an Astra model must not be assumed or silently substituted.

## Last successful fleet snapshot

- ophis-gpu: 135 queue task records; 86 compile-verified, 7 running, 40 queued, 1 paused, 1 blocked; one dispatcher confirmed.
- 360-1: 15 task records; 13 verified, 1 running, 1 blocked (last successful read).
- 360-2: 14 task records; 13 verified, 1 running (last successful read).
- Total registered task records in that snapshot: 164. Known running task records: 9. This is queue accounting, not a count of mathematical proofs or independent model threads.

## Stability and trend

Compared with the previous 23:52–23:53 window, ophis rose from 129 to 135 total tasks and from 37 to 40 queued, while compile-verified stayed at 86 after two earlier promotions. Thus recursive admission is still outrunning promotion. The fleet is live: leader/reviewer heartbeats are fresh and logs are actively growing, but consumption of the queued child wave is not yet stable.

The remote 360 hosts currently return SSH connection-closed errors. This is recorded as transport failure; their last known queue states above are not presented as a fresh live reading. No state was deleted or reset.

## Control action

Keep one dispatcher per host, keep `ADMISSION_PAUSED`, keep target 8 and hard cap 128, and repair queued metadata before increasing concurrency. Readiness audit `pf-readiness-2026-09-12-0025.json` found all 40 queued ophis children missing task-specific prompts and dedicated worktrees; most dependencies are prose/file descriptions rather than queue IDs. These tasks are therefore not runnable under the dispatcher gate.
