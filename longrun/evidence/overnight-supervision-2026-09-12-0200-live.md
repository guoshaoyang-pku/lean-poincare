# Live supervision checkpoint — 2026-09-12 02:00 +0800

## Scope

This checkpoint covers only the Poincare Lean formalization swarm. The unrelated cosmic-supervision swarm is excluded.

## Fleet membership and stability

- Research-group registry: **5 groups / 5 long-lived leaders** (`L1-lean-baseline`, `L2-upstream-adapters`, `L3-analytic-critical-path`, `L4-geometric-critical-path`, `L5-topology-audit`). The protocol does not define a 4-group layout.
- `ophis-gpu` live read: 141 queue task records; 92 `verified`, 40 `queued`, 7 `paused`, 2 `blocked`, 0 currently reported running. Exactly one `dispatch_loop.py` (PID 3924237) is alive.
- `ophis-gpu` admission: adaptive controller with `min=1`, `target=1`, `hard_cap=128`; recursive admission paused via `ADMISSION_PAUSED`.
- `360-1` and `360-2`: SSH returned `Connection closed ... port 22`; this is recorded as transport failure. Their last reliable snapshots (15 and 14 records) are historical and are not counted as current live state.
- Thus the only defensible current total is 141 live task records on ophis, plus two transport-unreadable pools. A cross-host total of 170 (141+15+14) is a historical lower-bound snapshot, not a live membership count.

## Throughput assessment

- Since the 01:49 readiness audit, ophis remains at 92 compile-verified and 40 queued. Queue growth has stopped after recursive admission pause; promotion has also stopped after provider exhaustion. This is stable-but-idle, not healthy sustained growth and not evidence of decay.
- The positive overnight promotion window remains material: compile-verified rose **86 → 92** through D13 heat-kernel bridge, L4 C3/C4, D13 cross-audit, L5 topology review and C4 semantic review gates. These are compile/audit artifacts with explicit model/conditional/statement-only ceilings; no exact named mathematical blocker closed and no unconditional Poincare theorem exists.
- Latest worker logs on L1, L2, L4 and C3 report `QUOTA: Insufficient Balance`; L3 also reports a concurrency `RATE_LIMIT`. The fail-safe `bin/worker_loop.sh` is deployed (sha256 `cd537c1c2ce11ec00ba97bc4f74ebce8ed4bbe6886dfefb015fe4ede5353596f`) and pauses quota-failing invocations while preserving checkpoints.

## Immediate control decision

Keep one dispatcher, keep `min/target=1`, preserve all worktrees/checkpoints/cards, and do not launch new model-consuming workers until a host-side API/balance probe succeeds. During quota downtime, continue provider-independent queue metadata repair, semantic review bookkeeping, source-hash/axiom inventory and dated evidence commits. On quota recovery, resume from checkpoints in this order: `L4-child-d13-semantic-audit`, `SEMREV-L4-C3-doubling-to-covers`, then `L1-child-self-implication-audit`; raise target gradually (1→4→6) only after fresh promotion evidence.

## ETA

With quota unavailable, no honest wall-clock ETA can be promised for the next mathematical artifact. If quota recovers and the current promotion rate (6 compile promotions in the overnight window) returns, another bounded compile/audit wave is plausible within hours; closure of the Ricci-flow mainline and independent semantic audit remains a multi-month to multi-year research program.
