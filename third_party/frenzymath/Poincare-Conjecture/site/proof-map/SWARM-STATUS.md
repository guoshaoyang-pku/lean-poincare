# Swarm proof-map status

The swarm.html page is a static visual prototype, not a live dashboard. Its embedded values are historical and must not be read as the current research state.

Latest reliable supervision snapshot (2026-09-11 23:38 +0800): ophis-gpu has 83 compile-verified, 6 task-level running, 21 queued after recursive leader import, 1 paused and 1 blocked; 360-1 has 13 verified and 1 blocked; 360-2 has 13 verified. The semantic ledger records 23 open blockers and no exact named blocker closures. D13 results are compile/audit artifacts and do not establish an unconditional Poincare proof. The independent \`ai4math-swarm\` is excluded from these counts.

ETA reading: additional local/conditional frontier artifacts can plausibly accumulate over the next several days to one week. Full Ricci-flow completion remains a multi-month to multi-year effort because the serial analytic and geometric dependencies, downstream consumers and independent semantic audit are not closed.

A future live view must load generated state containing timestamp, host queue counts, group/task status, heartbeat age, evidence level, source/artifact hashes and blocker data. Until then label the page static snapshot and show its capture time.
