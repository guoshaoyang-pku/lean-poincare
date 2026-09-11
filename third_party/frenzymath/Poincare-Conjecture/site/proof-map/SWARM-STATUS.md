# Swarm proof-map status

The swarm.html page is a static visual prototype, not a live dashboard. Its embedded values are historical and must not be read as the current research state.

Latest supervision snapshot (2026-09-11 22:05 +0800): ophis-gpu has 83 compile-verified, 1 running, 1 queued, 1 paused and 1 blocked; 360-1 has 13 verified and 1 blocked with no running task; 360-2 has 13 verified with no running task. The semantic ledger records 23 open blockers and no exact named blocker closures. D13 results are compile/audit artifacts and do not establish an unconditional Poincare proof.

A future live view must load generated state containing timestamp, host queue counts, group/task status, heartbeat age, evidence level, source/artifact hashes and blocker data. Until then label the page static snapshot and show its capture time.
