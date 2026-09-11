# Overnight supervision checkpoint — 2026-09-12 01:15 +0800

A fresh ophis-gpu read confirms the single dispatcher is alive. Ophis remains at 135 task records: 86 compile-verified, 7 running, 40 queued, 1 paused, 1 blocked; adaptive target 8 and hard cap 128. Host load has fallen from about 80 to 40/44/49 but remains high enough to avoid target expansion.

The three prepared L4 workers have fresh heartbeats and growing logs. `L4-C4-constant-curvature-rauch` is marked running; `L4-C1` and `L4-C3` have active worker processes and fresh heartbeats even though the queue label still says queued, so the controller will continue reconciling evidence rather than restarting them. The three semantic review cards remain present; L3 has no gate yet, while L5 and D13 repair/gate cycles are active.

360-1 and 360-2 still return SSH connection-closed transport failures; their last known states are retained and no state is deleted.

No exact named blocker has closed. The next action is to let current workers finish and reconcile their DONE/card/gate markers; no admission increase or task reset is justified.
