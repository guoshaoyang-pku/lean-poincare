# Primary controller supervision — 2026-09-11 23:12 +0800

- Publication branch: `codex/swarm-admission`; local HEAD `c64cdce`; `main` untouched.
- Five concrete leader prompts and registry committed in `longrun/prompts/L*-*.md` and `longrun/leader-registry.json`.
- ophis-gpu has one live dispatcher and adaptive min 8 / target 96 / hard cap 128.
- `SWARM-WAVE-2.md` is absent; Wave 1 and handoff remain authoritative.
- Resumed `D13-heatkernel-bridge-d10-d7` from checkpoint/artifact; D7 heat-kernel existence blocker remains open.
- Launched L1 baseline, L2 upstream adapters, L3 analytic, L4 geometric, L5 topology/audit; heartbeats fresh at 23:08.
- Queued `D13-cross-audit-ophis-cards` on 360-1 with independent worktree; queued one lightweight `D13-upstream-api-inventory-3602` on high-load 360-2.
- Existing heat bridge: 409 declarations, build 9202 jobs, axiom/semantic checks pass; finite-model bridge only. Existing 360 audit: 46/46 checks pass with F27/F28 and tensor B1/B2/B3 retained. No new exact blocker closures; semantic ledger remains 23 open.
- Initial SSH control-socket failure was retried successfully as transport friction; no state deleted. Full settings read was auto-review rejected due credential exposure risk; no credential extracted.
- Host load final check: ophis ~13.5, 360-1 ~3.2, 360-2 ~68.0.

Next: verify leader checkpoints/outboxes, import schema-valid child tasks, gate 360-1 audit on terminal state, monitor 360-2 until load recovers, and publish the next dated evidence summary.
