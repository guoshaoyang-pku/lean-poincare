# Supervision round summary — 2026-09-12 07:10 +0800

## Fleet

The latest authoritative ophis-gpu poll remains 141 registered tasks: 93 verified, 34 queued, 12 paused, 2 blocked, 0 running. Exactly one dispatcher (PID 2660017) is alive; `ADMISSION_PAUSED` remains present; adaptive admission is min/target 1 with hard cap 128. Host load remains around 10.2–10.5. 360-1 and 360-2 continue to return `Connection closed` on safe read-only retries; no state was deleted or reset.

## Material progress

The L3 child IBP axiom audit was completed in the verified pinned Lean v4.34.0-rc2 environment. Exit code is 0, and all five audited declarations (four reverse-kernel theorems plus `compactSupport_integral_mul_fderiv`) report only `propext`, `Classical.choice`, and `Quot.sound`. Evidence was pulled into the publication repo and pushed in commit `6ce6d40`; the earlier path failure remains preserved as historical evidence.

The L3 child remains `partial_artifact` and `model`: its directional IBP lemma is audited, but Laplacian transfer and a flat first-variation/monotonicity consumer are still absent. No exact mathematical blocker closure is claimed.

## Admission and trend

Queue remains stable but provider-stalled. The only material promotion in the observation window is 92 → 93 compile-verified; queued 34 ↔ 35 oscillation reflects reconciliation and pauses. Keep recursive admission paused and target at 1; do not raise hard cap.

Exact named blocker closures this round: `[]`. Semantic ledger remains 23 open blockers.

## Next action

Continue provider-independent downstream L3 work and semantic review of promoted cards. On quota recovery, resume prepared L1/L3/L4/L5 children one at a time from checkpoints and require compile, axiom, downstream-use, and semantic gates before promotion.
