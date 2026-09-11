# Quota-recovery execution order — 2026-09-12 02:00 +0800

The provider quota is still unavailable, so model-consuming workers remain paused and admission stays at `min=1,target=1`. This document fixes the next execution order without changing theorem semantics or queue state.

1. Resume `L4-child-d13-semantic-audit` from its preserved checkpoint and complete compile/axiom/semantic gate.
2. Resume `SEMREV-L4-C3-doubling-to-covers` from its preserved checkpoint; its parent C3 artifact already passed the 70-file compile gate.
3. Resume `L1-child-self-implication-audit` as the highest-value no-new-theorem audit task; its acceptance is a full kernel def-eq scan and remediation list.
4. Resume L1/L2/L4 leaders only after a successful host-side API/balance probe and a clean invocation.
5. Admit `L4-child-gh-family-covers` and `L4-child-ricci-to-doubling` only after C3 semantic review is accepted, preserving their explicit dependency on `L4-C3-doubling-to-covers`.

The queue audit found 40 queued entries lacking task-specific prompts under the current remote state. They remain queued and are not relabeled runnable. The fail-safe worker loop detects provider quota markers and exits after writing `PAUSED`.

Promotion baseline before quota exhaustion: 92 compile-verified, with verified growth 86→92 and no exact named blocker closure. Mathematical status remains bounded; no unconditional Poincare proof exists.
