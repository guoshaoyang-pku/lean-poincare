# Semantic review — D12 volume/IBP artifact

Date: 2026-09-12 07:35 +0800

This review examines the preserved D12-volume-ibp result card, JSON declaration inventory, checkpoint, source hashes, and gate/audit metadata. The remote Lean source files were not re-fetched in this interval because the relay is intermittently closing connections; therefore this is an evidence-backed card/checkpoint review, with source-level replay still desirable when transport recovers.

## Verdict

The artifact is correctly classified as a **Euclidean chart model**, with a **conditional** interpretation for closed-manifold use. It supplies a substantial chart-level density, divergence, metric integration-by-parts, drift-weighted IBP, and change-of-variables layer. It does not prove a global Riemannian volume/Stokes theorem, unrestricted D7 `WeightedIBPStatement`, or any Poincare conclusion. Exact named mathematical blocker closures remain `[]`.

## Semantic checks

- `ChartMetric` requires explicit entrywise smoothness and pointwise positive-definiteness. The density `sqrt(det g)` and inverse-matrix constructions are therefore not hypothesis-free.
- `chart_ibp` includes C2 regularity and compact support for the integrated factor; `chart_weighted_ibp` includes C2 regularity and compact support for the test factor. The card explicitly records that the unrestricted no-support D7 statement is overstrong on a noncompact chart.
- The divergence theorem is derived from the pinned mathlib box theorem rather than introduced as an axiom. Product-rule expansions and compact-support boundary cancellation are identified as the proof mechanism.
- `chartWeightedIBPStatementRestricted_holds` is a restricted downstream shape consumer. It must not be read as closing the unrestricted manifold-level D7 blocker.
- The change-of-variables layer requires a smooth injective/surjective chart map together with an explicit derivative-injectivity condition; the card records the x↦x^3 counterexample to show why map injectivity alone is insufficient.
- The Euclidean one-dimensional witness and non-Euclidean exponential metric witness establish non-vacuity and distinguish density from the Euclidean case.
- The named blockers for atlas gluing, boundary Stokes, orientation, and closed-manifold entropy are state-only and are not consumed as assumptions by proved declarations.

## Evidence and classification

The preserved card reports full build exit 0 (8956 jobs), 74/74 per-file checks, 63 declaration cones within `{propext, Classical.choice, Quot.sound}`, negative-control detection, and a clean forbidden-token scan under Lean `v4.34.0-rc2` / mathlib `7974e751`. These support compile/kernel evidence for the declared chart scope.

Classification: chart-level declarations are proved under explicit hypotheses; global closed-manifold use is conditional; Frenzymath/API comparison rows are upstream source claims or capability observations. No exact blocker closure is inferred.

## Remaining acceptance

1. Re-fetch the owned source worktree and independently replay the 74-file gate when SSH relay is stable.
2. Have D12 tensor/maximum and entropy consumers compile against the chart APIs.
3. Construct the missing atlas/gluing, global volume, and closed-manifold Stokes inputs before any manifold-level promotion.
