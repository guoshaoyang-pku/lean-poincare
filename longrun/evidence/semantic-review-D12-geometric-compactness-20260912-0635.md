# Independent semantic review — D12 geometric compactness

Date: 2026-09-12 06:35 +0800

The preserved D12 geometric compactness result card and checkpoint were reviewed against their declaration classes, explicit hypotheses, and compile/audit evidence.

## Verdict

The artifact proves a substantial general metric layer in mathlib unpointed GHSpace: cover and diameter transfer, the converse of the uniform-cover criterion, compactness assembly, and subsequence witnesses. It also proves a concrete Euclidean grid model. The smooth Cheeger–Gromov, pointed, Bishop–Gromov, ancient-kappa, and canonical-neighborhood portions remain statement-only. No general-manifold blocker closure follows from this card.

## Declaration checks

- `cover_transfer_*` and `diam_transfer_*` are conditional metric transfer lemmas with explicit isometric embeddings, Hausdorff/GH bounds, and radius inequalities.
- `uniformCovers_of_totallyBounded`, `totallyBounded_iff_uniformCovers`, `gromovCriterion`, and `isCompact_of_uniformCovers` operate on genuine compact metric spaces and explicitly require total boundedness/closedness and uniform diameter and covering bounds. They do not assume curvature, smoothness, or a convergent subsequence.
- `gh_subseq_*` constructs subsequence and limit witnesses from compactness; it does not take convergence as an input.
- `GridFamily` is a nondegenerate Euclidean model with unbounded cardinality, uniform covers, and an explicit limit. It does not encode Ricci curvature or a manifold flow.
- Frontier declarations such as `bishopGromovVolumeComparison`, `harmonicCoordinatesExistence`, `cheegerGromovCompactness`, `ancientKappaCompactnessFrontier`, and `canonicalNeighborhoodFrontier` are explicitly parameterized Prop definitions with no inhabitants and are excluded from the proved set.

The hypotheses are non-vacuous for the grid family, while the frontier interfaces remain intentionally uninhabited. No conclusion-equivalent hypothesis or forbidden authored token is claimed by the card.

## Evidence reconciliation

The card reports a pinned Lean v4.34.0-rc2 / mathlib 7974e751 build with exit 0, per-module exit 0, 39 declaration axiom audit restricted to `propext`, `Classical.choice`, and `Quot.sound`, and a planted negative control detected. These are adequate compile/kernel evidence for the stated metric/model scope.

## Classification and remaining work

General proved: unpointed metric compactness and subsequence layer. Model proved: unit-square grid family. Statement-only: pointed lift, Bishop–Gromov curvature-to-cover conversion, harmonic coordinates/elliptic regularity, Cheeger–Gromov smooth compactness, ancient-kappa compactness, and canonical neighborhoods. Exact named mathematical blocker closures from this review: `[]`.
