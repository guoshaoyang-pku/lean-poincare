# L4 round-3 outbox note (non-task; the dispatcher imports only `*.json` child tasks)

Round-3 artifacts are reported in `longrun/results/L4-geometric-critical-path.md` and `.json`
(verdict `TASK_DONE`, requesting independent acceptance; **no named blocker is claimed closed**).

New child task JSONs written this round (schema: id, group_id, parent_node, deps, lane,
acceptance, host_pool, requires_lean, max_hours):

- `L4-child-ricci-to-doubling.json` — U9: instantiate D12's Bishop–Gromov chain with explicit
  constant-curvature models and derive closed-form volume-ratio/doubling bounds, with a precise
  interface note on realizing radial volume as a ball measure.
- `L4-child-gh-family-covers.json` — U9: lift the round-3 pair-level
  `coveringNumber_univ_le_of_ghDist_lt_of_doubling` to a family in the exact `uniformCovers`
  language of D12's compactness criterion.
- `L4-child-jacobi-zero-interlacing.json` — U3: extend the round-3 one-sided Sturm zero
  existence to two-sided zero interlacing/spacing with the equality case.

Carried out in round 3 (do not re-dispatch without checking the result card):

- `L4-child-sturm-zero-interlacing` — its scope is now delivered by
  `release/Poincare/L4/GeodesicComparison/SturmZeroCount.lean` (constructed shifted model,
  `exists_jacobi_zero_of_curvature_gt`, `exists_jacobi_zero_before_pi_sqrt`, the dichotomy,
  witnesses, all axiom-audited).  The imported child entry is preserved as the original scope
  record; `L4-child-jacobi-zero-interlacing.json` is its genuine two-sided successor.
- `L4-C3-doubling-to-covers` — the metric-doubling ⟹ covering-bound half is delivered by
  `release/Poincare/L4/Compactness/DoublingToCovers.lean` plus the measure-growth half
  `release/Poincare/L4/Compactness/MeasureGrowthCovers.lean`; the remaining curvature →
  doubling input is `L4-child-ricci-to-doubling.json`.

Still open from earlier rounds (unchanged): `L4-child-pointed-gh-transport`,
`L4-child-d13-semantic-audit`, `L4-C1-geodesic-spray-interface`,
`L4-C2-manifold-atlas-bridge`.  `L4-C4-constant-curvature-rauch` and
`L4-child-conjugate-point-bound` remain **carried out in round 2**; do not re-dispatch.

No named blocker (U3, U7, U9, I4, I5) is closed.  Evidence:
`evidence/l4_axiom_audit.json`, `evidence/l4_source_hashes.txt`, `evidence/l4-verify.log`,
`evidence/l4-round3-build.log`.
