# Leader acceptance — round-6 M3 `FlatGeodesicExpModel.lean` (independent adversarial review)

- **Artifact:** `release/Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean`
- **Reviewed revision (as reviewed):** sha256 `88f47df8c4d347f46d1b1320bffbdece896e42aaca97df045b68c69cd50a9057`
- **Frozen revision (after review-driven doc-only corrections):** sha256
  `799134cacd1d4a9d31b490b246ad15eadb77ca5a6f974b6ba89f4749e937d7b5`
- **Reviewer verdict:** **PASS-with-findings** — 0 BLOCKER, 2 MAJOR (both scope/triviality,
  docstring-level), 5 MINOR, INFO (`evidence/review-flat-geodesic-exp-model.md`, 445 lines;
  reviewer scratch `scratch/review-flat-geodesic/`; delta re-verification of the doc-only
  corrections appended to the report).
- **Independent evidence accepted:** all 17 statements are true and all 17 axiom cones are
  exactly `[propext, Classical.choice, Quot.sound]`; forced compile exit 0 with zero output and
  also with `-DwarningAsError=true`; independent mathlib-only re-derivations (distance formula
  for all real times, translation injectivity, `t • v = 0 ↔ t = 0`, `J' = v`, `J'' = 0`); the
  torus dictionary identity independently checked (holds at `t = 0` and on `Icc 0 (1/2)`, fails
  for every `t > 1/2`, so the stated upper restriction is necessary); no circularity (only
  `AxiomAudit.lean` imports M3).
- **Findings disposition:**
  * M-1 MAJOR ("no conjugate points" over-claim in the header): **fixed** — the header now
    presents injectivity of the flat exponential map as the elementary model computation behind
    the absence of conjugate points and explicitly records conjugate points as a manifold-level
    notion that is not defined or proved; conjugate points are now in the not-claimed list.
  * M-2 MAJOR (`expMap_injective` triviality): **mitigated by documentation** — the docstring and
    the not-claimed list now state that it is a translation-injectivity statement holding in any
    additive group and is not a manifold-level or curvature statement.
  * M-3, F-4, F-5, F-6, F-7 MINOR: **all addressed in docstrings** in the frozen revision
    (torsion-freeness wording, standalone-restatement note for `scalarRadialJacobiSolutionOn`,
    cross-reference note for the torus dictionary line, corrected description of
    `euclid_volume_doubling_of_ricci_nonneg`, corrected `radialJacobi_hasDerivAt_deriv`
    docstring), delta-re-verified.
  * INFO (redundant direct `ModelEuclidean` import kept deliberately for the directly-used name;
    dead-end node status): recorded on the round-6 card.
- **Leader decision:** **ACCEPTED** for integration as a *proved flat-model (U3) dictionary
  module* with the strengthened honest-scope wording. It closes no part of U3 at manifold level;
  U3 remains open.
