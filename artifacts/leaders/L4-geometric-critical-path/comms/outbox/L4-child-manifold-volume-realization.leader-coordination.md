# Leader coordination — `L4-child-manifold-volume-realization` (U9)

**Status: PARTIALLY CARRIED OUT BY THE LEADER in round 6 (session slice 3)** — the recommended
flat-2-torus target is delivered; the remaining generality is split into
`comms/outbox/L4-child-torus-family-realization.json` (parameterized family, uniform constants)
and the still-open general manifold-volume gap. Do not re-dispatch this child as originally
scoped without checking the delivered artifact first.

Delivered in the leader worktree (`release/Poincare/L4/Compactness/FlatTorusGrowth.lean`):

* a concrete compact geometric family (the flat 2-torus `AddCircle 1 × AddCircle 1`) with a
  *constructed* measure (product Haar measure transported along the canonical isometry);
* the exact closed-ball measure `(ofReal (min 1 (2 s)))²` proved from mathlib's
  `AddCircle.volume_closedBall` (not assumed);
* a genuine inhabitant of the round-6 `UniformRicciBallGrowth` interface with explicit constants
  `C = 4`, `K = 1`, `R = 1/4` and profile `torusA t = 8 t` on `(0, 1/2]`;
* non-degeneracy: the ball measure genuinely depends on the radius (`1/4` at `s = 1/4` versus `1`
  at `s = 3/4`) and two points are at distance `1/2 > 0`;
* downstream checked use: `totallyBounded_torus`, `isCompact_torus`, `exists_pointed_subseq_torus`
  consume the round-5 chain (the leader theorems appear in the proof terms; nothing is reproved);
* a checked U3 link: `Poincare/L4/GeodesicComparison/FlatGeodesicExpModel.lean` proves
  `torusA t = 8 * radialJacobi 1 t` on the interval `(0, 1/2]`, connecting the U9 witness to the
  flat-model geodesic/exp/Jacobi layer.

Not delivered (still open, U9): a general Riemannian volume measure, a radial ball-profile
realization for an arbitrary family, harmonic coordinates, and the `C^{1,α}` limit upgrade. The
family-uniform version (all circumferences `T ∈ [1,2]` with constants independent of `T`) is
delegated as `L4-child-torus-family-realization`.
