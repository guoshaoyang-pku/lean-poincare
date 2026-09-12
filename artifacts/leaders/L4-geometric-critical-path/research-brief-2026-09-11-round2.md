# L4-geometric-critical-path — research brief (round 2, 2026-09-11/12)

Worktree: `longrun/worktrees/leaders/L4-geometric-critical-path`
Toolchain: `leanprover/lean4:v4.34.0-rc2`; mathlib pinned at
`7974e751bece493b6ff508039423ca9fa2452fa8` (`release/lake-manifest.json`).
Lane: builder. Named blockers in scope: U3, U7, U9, I4, I5.

## 0. Bottom line of this round

No named blocker is closed.  What was produced (50 new kernel-checked declarations): a
repaired and extended **scalar Jacobi/Rauch comparison chain** — flat model, sharp
constant-curvature model `j_K` in both directions (`u'/u ≤ j_K'/j_K` for `k ≥ K ≥ 0`,
`j_K'/j_K ≤ u'/u` for `k ≤ K ≤ 0`), the curvature-bound form, the integrated forms
`u ≤ j_K` and `j_K ≤ u`, and the conjugate-point bound `T ≤ π/√K` (U3 partial); the
**first consumer outside the D13 tree** plus an **independent axiom re-audit of the D13
headline layer** and a new **sign estimate** on its glued measure (U7 partial); and a
**quantitative covering-number stability theorem under Gromov–Hausdorff perturbation**
(U9 partial).  Every claim is evidence-ledgered; the chart/model vs manifold distinction is
kept explicit.

## 1. Findings that shape the critical path

1. **U3 verified from the pin.** grep over `Mathlib/Geometry/Manifold` shows no geodesic,
   exponential map, parallel transport, Jacobi field, injectivity radius or curvature
   tensor; only docstring TODOs.  Present and usable: `IsRiemannianManifold`,
   `Manifold.pathELength`/`riemannianEDist`, `CovariantDerivative` +
   `leviCivitaConnection`, first-order `IsMIntegralCurve` with local existence, `mfderiv`,
   `mlieBracket`.  The single missing primitive is the second-order geodesic-spray equation
   `∇_{γ'}γ' = 0`.
2. **U7: the D13 ManifoldIBP layer is terminal outside its own tree.** The strongest engine
   `SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` (POU constructed internally)
   and its side-condition-free instantiation
   `OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional` have no consumer outside
   `Poincare/D13/**`; in-tree consumers exist (`halfSpaceAtlas_dirichletEnergy`,
   `halfSpaceAtlas_greenIdentity`).  The critical missing bridge is
   mathlib-manifold → `SmoothOverlapAtlas` (charts, Gram matrix, tensor law), then a
   manifold-level consumer.
3. **U9: metric-level GH machinery is complete at the D12 level** (criterion both
   directions, subsequence witnesses, non-degenerate grid model); mathlib has
   `IsUnifLocDoublingMeasure`, `scalingConstantOf`, `Metric.coveringNumber`/`packingNumber`,
   `VitaliFamily`, `Besicovitch`.  Absent everywhere: Bishop–Gromov/volume comparison,
   `HasRicciBound`/CD(K,N), manifold Riemannian measure, and any doubling ⟹ covering-number
   bridge.  A *local* doubling measure does not by itself control covers at all scales
   (mathlib's class is uniformly **locally** doubling), so the honest U9 target is either a
   bounded-scale statement or an explicit global-doubling hypothesis with the maximal
   separated-set argument.
4. **I4/I5 unchanged.** The five D3 entropy Props remain unproved; κ-noncollapsing and
   recognition remain statement-only.  D13's Gaussian model consumption
   (`finiteLifetimeEntropyBridge_gaussian`, `monotoneOn_F_gaussian`) is the only I4-adjacent
   proved content, and its unrestricted forms are kernel-checked false.

## 2. What was constructed (all kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound})

### U3 — scalar Jacobi/Rauch chain (new, `Poincare/L4/GeodesicComparison/`)
- `RauchBridge.lean` (repaired from a non-compiling round-1 draft; 16 errors fixed):
  one-sided/two-sided mean-value bounds, Jacobi linear bounds, *constructed* quantitative
  Euclidean normalization `EuclideanNormalizedOn (u'/u) 1 (4B) t₀` from Jacobi initial data,
  Riccati identity, Rauch I `u'/u ≤ 1/t` for `k ≥ 0`, area-ratio antitone, sine witnesses,
  and propagation-regime (`t₀ < T`) witnesses.
- `DownstreamComparison.lean`: Rauch II (`1/t ≤ u'/u` for `k ≤ 0`) via the mirrored D12
  engine; Bishop–Gromov volume ratio via D12 `volumeRatio_antitone`; the derived doubling
  estimate `V(2r) ≤ 4 V(r)`; hyperbolic and sine witnesses.
- `ConstantCurvatureRauch.lean`: the sharp model `j_K` (D10) is a Jacobi solution; its
  second-derivative bound `|j_K''| ≤ K·max(1/√K,T)`; **sharp Rauch I**
  `u'/u ≤ j_K'/j_K` for `k ≥ K ≥ 0`; witness `k = 2` vs `K = 1` with the strict inequality
  `√2·cot(√2 t) < cot t`.
- `CurvatureBoundRauch.lean`: **Rauch I from the curvature bound `t·k(t) ≤ B`** with the
  second-derivative bound *derived* (via `u' ≤ 1` and `u ≤ t`), removing the separate `|u''|`
  hypothesis; two witnesses.
- `ConstantCurvatureRauchLower.lean`: **sharp Rauch II** for `k ≤ K ≤ 0` via the mirrored
  D12 engine, its integrated form `j_K ≤ u`, model positivity/monotonicity/bound lemmas, and
  two witnesses (`coth t ≤ √2·coth(√2 t)`, `sinh t ≤ sinh(√2 t)/√2`).
- `ConjugatePointBound.lean`: **conjugate-point bound** `T ≤ π/√K` for `k ≥ K > 0`, obtained
  by comparing on sub-intervals `T'' < π/√K` and passing to the limit against
  `j_K(π/√K) = 0`, with a consistent witness.

### U7 — D13 layer verification and one new estimate (`Poincare/L4/ManifoldIBP/`)
- `D13HeadlineAudit.lean`: independent re-derivation of the axiom cones of the 8 D13
  headline theorems from outside the D13 tree — all exactly the classical trio.
- `WeightedSelfAdjointness.lean`: `metricInnerInverse_self_nonneg`,
  `gradInnerInverse_self_nonneg` (from `Matrix.PosDef.inv`),
  `halfSpaceAtlas_dirichletEnergy_nonneg` (integrability from D13 + new pointwise
  positivity; the *sign* statement was absent in D13), and the self-adjointness form of
  D13's Green identity, **explicitly labelled a packaged corollary after adversarial review
  found the first version overstated novelty**.

### U9 — covering stability under GH perturbation (`Poincare/L4/Compactness/`)
- `coveringNumber_le_of_ghDist_lt`: `ghDist X Y < r` and `2r + δ < ε` imply
  `coveringNumber ε univ_X ≤ coveringNumber δ univ_Y`.  Consumes the minimal cover from
  mathlib and D12's `cover_transfer_of_ghDist`; this is the quantitative form in which a
  curvature/non-collapsing compactness hypothesis can be fed to `gromovCriterion`.

## 3. Verification state

- `lake build` (whole release, default targets + `Poincare` glob): exit 0, 9393 jobs.
- Per-file `lake env lean` sweep over all 10 `Poincare/L4/**/*.lean` files: all exit 0.
- Fail-closed axiom audit `tools/l4_axiom_audit.py`: PASS, 50 L4 declarations + 8 D13
  headline declarations, whitelist {propext, Classical.choice, Quot.sound}, planted
  `axiom`-based negative control detected, forbidden-token scan clean (comments stripped).
- Independent adversarial reviews: RauchBridge (witness coverage gap closed);
  ConstantCurvature + WeightedSelfAdjointness (novelty overclaim corrected);
  CoveringStability + corrected WeightedSelfAdjointness (5/5 PASS, two docstring nits
  fixed); lower/comparison/conjugate-point additions (14/14 PASS: directions verified
  numerically with 0 violations, engine instantiations faithful, `conjugate_point_bound`
  independently instantiated at `T = 3.14` with `K = k = 1` showing the hypotheses do not
  force `T` small).

## 4. Exact remaining blockers (not closed)

- **U3**: the geometric bridge — geodesic spray/exp map, shape-operator Riccati equation,
  Cauchy–Schwarz, and the identification of `u` with a geodesic-sphere area density.  The
  scalar comparison side is now complete in both curvature directions, in curvature-bound
  form, in integrated form, and with the conjugate-point bound.
- **U7**: mathlib-manifold → `SmoothOverlapAtlas` bridge; manifold smooth partition of
  unity; closed-manifold `v ≡ 1`; Stokes/boundary; oriented volume form.
- **U9**: curvature bound + non-collapsing ⟹ uniform covering numbers (Bishop–Gromov),
  pointed GH convergence, harmonic coordinates/elliptic regularity, C^∞ limit upgrade.
- **I4/I5**: the D3 entropy Props and κ/recognition statements.

## 5. Next child tasks (see `comms/outbox/`)

`L4-C1-geodesic-spray-interface`, `L4-C2-manifold-atlas-bridge`,
`L4-C3-doubling-to-covers`, `L4-C4-constant-curvature-rauch` (C4 has since been carried
out in this round; the outbox entry records the original scope), plus the round-2
`L4-child-*` tasks: `L4-child-pointed-gh-transport` (U9),
`L4-child-d13-semantic-audit` (U7), `L4-child-sturm-zero-interlacing` (U3).
`L4-child-conjugate-point-bound` was imported before it could be withdrawn; its scope is
already complete (`ConjugatePointBound.lean`) and it should not be re-run.
