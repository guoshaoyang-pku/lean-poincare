# Mathlib API scout report — geodesic/compactness interface

Pinned mathlib rev `7974e751bece493b6ff508039423ca9fa2452fa8`, toolchain
`leanprover/lean4:v4.34.0-rc2`. All greps run in `release/.lake/packages/mathlib/`;
all `#check`/`#print` in temp files run as `lake env lean ../debug/ScoutProbeN.lean`
from `release/`. Probe files: `debug/ScoutProbe{,2,3,4,5,6,7}.lean`, `debug/probe1.out`.

## 1. Geodesic / exponential map / parallel transport / Jacobi field / injectivity radius: ABSENT (U3 CONFIRMED)

```
grep -rIn --include=*.lean -iE "\b(geodesics?|exponential map|exp map|parallel transport|jacobi fields?|injectivity radius|cut locus|sectional curvature|ricci (tensor|curvature))\b" Mathlib/Geometry/Manifold/
```
→ only 2 hits, both docstring TODOs:
`Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/Metric.lean:35-36`
("When Mathlib has a notion of parallel transport, prove …"). No declaration.

Counts over all Mathlib (`grep -rIn --include=*.lean -i`): `parallelTransport` 0,
`JacobiField` 0, `injectivityRadius` 0, `cutLocus` 0, `sectionalCurvature` 0, `Ricci` 0,
`curvature` 1 (docstring `Mathlib/MeasureTheory/Measure/Doubling.lean:44`), `flow` 0 in
`Geometry/Manifold`. `geodesic`: 20 hits, all `Group.Generators.IsGeodesic` (word metric,
`Mathlib/Geometry/Group/WordMetric.lean:68`) and `geodesicSubtree` (quiver,
`Mathlib/Combinatorics/Quiver/Arborescence.lean:113`). `expMap`: 193 hits, one file
`Mathlib/NumberTheory/NumberField/CanonicalEmbedding/NormLeOne.lean:247` (log/exp on Minkowski space).

Present and adjacent:
- `class IsRiemannianManifold (I) (M) [PseudoEMetricSpace M] [ChartedSpace H M]
  [Bundle.RiemannianBundle (TangentSpace I)] : Prop` — `Mathlib/Geometry/Manifold/Riemannian/Basic.lean:81`
- `riemannianMetricVectorSpace : Bundle.ContMDiffRiemannianMetric (modelWithCornersSelf ℝ F) ⊤ F (TangentSpace ·)` — Basic.lean:103
- `PseudoEMetricSpace.ofRiemannianMetric` (521) / `EMetricSpace.ofRiemannianMetric` (546)
- `Manifold.pathELength I γ a b : ℝ≥0∞` — `PathELength.lean:66`;
  `Manifold.riemannianEDist I x y : ℝ≥0∞` — `PathELength.lean:208` (the Riemannian edistance);
  `riemannianEDist_le_pathELength` (214), `riemannianEDist_self` (311), `riemannianEDist_comm` (316),
  `riemannianEDist_triangle` (338). No differentiability/geodesic-equation statement for minimizers.
- Levi-Civita: `CovariantDerivative` structure (`VectorBundle/CovariantDerivative/Basic.lean:366`),
  `CovariantDerivative.IsLeviCivitaConnection` (`LeviCivita.lean:201`),
  `CovariantDerivative.leviCivitaConnection` (359),
  `isLeviCivitaConnection_leviCivitaConnection` (408), `IsMetricCompatible` (`Metric.lean:155`).
  Connection only — no parallel transport, no curvature tensor.
- First-order ODE on manifolds: `IsMIntegralCurveOn` (`IntegralCurve/Basic.lean:66`),
  `IsMIntegralCurveAt` (72), `IsMIntegralCurve` (77); local existence
  `exists_isMIntegralCurveAt_of_contMDiffAt [CompleteSpace E]` (`ExistUnique.lean:65`);
  uniqueness `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff` (189).
- Bundles/metrics: `Bundle.RiemannianMetric` (`Topology/VectorBundle/Riemannian.lean:370`),
  `Bundle.RiemannianBundle` (420), `Bundle.ContinuousRiemannianMetric` (468),
  `Bundle.ContMDiffRiemannianMetric`, `IsContinuousRiemannianBundle` (60),
  `IsContMDiffRiemannianBundle` (`Geometry/Manifold/VectorBundle/Riemannian.lean:67`),
  `mfderiv`, `TangentSpace`, `VectorField.mlieBracket` (`VectorField/LieBracket.lean`).

## 2. Gromov–Hausdorff (`Mathlib/Topology/MetricSpace/GromovHausdorff*.lean`)

`GromovHausdorff.lean`:
- `GromovHausdorff.GHSpace : Type` (86) := quotient of `NonemptyCompacts ℓ_infty_ℝ` by isometry,
  `ℓ_infty_ℝ := lp (fun n : ℕ => ℝ) ∞` (local notation, 55). `toGHSpace` (90), `GHSpace.Rep` (97),
  `instMetricSpaceGHSpace` (393), `instCompleteSpaceGHSpace` (938),
  `instSecondCountableTopologyGHSpace` (616).
- `ghDist (X) (Y) [MetricSpace X] [Nonempty X] [CompactSpace X] [MetricSpace Y] [Nonempty Y]
  [CompactSpace Y] : ℝ` (176); `dist_ghDist` (180).
- `ghDist_le_hausdorffDist` (185): `Isometry Φ → Isometry Ψ → ghDist X Y ≤ hausdorffDist (range Φ) (range Ψ)`.
- `ghDist_eq_hausdorffDist` (377): `∃ Φ Ψ, Isometry Φ ∧ Isometry Ψ ∧ ghDist X Y = hausdorffDist (range Φ) (range Ψ)`.
- `ghDist_le_of_approx_subsets` (538): ε₁-dense + ε₃-dense + ε₂-almost-isometric ⇒ `ghDist X Y ≤ ε₁ + ε₂/2 + ε₃`.
- `totallyBounded` (735): `Tendsto u atTop (𝓝 0) → (∀ p ∈ t, diam univ ≤ C) →
  (∀ p ∈ t, ∀ n, ∃ s : Set p.Rep, (#s) ≤ K n ∧ univ ⊆ ⋃ x∈s, ball x (u n)) → TotallyBounded t`.
  Docstring: only this direction is proved (no converse).
- NO subsequence lemma in either GH file (`grep "subseq"` → empty). Generic:
  `IsCompact.tendsto_subseq` (`Topology/Sequences.lean:298`), `IsCompact.tendsto_subseq'` (293),
  `SeqCompactSpace.tendsto_subseq` (277), `isCompact_iff_totallyBounded_isComplete`
  (`Topology/UniformSpace/Cauchy.lean:728`).

`GromovHausdorffRealized.lean`: `candidates` (85), `HD` (250), `premetricOptimalGHDist` (471),
`OptimalGHCoupling` (480), `optimalGHInjl` (485)/`optimalGHInjr` (493) with
`isometry_optimalGHInjl` (489)/`isometry_optimalGHInjr` (497),
`compactSpace_optimalGHCoupling` (502), `hausdorffDist_optimal_le_HD` (513). Also
`ghDist_le_nonemptyCompacts_dist` (505), `toGHSpace_lipschitz` (515).

## 3. Doubling measure / covering numbers: PRESENT (name is NOT `Measure.IsDoubling`)

- `class IsUnifLocDoublingMeasure {α} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α) : Prop`
  — `Mathlib/MeasureTheory/Measure/Doubling.lean:46`; field
  `exists_measure_closedBall_le_mul'' : ∃ C : ℝ≥0, ∀ᶠ ε in 𝓝[>] 0, ∀ x,
  μ (closedBall x (2*ε)) ≤ C * μ (closedBall x ε)` — uniformly **locally** doubling.
- API: `doublingConstant` (63), `eventually_measure_le_doublingConstant_mul` (66),
  `exists_eventually_forall_measure_closedBall_le_mul` (70), `scalingConstantOf` (91),
  `scalingScaleOf` (131), `measure_mul_le_scalingConstantOf_mul` (137), `scalingScaleOf_pos` (134).
  Instances: prod (`Measure/Prod.lean:356`), pi (`Constructions/Pi.lean:551`), `AddCircle`
  volume (`IntervalIntegral/Periodic.lean:121`).
- `Mathlib/Topology/MetricSpace/CoveringNumbers.lean`: `Metric.externalCoveringNumber (ε : ℝ≥0) (A : Set X) : ℕ∞` (71),
  `Metric.coveringNumber` (77), `Metric.packingNumber` (83);
  `packingNumber_two_mul_le_externalCoveringNumber` (330), `coveringNumber_le_packingNumber` (354),
  `coveringNumber_two_mul_le_externalCoveringNumber` (361), `coveringNumber_subset_le` (368),
  `minimalCover` (252), `maximalSeparatedSet` (291).
- Uniform covering numbers: `structure Metric.HasCoveringExponent (A : Set T) (c : ℝ≥0∞) (d : ℝ) : Prop`
  — `Mathlib/Topology/MetricSpace/CoveringExponent.lean:44`; fields `ediam_lt_top`,
  `coveringNumber_le : ∀ ε, ε ≤ ediam A → coveringNumber ε A ≤ c * ε⁻¹ ^ d`; plus
  `coveringNumber_lt_top` (48), `coveringNumber_ne_top` (60), `subset` (65).
- Vitali/Besicovitch: `VitaliFamily` (root ns, `MeasureTheory/Covering/VitaliFamily.lean:68`),
  `FineSubfamilyOn.exists_disjoint_covering_ae` (110), `measure_le_tsum` (171);
  `HasBesicovitchCovering` (`MeasureTheory/Covering/Besicovitch.lean:155`),
  `Besicovitch.exists_disjoint_closedBall_covering_ae` (833),
  `exists_closedBall_covering_tsum_measure_le` (857), `ae_tendsto_measure_inter_div` (1105).
  Also `MeasureTheory.Measure.hausdorffMeasure` (`Measure/Hausdorff.lean`).

## 4. Bishop–Gromov / Ricci bound / doubling→covering: ABSENT, one bridge exists

```
grep -rIn --include=*.lean -E "Bishop|volume comparison|HasRicciBound|RicciBound|curvature-dimension|CurvatureDimension|Lott.Sturm|SturmLiouville|CDCondition" Mathlib/
```
→ EMPTY (exit 1). No Bishop–Gromov, no volume comparison, no CD(K,N), no `HasRicciBound`.

```
grep -rIln --include=*.lean "IsUnifLocDoublingMeasure" Mathlib/ | xargs grep -ln "coveringNumber"
```
→ EMPTY (same for `packingNumber`). No doubling ⇒ covering-number lemma.

Present bridge: `Mathlib/MeasureTheory/Measure/Lebesgue/EqHaar.lean:550-551`
```
instance (priority := 100) Measure.isUnifLocDoublingMeasureOfIsAddHaarMeasure :
  ∀ {E} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure], IsUnifLocDoublingMeasure μ
```
Verified: `example : IsUnifLocDoublingMeasure (volume : Measure (Fin 3 → ℝ)) := inferInstance` compiles
(probe6). Combined with `IsCompact.measure_lt_top`
(`Measure/Typeclasses/Finite.lean:343`, `[IsFiniteMeasureOnCompacts μ] → IsCompact K → μ K < ⊤`)
this gives a chart-local route, but there is no manifold-level statement.

## 5. Volume form / measure / integration / divergence / Stokes

- `Orientation := Module.Ray R (M [⋀^ι]→ₗ[R] R)` — `Mathlib/LinearAlgebra/Orientation.lean:51` (a module, not a manifold).
- `Orientation.volumeForm {E} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n}
  [Fact (finrank ℝ E = n)] (o : Orientation ℝ E (Fin n)) : E [⋀^Fin n]→ₗ[ℝ] ℝ`
  — `Mathlib/Analysis/InnerProductSpace/Orientation.lean:170` (`irreducible_def`); `volumeForm_robust` (198),
  `abs_volumeForm_apply_le` (245).
- `Orientation.measure_eq_volume (o) : o.volumeForm.measure = volume` —
  `Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean:70`; `measure_orthonormalBasis` (57);
  `OrthonormalBasis.addHaar_eq_volume` (91).
- `Module.Basis.addHaar (b : Basis ι ℝ E) : Measure E` — `MeasureTheory/Measure/Haar/OfBasis.lean:254`;
  `isAddHaarMeasure_basis_addHaar` (257); `MeasureTheory.Measure.addHaar` (locally compact additive group)
  and `MeasureTheory.Measure.IsAddHaarMeasure` (`Group/Measure.lean:772`).
- ABSENT on manifolds:
  - `grep -rIn --include=*.lean -E "VolumeForm|volumeForm" Mathlib/Geometry/` → EMPTY
  - `grep -rIn --include=*.lean -E "MeasureSpace|RiemannianMeasure|riemannianVolume" Mathlib/Geometry/Manifold/` → EMPTY
  No `MeasureSpace` instance on any manifold, no μ_g, no integration of forms over manifolds
  (`Geometry/Manifold/PartitionOfUnity.lean:54` only mentions it as motivation). No manifold
  orientation typeclass (doc mention only, `Geometry/Manifold/Instances/Icc.lean:59`).
- Differential forms only on normed spaces: `Mathlib/Analysis/Calculus/DifferentialForm/Basic.lean`
  (`extDeriv` 199, `extDerivWithin`, `extDeriv_pullback` 260); no integration. Line integrals:
  `MeasureTheory/Integral/CurveIntegral/Basic.lean` — `CurveIntegrable` (114), `curveIntegral` (141),
  `curveIntegral_segment` (303) — for `Path a b` in a normed space, not a manifold.
- Divergence/Stokes in coordinates only:
  `MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable`
  (`Mathlib/MeasureTheory/Integral/DivergenceTheorem.lean:266`, box `Icc a b ⊆ Fin (n+1) → ℝ`);
  `BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt`
  (`Mathlib/Analysis/BoxIntegral/DivergenceTheorem.lean:265`). "Stokes" appears nowhere as a theorem.
- `MeasureTheory.IsFiniteMeasureOnCompacts` (`Measure/Typeclasses/Finite.lean:294`) +
  `IsCompact.measure_lt_top` (343) are the usable finiteness tools once μ exists.

## 6. ODE comparison beyond `release/Poincare/D12/ComparisonGeodesics`

Present (first-order / Gronwall only), `Mathlib/Analysis/ODE/`:
- `Gronwall.lean`: `gronwallBound δ K ε x` (~46); `le_gronwallBound_of_liminf_deriv_right_le` (112);
  `norm_le_gronwallBound_of_norm_deriv_right_le` (134); `dist_le_of_approx_trajectories_ODE` (188);
  `dist_le_of_trajectories_ODE_of_mem` (208); `dist_le_of_trajectories_ODE` (228);
  `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` (143).
- `ExistUnique.lean`: `ODE_solution_unique` (326), `ODE_solution_unique_of_mem_Icc` (251),
  `ODE_solution_unique_of_mem_Ioo` (278). `PicardLindelof.lean`: `IsPicardLindelof` (79),
  `exists_eq_forall_mem_Icc_eq_picard` (720). Also `DiscreteGronwall.lean`, `Transform.lean`.
- Absent: no Sturm–Liouville, no Sturm/Sturm–Picone comparison, no Riccati, no second-order
  oscillation comparison. `grep -rIn --include=*.lean -E "sturm|Sturm|riccati|Riccati" Mathlib/Analysis/`
  → EMPTY. "wronskian" only in `RingTheory/Polynomial/Wronskian.lean` and
  `NumberTheory/FLT/MasonStothers.lean` (polynomial Wronskian). `Analysis/Oscillation.lean` is
  function oscillation (discontinuity theory), not ODE oscillation.

## What a new manifold-level compactness/geodesic interface can and cannot build on

CAN build on:
- metric: `Metric.coveringNumber/packingNumber/externalCoveringNumber`, `Metric.HasCoveringExponent`,
  `Metric.totallyBounded_iff`, `IsCompact.tendsto_subseq`, `ProperSpace` +
  `Metric.isCompact_of_isClosed_isBounded`, `IsCompact.measure_lt_top`;
- GH: `GromovHausdorff.GHSpace` (already `CompleteSpace` + `SecondCountableTopology`), `ghDist`,
  `ghDist_le_hausdorffDist`, `ghDist_eq_hausdorffDist` (exact realization),
  `ghDist_le_of_approx_subsets`, `GromovHausdorff.totallyBounded` (ONE direction only),
  `OptimalGHCoupling` for coupling/transfer arguments;
- measure: `IsUnifLocDoublingMeasure` + `Measure.isUnifLocDoublingMeasureOfIsAddHaarMeasure`,
  `Measure.addHaar`/`Module.Basis.addHaar`/`Measure.IsAddHaarMeasure`,
  `Orientation.volumeForm` + `Orientation.measure_eq_volume` on model spaces,
  `VitaliFamily`/Besicovitch, `Measure.hausdorffMeasure`;
- smooth: `IsRiemannianManifold`, `Manifold.pathELength` + `Manifold.riemannianEDist`,
  `CovariantDerivative` + `IsLeviCivitaConnection` + `leviCivitaConnection`,
  `IsMIntegralCurve*` + local existence/uniqueness, `mfderiv`, `VectorField.mlieBracket`,
  `Bundle.RiemannianBundle`/`IsContMDiffRiemannianBundle`.

CANNOT (must be built from scratch):
- geodesic equation / covariant acceleration ∇_{γ'}γ' / geodesic spray / exp map / normal
  coordinates ⇒ no Gauss lemma, no minimizing-geodesic existence (Hopf–Rinow);
- second-order ODE on manifolds (only first-order `IsMIntegralCurve`; "flow" absent entirely) and
  global existence from manifold completeness;
- parallel transport; curvature tensor, sectional/Ricci curvature; injectivity radius; cut locus;
- Bishop–Gromov, volume comparison, CD(K,N), `HasRicciBound`;
- manifold Riemannian volume μ_g (no `MeasureSpace` on manifolds), its doubling property,
  integration of top forms, Stokes/divergence on manifolds, manifold orientation;
- ODE oscillation comparison (Sturm–Liouville/Sturm–Picone/Riccati) to feed Jacobi-field
  comparison — only Gronwall-type first-order comparison exists.

Bottom line: U3 is verified with exact greps. The metric/GH/covering/doubling layer is usable
today; the geodesic/curvature/volume-comparison layer is entirely absent, matching the earlier
project-local conclusion in `Poincare/D7/Geodesic/ManifoldInterfaces.lean` (the single missing
primitive is ∇_{γ'}γ' / the geodesic-spray ODE).
