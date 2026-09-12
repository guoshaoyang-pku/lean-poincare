# D13 ManifoldIBP / Riemannian / VolumeForm — proved-content inventory

Read-only audit. Commands (from `release/`): declaration grep `^(noncomputable )?(private )?(protected )?(def|theorem|lemma|structure|class|abbrev|instance|opaque) `; `lake env lean ../debug/IBPSig.lean` → `debug/IBPSig.out` (imports all 34 modules, `#print` of 7 structures, `#check @` of ~130 decls, 1434 raw lines); `lake env lean ../debug/IBPSig2.lean` (definition bodies); `lake env lean ../debug/IBPAxioms.lean` (`#print axioms`, 7 succeeded); grep consumer + forbidden-token scans. 26 files = 25 modules + barrel `Poincare/D13/ManifoldIBP.lean` (imports only).

Categories: **(a)** proved with analytic hypotheses only, ambient structures inhabited by constructed models; **(b)** conditional on an uninhabited named interface; **(c)** model theorem (Euclidean/chart); **(d)** statement-only `Prop`.

## 1. Inventory (binding order; full raw signatures in debug/IBPSig.out)

**Blocked.lean — (d).** `manifoldGluingConstructionExists := ∀ n ι A, True`; `smoothPartitionOfUnityExists := ∃ M _ _, True`; `closedManifoldEntropyIdentity := ∀ n G f, ContDiff ℝ 2 f → ∫ x, G.laplacian f x * e^{-f x} * G.density x = ∫ x, G.gradInnerInverse f f x * e^{-f x} * G.density x`; `manifoldStokesTheorem := False`; `orientedAtlasVolumeForm := False`. None used as a hypothesis anywhere.

**ChartSum.lean — (c).** `structure ChartSumData (n ι) := (metric : Fin ι → ChartMetric (n+1))`; `density, driftLaplacian, gradInnerInverse, laplacian, divergence`, `globalIntegral D f g = ∑ᵢ ∫ gᵢ·e^{-fᵢ}·ρᵢ`, `globalIntegralUnweighted`. Theorems (analytic hyps only): `globalWeightedIBP` (107), `globalLaplacianIntegralZero` (125), `globalDivergenceIntegralZero` (136), `globalUnweightedIBP` (148).

**DisjointModel.lean — (c).** `DisjointAtlas n ι := Fin ι × Vec (n+1)`; `weightedChartMeasure`, `integral_weightedChartMeasure`, `disjointAtlasMeasure`, `integral_disjointAtlasMeasure`, `disjointAtlasData : ManifoldAtlasData (Fin ι × Vec (n+1)) n ι`, four `integrable_*`, `disjointAtlas_weightedIBP` (246).

**GlobalMeasure.lean — (a) core / (c) model.** `structure OverlapAtlas (M) [MeasurableSpace M] (d)`: `chart : ℕ → Vec d → M`, `source`, `isOpen_source`, `measurable_chart`, `injOn_chart`, `cover : ⋃ i, chart i '' source i = univ`, `measurableSet_image`, `metric : ℕ → ChartMetric d`, `transition`, `transition_mem/_chart/_diff`, `metric_transform : (metric j).matrix y = Jᵀ (metric i).matrix (τ y) J`. Defs `overlapOf`, `jacobianOf ψ s y = toMatrix (fderivWithin ℝ ψ s y)`, `density`, `chartPreimage`, `chartMeasure`, `chartPiece`, `globalMeasure`. Results: `det_jacobianOf` (125), `density_transform : ρ_j y = ρ_i (τ y)·|det (fderivWithin τ s y)|` (155), `chartMeasure_apply` (192), **`chartMeasure_apply_eq`** (216, chart-independence of the measure), `globalMeasure_apply_chart` (300), `globalMeasure_smul`, `globalMeasure_restrict_eq_chartMeasure` (362), `globalMeasure_eq_chartMeasure_of_cover` (376).

**IntegrableTransfer.lean — (a).** `integrable_chartMeasure_iff` (55), `integrable_globalMeasure_iff` (78), `integrable_globalMeasure_withDensity_of_supported` (99).

**Transfer.lean — (b).** `structure ManifoldAtlasData (M) [MeasurableSpace M] (n ι)`: `μ`, `chart : Fin ι → Vec (n+1) → M`, `metric`, `drift`, **`integral_decomp`** (= B-D13-MANIFOLD-GLUING), `driftLaplacianM`, `gradInnerM`, **`weighted_laplacian_compat`**, **`grad_inner_compat`**. `laplacianIntegral_eq_chartSum` (82), `gradInnerIntegral_eq_chartSum` (106), `manifoldWeightedIBP_of_atlasData` (131).

**OverlapIBP.lean — (a).** Top level `integral_eq_restrict_of_support` (57), `setIntegral_eq_integral_of_support` (72). In `OverlapAtlas`: `weight f m = ofReal (e^{-f m})`, `integral_chartMeasure_of_supported` (112), `integral_globalMeasure_of_supported` (138), `integral_globalMeasure_withDensity_of_supported` (151), **`globalWeightedIBP_of_chartSupported`** (186), `…_smul` (276), `globalIBP_of_chartSupported` (319), `globalLaplacianIntegralZero_of_chartSupported` (361).

**GlobalIBP.lean — (a).** `gradInnerInverse_finset_sum` (57); `OverlapAtlas.globalWeightedIBP_finset` (99), `globalIBP_finset` (152).

**OverlapModel.lean — (c).** `dilateMetric`, `dilationChart/Metric/Transition`, `dilationAtlas` (220), `dilationAtlas_chartMeasure_univ_eq` (288), `dilationAtlas_globalMeasure_eq_chartMeasure` (300).

**OverlapIBPModel.lean — (c).** `dilationAtlasTwo` (44), `…_integral_eq_chart` (90), `…_weightedIBP` (118), `…_chart` (161), `…_ibp` (187), `…_laplacianIntegralZero` (210), `…_dirichletEnergy` (224).

**OverlapIBPData.lean — (c) inhabiting (b).** `dilationAtlasTwo_globalMeasure_eq_chartMeasure`, `…_chartMeasure_absolutelyContinuous`, `dilationAtlasTwoData : ManifoldAtlasData (Vec (n+1)) n 1` (79), `…_weightedIBP` (109).

**OverlapOperatorCheck.lean — (a).** `dilateMetric_gradInnerInverse` (78), `dilationAtlasTwo_gradInnerInverse_chart_independent` (110), `dilateMetric_density/grad/weightedDivergence/laplacian/driftLaplacian`, `dilationAtlasTwo_driftLaplacian_chart_independent` (221), `…_weightedIBP_chartOne` (239), two chartOne integral identities.

**SmoothPartition.lean — (a), Euclidean.** `exists_contDiff_bump` (44), `exists_smooth_partitionOfUnity_subordinate` (111): finite open cover of a compact set in `Vec d`.

**POUAssembly.lean — (a).** `eq_sum_of_pou` (50), `globalWeightedIBP_of_pouData` (80). **POUAssemblyAE.lean — (a).** `setIntegral_eq_integral_of_ae_support` (37), `globalWeightedIBP_of_chartSupported_ae` (52), `…_finset_ae` (137), `…_of_pouData_ae` (192).

**SmoothAtlas.lean — (a).** `structure SmoothOverlapAtlas` extends `OverlapAtlas` with `isOpen_overlap`, `inj_chart`, `measurable_readback : Measurable (invFunOn (chart i) (source i))`, `contDiff_transition`, `transition_chart_global`; `lift` (62) + `lift_apply_chart`, `support_lift_subset`, `measurable_lift`, `lift_apply_chart_of_mem`, `support_lift_subset_tsupport`.

**SmoothAtlasIBP.lean — (a), total atlases.** `IsTotal` (56), `pouPiece`, `pouPairing`, `sum_pouPairing` (136), `globalWeightedIBP_of_pou` (210), `…_of_pou'` (347).

**SmoothAtlasPartial.lean — (a).** `lift_apply_chart_of_support` (67), `pouPiece_chart_of_support` (87), `gradInnerInverse_eq_zero_of_eventuallyEq_zero` (112), `sum_pouPairing_of_support` (128), `globalWeightedIBP_of_pou_partial` (270). **SmoothAtlasPartialAE.lean — (a).** `support_pouPairing_subset_chart` (44), `globalWeightedIBP_of_pou_partial_ae` (58, null-boundary).

**SmoothAtlasModel.lean — (c).** `dilationAtlasTwoSmooth` (42), `…_isTotal` (107), `…_weightedIBP_via_pou` (129). **POUModel.lean — (c).** `exists_pou_dilationTwo` (50), `dilationAtlasTwo_pou_pairing_reassembly` (116), `…_pou_weightedIBP` (170).

**POUConstruction.lean — (a).** **`SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae`** (60, POU constructed internally, integrability derived); `OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover` (251), `…_chartOne` (358).

**PartialChartModel.lean — (c).** `hsChart/hsSource/hsMetric`, `halfSpaceAtlas : SmoothOverlapAtlas (Vec (n+1)) (n+1)` (200), `halfSpaceAtlas_frontier_volume_zero` (440), `source_ne_univ` (451), `not_isTotal_halfSpaceAtlas` (466), `transition_coherence` (473), `transition_preimage_isCompact` (501), `hsAtlas` (529), `halfSpaceAtlas_weightedIBP_of_pou_partial_ae` (540).

**PartialChartModelPOU.lean — (c), side-condition-free.** `hsStep`, `hsPsi` + ~14 support/smoothness lemmas; **`halfSpaceAtlas_weightedIBP_unconditional`** (192), `…_dirichletEnergy` (470), `…_greenIdentity` (484), `…_integrable_dirichlet` (511), `support_laplacian_subset` (585), `…_laplacianIntegralZero` (629).

**VolumeFormBridge.lean — (a).** `chartVolumeForm_stdFrame_eq_density` (41), `globalMeasure_apply_chart_volumeForm` (51), `…_of_cover` (64), `dilationAtlasTwo_volume_univ` (76).

**Riemannian (all (a)).** `AtlasBridge`: `jacobianOf_eq_toMatrix` (60), `chartMetricMatrix` (70), `metric_transform_chartTransition` (80), `fderivWithin_chartTransition_eq_of_isOpen` (96), `chartOverlap` (104), `chartOverlap_eq_overlapOf` (111), `metric_transform_chartOverlap` (124). `AtlasPairing` (ns `ManifoldIBP.OverlapAtlas`): `gradInnerInverse_chartTransition` (60), `…_mul` (90). `ChartMetricBridge`: `chartMetricCoeff(Ext)`, `contDiffOn_chartMetricCoeff` (76), `contDiff_chartMetricCoeffExt_mul` (84), `posDef_chartMetricCoeffExt` (111), `structure SmoothChartMetric` (134), `extendedSmoothChartMetric` (145), `…_g_eq_genuine` (179), `extendedChartMetric` (222), `…_g_eq_genuine` (258). `MetricBridge`: `trivializationAt_symm_eq_tangentCoordChange` (80), `chartGramMatrix` (113), `chartGramMatrix_eq_inner` (130), `chartFrameVec_eq_symm_tangentCoordChange` (137), `chartGramMatrix_change` (188), **`chartGramMatrix_det_change`** (208), `chartGramMatrix_sqrt_det_change` (221), `tangentCoordChange_eq_fderivWithin_chartTransition` (244), `chartGramMatrix_isHermitian` (271), `…_posDef` (298), `…_det_pos` (348). `MetricBridgeSmooth`: `contMDiffOn_chartFrameSection` (49), `contMDiffOn_chartGramMatrix_entry` (84), `contDiffOn_chartGramMatrix_coord` (98). `PullbackPairing`: `gradInnerInverse_congruence` (129), `gradInnerInverse_pullbackMetric` (176).

**VolumeForm (all (a)).** `Basic`: `stdOrientation` (99), `euclideanVolumeForm` (105), `…_apply` (109), `orientationVolumeForm_eq_basisDet` (125), `euclideanVolumeForm_stdFrame` (140), `chartVolumeForm G x = G.density x • euclideanVolumeForm d` (151), `chartVolumeForm_apply` (157), `…_positive_on_standardFrame` (174), `signedVolume` (203), `signedVolume_orthonormal_basis_invariant` (227). `Gluing`: `structure ChartPartitionOfUnity` (43), `exists_pos` (56), `gluedDensity` (66), `gluedDensity_eq_of_supportCompatible` (101), `integral_gluedDensity_eq_sum` (123). `Transformation`: `det_matrix_of_fderiv_frame` (61), `chartVolumeForm_pullback_general` (80), `…_orientationPreserving(_map)` (105/116), `…_euclidean` (128).

## 2. Strongest genuinely proved theorem

**General engine: `Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae` (POUConstruction.lean:60).**
```
∀ {M} [MeasurableSpace M] {n} {A : SmoothOverlapAtlas M (n+1)},
 (∀ i j y, A.chart j y ∈ A.chart i '' A.source i → A.transition i j y ∈ A.source i) →
 ∀ (b) {ι} [Fintype ι] (chartOf : ι → ℕ) (f u v Du Guv : M → ℝ),
 Measurable f → Measurable v → Measurable Du → Measurable Guv →
 (∀ m, v m ≠ 0 → m ∈ A.chart b '' A.source b) →
 (∀ i, ContDiff ℝ 2 (f ∘ A.chart i)) → (∀ i, ContDiff ℝ 2 (u ∘ A.chart i)) →
 (∀ i, ContDiff ℝ 2 (v ∘ A.chart i)) →
 HasCompactSupport (v ∘ A.chart b) → tsupport (v ∘ A.chart b) ⊆ A.source b →
 A.chart b '' A.source b ⊆ ⋃ j, A.chart (chartOf j) '' A.source (chartOf j) →
 (∀ i y, y ∈ A.source i → Du (A.chart i y) = (A.metric i).driftLaplacian (f∘chart i) (u∘chart i) y) →
 (∀ i y, y ∈ A.source i → Guv (A.chart i y) = (A.metric i).gradInnerInverse (u∘chart i) (v∘chart i) y) →
 (∀ m, Guv m ≠ 0 → m ∈ A.chart b '' A.source b) →
 (∀ i j K, IsCompact K → IsCompact (A.transition i j ⁻¹' K)) →
 (∀ i, volume (frontier (A.source i)) = 0) →
 ∫ m, Du m * v m ∂(A.globalMeasure volume).withDensity (A.weight f)
   = -∫ m, Guv m ∂(A.globalMeasure volume).withDensity (A.weight f)
```
Consumes an inhabited `SmoothOverlapAtlas` (globally injective charts, measurable readbacks, globally C² transitions, metric tensor law), a finite chart cover of the support, proper transitions, null chart boundaries, and the operator identifications `Du`, `Guv`. Produces the weighted Green/IBP identity on the **glued overlapping-atlas measure** `(globalMeasure volume).withDensity (e^{-f})`. No POU data and no integrability hypotheses: both are constructed.

**Unconditional end of the chain: `OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional` (PartialChartModelPOU.lean:192).**
```
∀ {n} (G : ChartMetric (n+1)) (f u v : Vec (n+1) → ℝ),
 ContDiff ℝ 2 f → ContDiff ℝ 2 u → ContDiff ℝ 2 v →
 HasCompactSupport v → tsupport v ⊆ {y | y 0 < 1} →
 ∫ m, G.driftLaplacian f u m * v m ∂((hsAtlas G).globalMeasure volume).withDensity ((hsAtlas G).weight f)
   = -∫ m, G.gradInnerInverse u v m ∂(… same measure …)
```
No atlas/POU/integrability/cover hypothesis at all; ambient space is the model `Vec (n+1) = Fin (n+1) → ℝ` with the concrete two-chart partial half-space atlas `hsAtlas G` (identity on `{y₀<1}`, dilation by 2 on `{0<y₀}`). It is a genuine glued-overlapping-atlas statement but **not** stated over an abstract `ChartedSpace` manifold. `#print axioms` for both: `[propext, Classical.choice, Quot.sound]` only. Corollaries: `halfSpaceAtlas_dirichletEnergy`, `…_greenIdentity`, `…_integrable_dirichlet`, `…_laplacianIntegralZero`. Other end-points: `ChartSumData.globalWeightedIBP` (disjoint chart sum), `dilationAtlasTwo_weightedIBP`, `manifoldWeightedIBP_of_atlasData` (abstract `M`, conditional), `VolumeFormBridge.globalMeasure_apply_chart_volumeForm`.

## 3. Downstream consumers outside the owning file

**None.** Full-tree search for every principal name found only: barrel `Poincare/D13/ManifoldIBP.lean:1–25`; audit `Poincare/D13/Audit.lean:84,85,89,92,255,258,259,266,267,295,338,339,358,387,388,393,403,407,408,409,411,439,447` (`#print axioms` lines, not mathematical uses); docstring mention only at `Poincare/D13/Bridge.lean:273`. `Poincare/D13/Riemannian/AtlasPairing.lean:54–101` proves `gradInnerInverse_chartTransition` **from** the `OverlapAtlas.metric_transform` field and is consumed **by** `ManifoldIBP/SmoothAtlasPartial.lean:23` — upstream input, not a consumer. No file under `Poincare/Stage1`, `Stage6`, `Poincare/L4` imports any `Poincare.D13.ManifoldIBP.*`, `.Riemannian.*` or `.VolumeForm.*` module. The layer is terminal.

## 4. Remaining gaps to a manifold-level divergence theorem

1. **No mathlib-manifold → atlas bridge.** Every IBP theorem is over `OverlapAtlas`/`SmoothOverlapAtlas`/`ManifoldAtlasData` on a bare measurable space with explicit chart parametrizations. Nothing constructs an `OverlapAtlas M d` from `[ChartedSpace H M] [IsManifold I ∞ M] [Bundle.RiemannianBundle (TangentSpace I)]`. `Riemannian.MetricBridge`/`AtlasBridge`/`ChartMetricBridge` supply the ingredients (chart Gram matrix, tensor law, smooth coefficient extension) but no instance. The `M` in the IBP layer carries no tangent bundle or manifold structure.
2. **Smooth POU on a manifold (B-D13-SMOOTH-POU).** Only the Euclidean `exists_smooth_partitionOfUnity_subordinate` exists; on `M` the layer assumes globally injective charts with measurable readbacks plus an explicit finite cover `hcover` and builds the POU in the base chart.
3. **Measure gluing (B-D13-MANIFOLD-GLUING).** `ManifoldAtlasData.integral_decomp` is an interface field, inhabited only by the disjoint atlas and the dilation-chart atlas; overlapping-atlas well-definedness is proved (`chartMeasure_apply_eq`, `globalMeasure`) but only for the explicit-chart `OverlapAtlas`.
4. **Closed-manifold entropy identity (B-D13-CLOSED-MANIFOLD).** `v ≡ 1` is not compactly supported; needs compact `M`, finite atlas, finite POU sum. `closedManifoldEntropyIdentity` is statement-only (Blocked.lean:60).
5. **Boundary/Stokes (B-D13-STOKES).** No `∂M`, outward normal or boundary measure; `manifoldStokesTheorem := False` (Blocked.lean:71). Manifold-level divergence exists only as the Laplacian form `∫ ΔV dμ = 0` for chart-supported `V`.
6. **Orientation / volume forms (B-D13-ORIENTED-ATLAS).** `chartVolumeForm` is chart-level; gluing forms needs an oriented atlas with orientation-compatible transitions (chart law proved in `VolumeForm.Transformation`); no global form on `M`, no integration of forms in the pin; `orientedAtlasVolumeForm := False` (Blocked.lean:78).
7. **U7-GLOBAL-LIFT** is closed only for total atlases (`IsTotal`) and null-boundary partial atlases; a general atlas without global injectivity/measurable readback lacks lifted pieces.

Suggested next consumer: the mathlib-manifold → `SmoothOverlapAtlas` bridge (gaps 1+2), which would turn `globalWeightedIBP_of_cover_partial_ae` into a theorem about `[ChartedSpace H M] [IsManifold I ∞ M] [RiemannianBundle (TangentSpace I)]`.

## 5. Forbidden-token scan (`Poincare/D13/**`, `Poincare/L4/**`)

`grep -rn -E "sorry|admit|axiom |unsafe|native_decide|proof_wanted"` → 71 raw hits, all inspected; plus precise `^\s*sorry`, `^\s*admit`, `^\s*axiom `, `^\s*(unsafe|@\[unsafe)` scans.
- `sorry` tactic, `admit`, `unsafe` declaration, `native_decide` invocation, `proof_wanted` declaration: **none found**. All matches are docstring prose ("no `sorry`, … in this file"), detector code in `Poincare/D13/CriticalPathReview/AxiomAudit.lean` (`sorryAxiom : Name := ``sorryAx`, `.«unsafe»`, `native_decide` strings), or comments (`CertificateOn.lean:136`; `Poincare/L4/AxiomAudit.lean:5,7,13`).
- Real `axiom` declarations (2, both deliberate negative controls unused by any proof): `Poincare/D13/Audit.lean:44` `axiom negativeControl : False`; `Poincare/D13/CriticalPathReview/NegControl.lean:17` `axiom negControlBadAxiom : False` (documented as never imported by a proof module).
- Supporting evidence: `#print axioms` on `halfSpaceAtlas_weightedIBP_unconditional`, `globalWeightedIBP_of_cover_partial_ae`, `globalWeightedIBP_of_pou_partial_ae`, `globalWeightedIBP_of_chartSupported`, `manifoldWeightedIBP_of_atlasData`, `ChartSumData.globalWeightedIBP`, `chartVolumeForm_pullback_general` → all `[propext, Classical.choice, Quot.sound]`, so the whole proof cone (including the D12 chart theorems it bottoms out in) is free of `sorryAx` and project axioms.
