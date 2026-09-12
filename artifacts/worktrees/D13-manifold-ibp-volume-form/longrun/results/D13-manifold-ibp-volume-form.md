# D13-manifold-ibp-volume-form — result card

**Task id:** `D13-manifold-ibp-volume-form`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-manifold-ibp-volume-form`
**Generated (UTC):** 2026-09-11T11:33:00Z
**Verdict:** `TASK_DONE` — the milestone is complete on the release pin: the Riemannian volume
measure and the manifold integration-by-parts layer are constructed (chart layer, overlapping
atlas gluing with chart-independence, Euclidean and atlas partitions of unity, lifted pieces,
global IBP), the named blockers `I4` and `U7` of the D12 semantic ledger are discharged with
**constructed downstream checked uses**, and each target theorem is either unconditional or an
explicit conditional interface with all hypotheses listed. Invocation 7 closes the last
bookkeeping residuals of the atlas layer: **integrability** of the lifted pieces is transferred
from the chart to the glued measure (`IntegrableTransfer`), the **partition of unity** as well
as the integrability are *constructed* from a finite chart cover
(`SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae`), and the genuinely partial
half-space atlas now satisfies the atlas IBP **with no hypotheses left** beyond `C²` data and
compact support of the test function in a chart source
(`halfSpaceAtlas_weightedIBP_unconditional`), with the Green identity, the Dirichlet energy
identity, the divergence theorem `∫ Δ_g V dμ_g = 0` and non-vacuity (integrability of both
sides) as consumed consequences. The full
release builds (`lake build`, 9003 jobs, exit 0) with `D6AUDIT VERDICT PASS` and every audited
axiom cone inside `{propext, Classical.choice, Quot.sound}`.

## 0. Bottom line

| item | result |
| --- | --- |
| new Lean files this invocation | **3**: `ManifoldIBP/IntegrableTransfer.lean` (126 lines, 3 decls), `ManifoldIBP/PartialChartModelPOU.lean` (678 lines, 29 decls), `ManifoldIBP/POUConstruction.lean` (482 lines, 3 decls); umbrella + audit extended |
| integrability of the lifted pieces | **closed**: `integrable_chartMeasure_iff`, `integrable_globalMeasure_iff`, **`integrable_globalMeasure_withDensity_of_supported`** — a chart-supported function is integrable for the entropy-weighted glued measure as soon as its weighted chart expression is integrable |
| partition of unity on the atlas | **constructed** from a finite chart cover by `exists_smooth_partitionOfUnity_subordinate` (cut down by a ball for compact support) in **`globalWeightedIBP_of_cover_partial_ae`**; no POU data remains a hypothesis |
| fully unconditional partial-atlas IBP | **`halfSpaceAtlas_weightedIBP_unconditional`**: on the genuinely partial atlas `halfSpaceAtlas` (identity on `{y 0 < 1}`, dilation by `2` on `{0 < y 0}`), for `C²` `f, u, v` with `v` compactly supported and `tsupport v ⊆ {y 0 < 1}` — no atlas, POU, measurability or integrability hypotheses remain |
| second route and second base chart | **`halfSpaceAtlas_weightedIBP_of_cover`** (the general cover theorem applied with base chart `0`) and **`halfSpaceAtlas_weightedIBP_of_cover_chartOne`** (base chart `1`, test function supported in `{0 < y 0}` — not covered by the hand-built POU) |
| consumed consequences | **`halfSpaceAtlas_dirichletEnergy`** (`∫ (Δ_F V)·V = -∫ |∇V|²`), **`halfSpaceAtlas_greenIdentity`** (`∫ (Δ_F U)·V = ∫ U·(Δ_F V)`), **`halfSpaceAtlas_laplacianIntegralZero`** (the divergence theorem `∫ Δ_g V dμ_g = 0`), **`halfSpaceAtlas_integrable_dirichlet`** (both integrands are integrable: the identities are not vacuous) |
| full release package `lake build` | **exit 0 (9003 jobs)**; `D6AUDIT VERDICT PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no unapproved axiom, no proof_wanted` |
| axiom audit (`Poincare.D13.Audit`, 347 `#print axioms`) | **346 printed cones, all ⊆ {propext, Classical.choice, Quot.sound}** except the intentional negative control; `grep sorryAx` = 0 |
| forbidden-token scan | **exactly 1 hard token over the whole 47-file D13 tree**: the intentional `axiom negativeControl` (unused by any theorem); no `sorry`/`admit`/`unsafe`/`native_decide`/`proof_wanted` |

## 1. What is newly proved this invocation (all kernel-checked, axioms ⊆ {propext, Classical.choice, Quot.sound})

### 1a. `Poincare.D13.ManifoldIBP.IntegrableTransfer` — integrability transfer (3 decls)

* **`integrable_chartMeasure_iff`** — integrability against the `i`-chart measure is equivalent
  to integrability of the chart expression `y ↦ g (chart i y) · ρ_i(y)` against the reference
  measure restricted to the chart source (`integrable_map_measure` +
  `integrable_withDensity_iff_integrable_smul₀'`).
* **`integrable_globalMeasure_iff`** — for a function supported in the `i`-th chart image, the
  global (glued) measure may be replaced by the chart measure (the chart-independence theorem
  `globalMeasure_restrict_eq_chartMeasure` read as an integrability statement).
* **`integrable_globalMeasure_withDensity_of_supported`** — the entropy-weighted form: a
  chart-supported function is integrable for `(globalMeasure μ).withDensity (e^{-f})` as soon as
  its weighted chart expression is integrable against `μ`. This removes the systemic
  `Integrable` residual of the invocations 1–6 atlas IBP theorems for compactly supported smooth
  pieces.

### 1b. `Poincare.D13.ManifoldIBP.PartialChartModelPOU` — explicit POU and the unconditional partial-atlas IBP (27 decls)

* **`hsStep`** — the smooth step `y ↦ smoothTransition (4 * y 0 - 1)` (`Real.smoothTransition`):
  `0` for `y 0 ≤ 1/4`, `1` for `1/2 ≤ y 0`, with `tsupport ⊆ {0 < y 0}`.
* **`hsPsi χ`** — the two-chart POU `ψ 0 = χ · (1 - step)`, `ψ 1 = χ · step`, with
  `contDiff_hsPsi`, **`hsPsi_sum`** (`ψ 0 + ψ 1 = χ`), the support lemmas
  (`support (ψ 0) ⊆ {y 0 < 1/2}`, `tsupport (ψ 1) ⊆ {0 < y 0}`, `tsupport (ψ j) ⊆ tsupport χ`)
  and **`hasCompactSupport_hsPsi`**.
* **`halfSpaceAtlas_weightedIBP_unconditional`** — the weighted IBP on the partial atlas
  `halfSpaceAtlas` for `C²` `f, u, v` with `v` compactly supported and
  `tsupport v ⊆ {y 0 < 1}`. **No hypotheses remain** beyond this test data: the POU is
  constructed from a bump `χ` produced by `exists_contDiff_bump` (support in
  `{y 0 < 1} ∩ ball (R+1)`), the chart identifications `hD`/`hG` are
  `dilateMetric_driftLaplacian` / `dilateMetric_gradInnerInverse`, the structural hypotheses
  (`htrans`, `hproper`, `hbd`) are the invocations-6 theorems
  (`halfSpaceAtlas_transition_coherence`, `halfSpaceAtlas_transition_preimage_isCompact`,
  `halfSpaceAtlas_frontier_volume_zero`), and the integrability is §1a.
* **`halfSpaceAtlas_dirichletEnergy`** — `∫ (Δ_F V)·V d(e^{-F} μ_g) = -∫ |∇V|²_{G⁻¹} d(e^{-F} μ_g)`.
* **`halfSpaceAtlas_greenIdentity`** — `∫ (Δ_F U)·V = ∫ U·(Δ_F V)` (the IBP applied twice;
  `⟨∇U,∇V⟩` is symmetric by `ChartMetric.gradInnerInverse_comm`).
* **`halfSpaceAtlas_integrable_dirichlet`** — both Dirichlet integrands are integrable for the
  weighted glued measure, so the two identities above are not vacuous.
* **`support_laplacian_subset`** — `support (Δ_g u) ⊆ tsupport u` (locality of the Laplacian,
  proved from the definitions `laplacian`/`divergence`/`weightedDivergence`/`grad`).
* **`halfSpaceAtlas_laplacianIntegralZero`** — the **divergence theorem** on the partial atlas:
  `∫_M Δ_g V dμ_g = 0` for `C² V` with topological support in the base chart source, by
  transferring the manifold integral to the base chart and applying D12's
  `laplacian_integral_eq_zero`.

### 1c. `Poincare.D13.ManifoldIBP.POUConstruction` — constructed POU and integrability at the general level (3 decls)

* **`SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae`** — the general global weighted
  IBP for partial charts with null-boundary sources where the partition of unity **and** the
  integrability are constructed. Beyond the atlas structure (`htrans`, `hproper`, `hbd`) the
  only geometric input is a finite chart cover of the base chart image
  (`hcover : chart b '' source b ⊆ ⋃ j, chart (chartOf j) '' source (chartOf j)`) plus the
  standard test-data conditions (`C²` chart expressions, compact support of `v ∘ chart b`,
  `tsupport (v ∘ chart b) ⊆ source b`, operator identifications `hD`/`hG`). The POU comes from
  `exists_smooth_partitionOfUnity_subordinate` applied to the open cover
  `overlapOf chart source (chartOf j) b ∩ ball 0 (R+1)` of the compact set
  `tsupport (v ∘ chart b)` (the ball makes the pieces compactly supported); integrability is
  proved by writing each piece/pairing chart expression as `Φ · 1_{source i}` with `Φ`
  continuous and compactly supported (`Integrable.mono` + §1a).
* **`OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover`** — the general theorem applied to the
  half-space model with base chart `0` (second route to the model result).
* **`OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover_chartOne`** — the same applied with base
  chart `1` (dilation chart), covering test functions supported in the second half-space
  `{0 < y 0}`: a genuinely new instance that the hand-built (chart-`0`-tied) `hsPsi` does not
  provide.

## 2. The layer accumulated in invocations 1–6 (unchanged, still checked)

The chart layer `Poincare.D12.VolumeIBP` (Riemannian density, chart divergence theorem,
`chart_weighted_ibp`, Bochner formula) is consumed by:

* **Volume measure.** `OverlapAtlas` + `chartMeasure` + **`chartMeasure_apply_eq`** (the
  Jacobian/density cancellation) + **`globalMeasure`** glued from a countable overlapping atlas +
  `globalMeasure_apply_chart`, `globalMeasure_restrict_eq_chartMeasure`,
  `globalMeasure_eq_chartMeasure_of_cover`, and the volume-form bridge
  `globalMeasure_apply_chart_volumeForm`; the concrete overlapping model `dilationAtlas`
  (`c • 1` Jacobian) inhabits it, and `dilationAtlasTwoData` inhabits `ManifoldAtlasData` with a
  **proved** `integral_decomp` (this is the D13→D4/D7 interface consumption for `U7`).
* **Manifold IBP.** `globalWeightedIBP_of_chartSupported`, the finite-decomposition assembly
  (`globalWeightedIBP_finset`, `globalWeightedIBP_of_pouData`), the Euclidean POU
  (`exists_contDiff_bump`, `exists_smooth_partitionOfUnity_subordinate`), the pairing
  chart-independence (`inv_congruence`, `gradInnerInverse_congruence`,
  `OverlapAtlas.gradInnerInverse_chartTransition`), the lift and POU pieces
  (`SmoothOverlapAtlas.lift`, `pouPiece`, `pouPairing`, `sum_pouPairing`,
  `globalWeightedIBP_of_pou`, `globalWeightedIBP_of_pou'`), the partial-chart layer
  (`lift_apply_chart_of_support`, `sum_pouPairing_of_support`,
  `globalWeightedIBP_of_pou_partial`), the almost-everywhere/null-boundary layer
  (`setIntegral_eq_integral_of_ae_support`, `globalWeightedIBP_of_chartSupported_ae`,
  `globalWeightedIBP_finset_ae`, `globalWeightedIBP_of_pouData_ae`,
  `globalWeightedIBP_of_pou_partial_ae`), and the genuinely partial model `halfSpaceAtlas`
  (`not_isTotal_halfSpaceAtlas`, `halfSpaceAtlas_frontier_volume_zero`,
  `halfSpaceAtlas_transition_coherence`, `halfSpaceAtlas_transition_preimage_isCompact`).
* **I4 (Gaussian model).** `BochnerFlat.bochnerIdentityOn_euclidean`,
  `GaussianF.contDiffOn_gaussianF`, `HeatBridge.gaussian_conjugate_heat`,
  `restrictedWeightedIBP_euclideanChartCalculus`, packaged by
  `HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian` and consumed as
  `monotoneOn_F_gaussian`, `F_gauss_mono`, `F_gauss_initial_le`,
  `monotoneCertificate_gaussian`; W-side: `W_gaussEntropyData`, `W_gauss_antitone`,
  `hasDerivAt_gaussianW`. The unrestricted D7 Props are kernel-checked **false**
  (`Bridge.RealCalculus.unrestrictedWeightedIBPStatement_false`), which is itself part of the
  discharge: the honest restricted forms are the ones proved.

## 3. Expanded hypotheses (what each theorem assumes, honestly)

1. **`globalWeightedIBP_of_cover_partial_ae`** (general, constructed POU): atlas hypotheses
   `htrans` (coherence), `hproper` (proper transitions), `hbd` (null source frontiers); a finite
   chart cover `hcover` of the base chart image; `C²` chart expressions of `f, u, v`;
   `HasCompactSupport (v ∘ chart b)`; `tsupport (v ∘ chart b) ⊆ source b`; `v` supported in the
   base chart image; the operator identifications `hD`/`hG` on the sources; measurability. It
   does **not** assume a POU, its compact support, or integrability of any piece.
2. **`halfSpaceAtlas_weightedIBP_unconditional`** (model): `C²` `f, u, v`, `v` compactly
   supported with `tsupport v ⊆ {y 0 < 1}`. Nothing else — the atlas, POU, chart
   identifications, measurability and integrability are all constructed. (The support condition
   is necessary: the piece `v ∘ chart 0` must have compact support inside the base chart source
   for the POU to exist at all.)
3. **`halfSpaceAtlas_weightedIBP_of_cover_chartOne`**: the same with `tsupport v ⊆ {0 < y 0}`
   (base chart `1`).
4. **`halfSpaceAtlas_greenIdentity` / `_dirichletEnergy`**: two `C²` compactly supported
   functions with topological support in the base chart source.
5. **`integrable_globalMeasure_withDensity_of_supported`**: measurability of `f` and `g`,
   support of `g` in one chart image, and integrability of the weighted chart expression.
6. **Pre-existing interfaces unchanged**: the *general* partial theorem
   `globalWeightedIBP_of_pou_partial_ae` still takes explicit POU data (now shown constructible
   by §1c); `ManifoldAtlasData` still takes `integral_decomp` and the operator compatibility
   (inhabited with proofs for the models); `ChartMetric.smooth` at the D12 pin still asks for
   `ContDiff ℝ ⊤` (= analytic) coefficients, the honest `C^∞` variant being
   `SmoothChartMetric`.
7. **No hypothesis is equivalent to a conclusion.** The POU is *produced* from the cover and a
   bump, the chart identifications are the D12 dilation chart-independence lemmas, the
   integrability is *transferred* from explicitly bounded compactly supported expressions, and
   the IBP itself is the D12 chart theorem assembled through the constructed pieces; the
   Green/Dirichlet identities are consumed consequences, and their non-vacuity is proved.

## 4. Semantic class

* **Proved theorem (unconditional):** the integrability-transfer lemmas; the constructed-POU
  general cover theorem (given the listed standard geometric hypotheses); the explicit-POU
  unconditional IBP on the partial half-space atlas and its two cover-route instances; the Green
  identity, Dirichlet energy and integrability of both sides; the Euclidean bump/POU layer; the
  chart-level volume form, divergence theorem, IBP and Bochner formula; the entire I4 Gaussian
  package and its `FiniteLifetimeEntropyBridge` consumption; the volume-measure gluing and
  chart-independence.
* **Conditional interface (explicit hypotheses):** `globalWeightedIBP_of_pouData` /
  `globalWeightedIBP_of_pou` / `globalWeightedIBP_of_pou_partial` with supplied POU data;
  `ManifoldAtlasData` and `ChartSumData`; `FiniteLifetimeEntropyBridge` (for data other than the
  Gaussian); the metric-tensor packaging of the atlas layer (the tensor law itself is proved).
* **Model:** the overlapping dilation atlas (`dilationAtlas`/`dilationAtlasTwo`, total), the
  genuinely partial half-space atlas `halfSpaceAtlas` (two half-space sources, null boundaries,
  proper dilation transitions, not total), the Gaussian family (I4), the Euclidean chart
  calculus.
* **Statement-only / named limitations:** an atlas instantiated from mathlib's manifold API with
  a genuine Riemannian metric (packaging); closed-manifold integration; Stokes with boundary;
  orientation-dependent volume form; the fat-boundary case. See §6.
* **Upstream source claim (not local evidence):** the Frenzymath snapshot at `bb91a091` (upstream
  pin Lean `v4.32.1` / mathlib `520045ab`), source-level reference only, not buildable at this
  pin.

## 5. Exact blockers closed (with the constructed downstream checked use)

| blocker | closed content | downstream checked use |
| --- | --- | --- |
| **U7-GLOBAL-INTEGRABILITY** | `integrable_chartMeasure_iff`, `integrable_globalMeasure_iff`, `integrable_globalMeasure_withDensity_of_supported` | `hintL`/`hintR` of `halfSpaceAtlas_weightedIBP_unconditional` and of `globalWeightedIBP_of_cover_partial_ae`; `halfSpaceAtlas_integrable_dirichlet` |
| **U7-GLOBAL-POU / POU construction** | `exists_smooth_partitionOfUnity_subordinate` applied to the finite cover `overlapOf … ∩ ball 0 (R+1)` inside **`globalWeightedIBP_of_cover_partial_ae`** | the theorem has no POU hypothesis; `halfSpaceAtlas_weightedIBP_of_cover` and `halfSpaceAtlas_weightedIBP_of_cover_chartOne` apply it to the model |
| **U7-GLOBAL-BOUNDARY / partial-atlas model** | `hsStep`, `hsPsi`, `hsPsi_sum`, `hasCompactSupport_hsPsi`, **`halfSpaceAtlas_weightedIBP_unconditional`** | `halfSpaceAtlas_dirichletEnergy`, `halfSpaceAtlas_greenIdentity`, `halfSpaceAtlas_integrable_dirichlet` |
| **U7-DIVERGENCE / partial-atlas model** | `support_laplacian_subset`, **`halfSpaceAtlas_laplacianIntegralZero`** | D12's `laplacian_integral_eq_zero` transported to the glued measure of the partial atlas (the total dilation model had `dilationAtlasTwo_laplacianIntegralZero`) |
| **U7-GLOBAL-LIFT (partial charts)** | invocation 6: `lift_apply_chart_of_support`, `pouPiece_chart_of_support`, `sum_pouPairing_of_support`, `globalWeightedIBP_of_pou_partial`, `support_pouPairing_subset_chart`, `globalWeightedIBP_of_pou_partial_ae` | the two new theorems apply it with all hypotheses discharged |
| **U7-GLOBAL-POU (invocation 6)** | `exists_contDiff_bump`, `exists_smooth_partitionOfUnity_subordinate`, `gradInnerInverse_congruence`, `OverlapAtlas.gradInnerInverse_chartTransition`, `globalWeightedIBP_finset`, `globalWeightedIBP_of_pouData`, `SmoothOverlapAtlas.globalWeightedIBP_of_pou` | `dilationAtlasTwo_weightedIBP_via_pou`; the new cover theorem |
| **U7-GLOBAL-MEASURE / VOLUME-FORM (invocations 3–5)** | `globalMeasure`, `chartMeasure_apply_eq`, `globalMeasure_apply_chart`, `globalMeasure_restrict_eq_chartMeasure`, `globalMeasure_apply_chart_volumeForm`, `dilationAtlasTwoData` | `dilationAtlasTwoData_weightedIBP` through `manifoldWeightedIBP_of_atlasData` (the D4/D7-facing interface consumption) |
| **U7 chart-level (D12/D13)** | chart volume form, `chart_weighted_ibp`, chart divergence theorem, `BochnerFlat.bochnerIdentityOn_euclidean` | the manifold assembly above; the I4 bridge below |
| **I4 (all five components)** | `f_derivative`, `weighted_ibp`, `bochner`, `conjugate_measure_evolution`, `regularity` for the Gaussian family (`HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian`) | `monotoneOn_F_gaussian`, `F_gauss_mono`, `F_gauss_initial_le`, `monotoneCertificate_gaussian`; `W_gaussEntropyData`, `W_gauss_antitone` |
| **I4-residual defects (proved)** | unrestricted `WeightedIBPStatement` false; the `∀t>0` conjugate-heat/regularity forms unsatisfiable for nontrivial finite-lifetime data | the honest restricted statements are the ones used everywhere |

## 6. Remaining blockers and named limitations (genuine, out of the I4/U7 discharge)

1. **B-D13-RIEMANNIAN-METRIC-BRIDGE-PACKAGING.** An atlas instantiated from mathlib's manifold
   API (`IsManifold` + `RiemannianMetric`) with one consistent global `ChartMetric` per chart:
   the tensor law itself is proved (`metric_transform_chartTransition`,
   `metric_transform_chartOverlap`), and the model atlases are globally consistent, but the
   bump-extension of the genuine chart Gram matrix is only genuine where the bump is `1`, so a
   literal instantiation from arbitrary genuine charts is not built. This needs a locally finite
   atlas of small charts, not available at the pin without substantial manifold infrastructure.
2. **D12 `ChartMetric.smooth` asks for analytic coefficients** (`ContDiff ℝ ⊤ = ω` at this pin);
   the honest `C^∞` variant is `SmoothChartMetric`. D12's theorems only use `C²`.
3. **U7-GLOBAL-BOUNDARY (fat boundaries).** For chart sources whose frontier has positive
   measure the lifted pairing may be nonzero on the frontier; the null-boundary theorem
   (`hbd : volume (frontier (source i)) = 0`, satisfied by all open chart domains used here)
   is the honest hypothesis. A source with fat frontier can be replaced by a smaller open source.
4. **B-D13-CLOSED-MANIFOLD** — no closed-manifold integration API; compact support cannot be
   discharged by closedness.
5. **B-D13-STOKES / B-D12-BOUNDARY-STOKES** — manifold boundary measure / outward normal /
   Stokes absent (the chart-level divergence theorem is the boundary case used).
6. **B-D13-ORIENTED-ATLAS** — global orientation-dependent volume form not constructed (the
   unoriented density route is used).
7. **Manifold-level F-functional.** The I4 consumption is for the explicit Gaussian model on the
   Euclidean chart; there is no manifold `WeightedCalculus` instance (the D3 calculus is a
   normed-space structure), so the U7 layer is consumed through `ManifoldAtlasData` /
   `globalWeightedIBP_of_cover_partial_ae` rather than through `FiniteLifetimeEntropyBridge`.

## 7. Source hashes (sha256)

| file | sha256 | lines |
| --- | --- | --- |
| `release/Poincare/D13/ManifoldIBP/IntegrableTransfer.lean` | `bbb85aba5fb7783222970a79b4c1f1ac6f66caea3bbcfd2b2a4ef7005caff868` | 126 |
| `release/Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean` | `d8815e5da15ee66981793daf3b404a0ed44a13faa203420a7962746b5715bf89` | 678 |
| `release/Poincare/D13/ManifoldIBP/POUConstruction.lean` | `ab136b68a704557c412072d5985fbf7cf7ce32685c37fa16479f309cb3af5d9e` | 482 |
| `release/Poincare/D13/ManifoldIBP.lean` (umbrella) | `afc37991ad08a4347abf1017d3dd56fbaf60455b920c29dffce3757e6ec5d73f` | 25 |
| `release/Poincare/D13/Audit.lean` | `57f6fa6276bfc6bb8c8121ec8fe1b35814562da776d2be45fa46b171fa5329ee` | 456 |

Invocation-6 files (unchanged, hashes in the invocation-6 card section): `SmoothPartition`,
`GlobalIBP`, `PullbackPairing`, `AtlasPairing`, `POUAssembly`, `POUModel`, `SmoothAtlas`,
`SmoothAtlasIBP`, `SmoothAtlasModel`, `SmoothAtlasPartial`, `POUAssemblyAE`,
`SmoothAtlasPartialAE`, `PartialChartModel`; invocations 1–5: the D12 chart layer, the
`VolumeForm/*`, `ManifoldIBP/{ChartSum,Transfer,Blocked,DisjointModel,GlobalMeasure,OverlapModel,
OverlapIBP,OverlapIBPModel,OverlapIBPData,OverlapOperatorCheck,VolumeFormBridge}` and
`Riemannian/*` modules.

Toolchain `leanprover/lean4:v4.34.0-rc2` (commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`),
mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` — unchanged, pinned by
`release/lake-manifest.json`.

## 8. Compile evidence (commands, cwd, exits)

| # | command | cwd | exit |
| --- | --- | --- | --- |
| 1 | `lake env lean Poincare/D13/ManifoldIBP/IntegrableTransfer.lean` | `release/` | 0 — 3/3 decls, standard cones |
| 2 | `lake env lean Poincare/D13/ManifoldIBP/PartialChartModelPOU.lean` | `release/` | 0 — 29 decls, standard cones (iterated: the file was compiled after each repair) |
| 3 | `lake env lean Poincare/D13/ManifoldIBP/POUConstruction.lean` | `release/` | 0 — 3/3 decls, standard cones |
| 4 | `lake build` (full package incl. audit) | `release/` | 0 — `Build completed successfully (9003 jobs)`; `D6AUDIT VERDICT PASS` |
| 5 | `lake env lean Poincare/D13/Audit.lean` | `release/` | 0 — **346** printed cones (347 `#print axioms`); `grep -c sorryAx` = 0; only `negativeControl` deviates |
| 6 | comment-aware forbidden scan over 47 D13 `.lean` files | worktree | exactly 1 hard token: the intentional `axiom negativeControl` |

## 9. Axiom evidence

Every declaration printed by `Poincare.D13.Audit` (347 `#print axioms`, 346 printed cones)
depends only on `propext`, `Classical.choice`, `Quot.sound`. The negative control
`negativeControl` (an `axiom`, never used by any theorem) is flagged with its own axiom, proving
the audit is not vacuous. No `sorry`, `admit`, `unsafe`, `native_decide` or `proof_wanted`
appears in any D13 file (comment-aware scan over the 47-file tree: one hit, the negative
control). The 35 new declarations of the three new modules are clean, including the three
headline theorems `globalWeightedIBP_of_cover_partial_ae`,
`halfSpaceAtlas_weightedIBP_unconditional`, `halfSpaceAtlas_greenIdentity`.

## 10. Next dependency requests

1. **Locally finite genuine atlas** (`B-D13-RIEMANNIAN-METRIC-BRIDGE-PACKAGING`): a finite/
   locally finite cover of a mathlib manifold by small charts whose bump-extended Gram metrics
   are genuine on the cover, then a literal `OverlapAtlas`/`SmoothOverlapAtlas` instantiation;
   `globalWeightedIBP_of_cover_partial_ae` then applies with `hcover` the chart cover.
2. **D12 interface regularity**: weaken `ChartMetric.smooth` from `ContDiff ℝ ⊤` (= analytic) to
   `ContDiff ℝ ∞`; `exists_contDiff_bump` is the ready-made smooth replacement.
3. **A `WeightedCalculus` instance on a manifold** (or a manifold analogue of the D3/D4
   structure) so that `FiniteLifetimeEntropyBridge.monotoneOn_of_bridge` can consume the U7
   manifold IBP directly instead of through `ManifoldAtlasData`.
4. **D4/D7 consumers**: cite `CertificateOn.FiniteLifetimeEntropyBridge` +
   `monotoneOn_of_bridge`, `HeatKernelBridge.monotoneOn_F_gaussian`; the U7 entry points are
   `SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae`,
   `OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional`,
   `OverlapAtlas.globalWeightedIBP_of_pouData` and
   `Riemannian.OverlapAtlas.gradInnerInverse_chartTransition`.
5. **D7-side repair**: restrict `WeightedIBPStatement` / `BochnerStatement` /
   `FDerivativeStatement` / `EntropyFunctionalRegularityStatement` by support/regularity/
   finite-lifetime hypotheses (their unrestricted forms are proved false).

## 11. Elapsed time

* Invocation 7: ≈ 0 h 30 min wall clock (2026-09-11 11:06Z → 11:33Z, within the four-hour cap);
  this checkpoint is compile-checked and self-consistent.
* Invocation 6: ≈ 2 h 0 min; invocation 5: ≈ 1 h 20 min; invocation 4: ≈ 0 h 45 min;
  invocation 3: ≈ 0 h 50 min; invocation 2: ≈ 3 h 20 min; invocation 1: ≈ 4 h.

**Not claimed:** no unconditional global IBP for arbitrary `C²` data on an arbitrary charted
manifold — the general theorem `globalWeightedIBP_of_cover_partial_ae` assumes the finite chart
cover, the support/compactness of the test data in the base chart, proper null-boundary atlas
transitions and the operator identifications; no literal instantiation of the atlas layer from
mathlib's manifold API; no Stokes theorem with boundary, no closed-manifold integration and no
global oriented volume form; no manifold-level entropy functional and no Perelman or Poincaré
theorem. The `I4` discharge is for the explicit Gaussian model; the `U7` discharge covers the
chart layer, the overlapping-atlas measure, the chart-supported IBP, the constructed partitions
of unity, the constructed integrability, the lifted-piece assembly for total and partial
atlases, and the fully unconditional partial-atlas model instances with their Green/Dirichlet
consequences, with the constructed downstream checked uses listed in §5.

TASK_DONE
