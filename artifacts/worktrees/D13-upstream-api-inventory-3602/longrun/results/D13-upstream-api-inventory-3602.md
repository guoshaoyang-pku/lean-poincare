# D13-upstream-api-inventory-3602 — result card

Generated: 2026-09-12T00:01:33+08:00 (worktree `worktrees/D13-upstream-api-inventory-3602`).

**Task**: inventory the Frenzymath upstream packages/APIs relevant to manifold
geometry, heat/PDE and topology under Lean 4.32.1; do not flatten pins or import
admitted proofs; build only selected adapter probes; record exact source revisions
and licenses, compile exits, and classify declarations as compiled, conditional,
model, statement-only or upstream source claim.

**This card proves no mathematical theorem and makes no Poincare claim.** Every
declaration discussed below is an *upstream* declaration; the only original Lean
content in this worktree is the adapter-probe package `probes/`, which imports and
re-checks selected upstream declarations.

## 1. Source, revision, license

- repository: <https://github.com/frenzymath/Poincare-Conjecture>
- commit: `bb91a091f0b968f8bbe8d861e025a88d82b161be`
- tree: `5146f0db9ea8c171ee6252d64933fdc1448be124`
- license: **Apache-2.0** (single root `LICENSE`; no per-package license files)
- snapshot: `2801` files, of which 2352 Lean files / 657192 Lean lines
- provenance check: **exact_match** — remote blobs 2801, missing 0, extra 0, modified 0 (SHA-1 git blob hashes compared against the GitHub trees API for the recorded tree)
- snapshot digest (sha256 over sorted `path blob-sha1`): `894748a91da268f0dbb02195c09e550d733a27ab2f24a919a8d2ed01cffb9c7e`

**Pins are preserved, not flattened.** Every one of the 18 Lake packages in the
snapshot keeps its own `lean-toolchain` and `lake-manifest.json`; all 18 pin
`leanprover/lean4:v4.32.1` and mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. Nothing in this worktree
rewrites an upstream pin; the probe package is a separate Lake package that
*requires* the upstream packages by relative path.

## 2. Package inventory

| package | role | files | Lean lines | decls | admitted decls | toolchain | mathlib |
|---|---|---:|---:|---:|---:|---|---|
| `Petersen` | Petersen, Riemannian geometry | 419 | 144140 | 4494 | 0 | v4.32.1 | `520045ab` |
| `MorganTian` | Morgan-Tian, Ricci flow and the Poincare conjecture | 573 | 140731 | 4496 | 0 | v4.32.1 | `520045ab` |
| `LeeSmooth` | Lee, Smooth manifolds | 552 | 135191 | 5845 | 271 | v4.32.1 | `520045ab` |
| `DoCarmo` | do Carmo, Riemannian geometry (formalized) | 293 | 103342 | 2804 | 0 | v4.32.1 | `520045ab` |
| `Topping` | Topping, Lectures on the Ricci flow | 184 | 44610 | 1717 | 0 | v4.32.1 | `520045ab` |
| `LeeRiemannian` | Lee, Riemannian manifolds | 116 | 33374 | 1447 | 0 | v4.32.1 | `520045ab` |
| `Evans` | Evans, Partial Differential Equations (formalized) | 65 | 22091 | 948 | 0 | v4.32.1 | `520045ab` |
| `Hatcher` | Hatcher, Algebraic Topology | 58 | 18778 | 1180 | 0 | v4.32.1 | `520045ab` |
| `HanLinLectureNotes` | Han-Lin, elliptic PDE lecture notes | 37 | 10059 | 314 | 0 | v4.32.1 | `520045ab` |
| `KleinerLott` | Kleiner-Lott, notes on Perelman's papers | 11 | 1962 | 96 | 0 | v4.32.1 | `520045ab` |
| `GilbargTrudinger` | Gilbarg-Trudinger, elliptic PDE (Ch5) | 9 | 1509 | 63 | 0 | v4.32.1 | `520045ab` |
| `shared` | book-independent infrastructure (mathlib gaps + linters) | 12 | 877 | 51 | 0 | v4.32.1 | `520045ab` |
| `ChowKnopf` | Chow-Knopf, Ricci flow techniques | 8 | 357 | 23 | 0 | v4.32.1 | `520045ab` |
| `CaoZhu` | Cao-Zhu, Hamilton-Perelman proof (blueprint stub) | 3 | 37 | 0 | 0 | v4.32.1 | `520045ab` |
| `PoincareConjecture` | primary custom proof architecture (blueprint only) | 3 | 37 | 0 | 0 | v4.32.1 | `520045ab` |
| `CheegerGromovTaylor` | Cheeger-Gromov-Taylor (blueprint stub) | 3 | 36 | 0 | 0 | v4.32.1 | `520045ab` |
| `ChowEtAl` | Chow et al., Ricci flow (blueprint stub) | 3 | 36 | 0 | 0 | v4.32.1 | `520045ab` |
| `Thurston` | Thurston, three-manifolds (blueprint stub) | 3 | 25 | 0 | 0 | v4.32.1 | `520045ab` |

Totals: 2352 Lean files, 657192 lines, 23478 top-level declarations.

## 3. Admitted-proof map (upstream)

Comment/string-aware scan for the D5 hard tokens (`sorry`, `axiom`, `unsafe`, `native_decide`, `proof_wanted`, `sorryAx`, `admit`):

| package | admitted declarations | modules involved | tokens |
|---|---:|---:|---|
| `LeeSmooth` | 271 | 89 | `{'sorry': 274}` |

Notes:

- `LeeSmooth` is the only library package with admitted proofs: 271 declarations across 89 modules carry an admitted step in their own body. They are classified `statement-only` below and are excluded from every probe import closure.
- `DoCarmo`'s two token hits are outside the library, in review tooling (`apps/review/server/lean/ExtractCommands.lean`, `tools/ExtractLeanGraph.lean`); the `DoCarmoLib` library itself is token-free.
- All other packages (Evans, Hatcher, MorganTian, Petersen, Topping, KleinerLott, ChowKnopf, GilbargTrudinger, HanLinLectureNotes, LeeRiemannian, shared) contain no hard token in library code.

## 4. Blueprint status (statement-level upstream source claims)

8248 blueprint environments, of which 669 are marked `\notready` (stated in the blueprint, not yet formalised). These are the *upstream source claim* class: they assert mathematics but offer no Lean declaration to import.

| package | environments | notready | with proof block |
|---|---:|---:|---:|
| `PoincareConjecture` | 279 | 278 | 0 |
| `Thurston` | 266 | 266 | 0 |
| `MorganTian` | 889 | 45 | 0 |
| `DoCarmo` | 601 | 37 | 0 |
| `Petersen` | 1070 | 30 | 0 |
| `LeeRiemannian` | 1128 | 8 | 53 |
| `Topping` | 138 | 5 | 0 |
| `CaoZhu` | 174 | 0 | 0 |
| `CheegerGromovTaylor` | 28 | 0 | 0 |
| `ChowEtAl` | 1268 | 0 | 0 |
| `ChowKnopf` | 334 | 0 | 0 |
| `Evans` | 757 | 0 | 0 |
| `GilbargTrudinger` | 401 | 0 | 0 |
| `HanLinLectureNotes` | 147 | 0 | 0 |
| `Hatcher` | 216 | 0 | 0 |
| `KleinerLott` | 242 | 0 | 0 |
| `LeeSmooth` | 310 | 0 | 0 |

## 5. Focus APIs (geometry / heat-PDE / topology)

Entry points are quoted from the upstream sources; `class` follows the D13
classification and is `model` for definitions/structures, `claim` for
theorems/lemmas (see section 8 for the evidence level of each).

### 5.1 geometry

**length-space infrastructure** — `shared` — modules: `LengthSpace`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `pathLength` | def | noncomputable def pathLength {M : Type*} [PseudoEMetricSpace M] {x y : M} (γ : Path x y) : ℝ≥0∞ | no |
| `LengthSpace` | class | class LengthSpace (M : Type*) [PseudoEMetricSpace M] : Prop | no |
| `edist_le_pathLength` | theorem | theorem edist_le_pathLength {x y : M} (γ : Path x y) : | no |
<sub>1 modules, 3 declarations, 0 admitted.</sub>

**bilinear forms on real vector spaces** — `shared` — modules: `Basic`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `Form` | abbrev | abbrev Form (𝕜 : Type*) [CommSemiring 𝕜] (V : Type*) [AddCommMonoid V] [Module 𝕜 V] | no |
| `IsSymm` | abbrev | abbrev IsSymm (B : Form 𝕜 V) : Prop | no |
| `inner` | def | def inner (B : Form 𝕜 V) (v w : V) : 𝕜 | no |
| `inner_def` | theorem | theorem inner_def (B : Form 𝕜 V) (v w : V) : | no |
| `inner_comm` | theorem | theorem inner_comm {B : Form 𝕜 V} (hB : IsSymm B) (v w : V) : | no |
| `inner_add_left` | theorem | theorem inner_add_left (B : Form 𝕜 V) (v₁ v₂ w : V) : | no |
| `inner_add_right` | theorem | theorem inner_add_right (B : Form 𝕜 V) (v w₁ w₂ : V) : | no |
| `inner_smul_left` | theorem | theorem inner_smul_left (B : Form 𝕜 V) (c : 𝕜) (v w : V) : | no |
<sub>1 modules, 18 declarations, 0 admitted.</sub>

**T2 total space of a fibre bundle** — `shared` — modules: `FiberBundleT2`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `FiberBundle.t2Space_totalSpace` | theorem | theorem FiberBundle.t2Space_totalSpace {B F : Type*} [TopologicalSpace B] [TopologicalSpace F] {E : B → Type*} [TopologicalSpace (Bundle.TotalSpace F E)] [∀ b, ... | no |
| `TangentBundle.t2Space` | instance | instance TangentBundle.t2Space {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) (M : Type*) [T... | no |
<sub>1 modules, 2 declarations, 0 admitted.</sub>

**do Carmo Ch2: affine connections** — `DoCarmo` — modules: `DoCarmoCh2`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `SmoothVectorField.dir` | def | def SmoothVectorField.dir (X : SmoothVectorField I M) (f : M → ℝ) (p : M) : ℝ | no |
| `dirTangent` | def | def dirTangent (f : M → ℝ) {p : M} (v : TangentSpace I p) : ℝ | no |
| `dirTangent_add` | theorem | theorem dirTangent_add (f : M → ℝ) {p : M} (v w : TangentSpace I p) : | no |
| `dirTangent_smul` | theorem | theorem dirTangent_smul (f : M → ℝ) {p : M} (c : ℝ) (v : TangentSpace I p) : | no |
| `exists_smoothVectorField_eq` | theorem | theorem exists_smoothVectorField_eq [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] (p : M) (v : TangentSpace I p) : ∃ Z : SmoothVectorField I M, Z p ... | no |
| `IsAffineConnectionMap` | def | def IsAffineConnectionMap (cov : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M) : Prop | no |
| `AffineConnection` | structure | structure AffineConnection (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] | no |
| `ofIsAffineConnectionMap` | def | def ofIsAffineConnectionMap (cov : SmoothVectorField I M → SmoothVectorField I M → SmoothVectorField I M) (hcov : IsAffineConnectionMap cov) : AffineConnection ... | no |
<sub>1 modules, 60 declarations, 0 admitted.</sub>

**curvature tensor (pointwise)** — `DoCarmo` — modules: `CurvaturePointwise`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `curvature_zero_left` | theorem | theorem curvature_zero_left (Y Z : SmoothVectorField I M) (p : M) : (nabla.curvature 0 Y Z) p = 0 | no |
| `curvature_zero_right` | theorem | theorem curvature_zero_right (X Y : SmoothVectorField I M) (p : M) : (nabla.curvature X Y 0) p = 0 | no |
| `curvature_apply_eq_zero_of_eventuallyEq_zero_left` | theorem | theorem curvature_apply_eq_zero_of_eventuallyEq_zero_left {τ : SmoothVectorField I M} (Y Z : SmoothVectorField I M) {p : M} (hτ : ∀ᶠ q in nhds p, τ q = 0) : | no |
| `curvature_apply_eq_zero_of_eventuallyEq_zero_right` | theorem | theorem curvature_apply_eq_zero_of_eventuallyEq_zero_right {τ : SmoothVectorField I M} (X Y : SmoothVectorField I M) {p : M} (hτ : ∀ᶠ q in nhds p, τ q = 0) : | no |
| `curvature_apply_eq_zero_of_forall_eq_sum_left` | theorem | theorem curvature_apply_eq_zero_of_forall_eq_sum_left {ι : Type*} (s : Finset ι) {f : ι → M → ℝ} (hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i)) (W : ι → SmoothVectorFi... | no |
| `curvature_apply_eq_zero_of_forall_eq_sum_right` | theorem | theorem curvature_apply_eq_zero_of_forall_eq_sum_right {ι : Type*} (s : Finset ι) {f : ι → M → ℝ} (hf : ∀ i, ContMDiff I 𝓘(ℝ, ℝ) ∞ (f i)) (W : ι → SmoothVectorF... | no |
| `curvature_apply_eq_zero_of_apply_eq_zero_left` | theorem | theorem curvature_apply_eq_zero_of_apply_eq_zero_left (Y Z : SmoothVectorField I M) {σ : SmoothVectorField I M} {p : M} (hσ : σ p = 0) : | no |
| `curvature_apply_eq_zero_of_apply_eq_zero_middle` | theorem | theorem curvature_apply_eq_zero_of_apply_eq_zero_middle (X Z : SmoothVectorField I M) {σ : SmoothVectorField I M} {p : M} (hσ : σ p = 0) : | no |
<sub>1 modules, 19 declarations, 0 admitted.</sub>

**geodesic equation** — `DoCarmo` — modules: `Equation`, `EquationTransfer`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `chartCoord` | def | def chartCoord (i : Fin (Module.finrank ℝ E)) (v : E) : ℝ | no |
| `chartCoord_smul` | lemma | lemma chartCoord_smul (i : Fin (Module.finrank ℝ E)) (a : ℝ) (v : E) : | no |
| `chartCoord_zero` | lemma | lemma chartCoord_zero (i : Fin (Module.finrank ℝ E)) : | no |
| `chartCoord_add` | lemma | lemma chartCoord_add (i : Fin (Module.finrank ℝ E)) (v w : E) : | no |
| `chartChristoffelContraction` | def | def chartChristoffelContraction (g : RiemannianMetric I M) (α : M) (v w : E) (y : E) : E | no |
| `chartChristoffelContraction_symm` | lemma | lemma chartChristoffelContraction_symm (g : RiemannianMetric I M) (α : M) (v w : E) (y : E) : | no |
| `chartChristoffelContraction_zero_left` | lemma | lemma chartChristoffelContraction_zero_left (g : RiemannianMetric I M) (α : M) (w : E) (y : E) : | no |
| `chartChristoffelContraction_smul_smul` | lemma | lemma chartChristoffelContraction_smul_smul (g : RiemannianMetric I M) (α : M) (a : ℝ) (v : E) (y : E) : | no |
<sub>2 modules, 73 declarations, 0 admitted.</sub>

**Gauss lemma** — `DoCarmo` — modules: `GaussLemma`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `chartMetricInner_zero_left` | theorem | theorem chartMetricInner_zero_left (g : RiemannianMetric I M) (α : M) (y b : E) : | no |
| `chartMetricInner_zero_right` | theorem | theorem chartMetricInner_zero_right (g : RiemannianMetric I M) (α : M) (y a : E) : | no |
| `chartMetricInner_smul_left` | theorem | theorem chartMetricInner_smul_left (g : RiemannianMetric I M) (α : M) (y : E) (s : ℝ) (a b : E) : | no |
| `chartMetricInner_smul_right` | theorem | theorem chartMetricInner_smul_right (g : RiemannianMetric I M) (α : M) (y : E) (s : ℝ) (a b : E) : | no |
| `chartMetricInner_symm` | theorem | theorem chartMetricInner_symm (g : RiemannianMetric I M) (α : M) (y a b : E) : | no |
| `hasDerivAt_chartMetricInner_quadratic` | theorem | theorem hasDerivAt_chartMetricInner_quadratic (g : RiemannianMetric I M) (α : M) (y a d : E) : | no |
| `gauss_surface_computation` | theorem | theorem gauss_surface_computation (g : RiemannianMetric I M) (p : M) (f : E → E) {ρ b : ℝ} (hb : 1 < b) (hC2 : ContDiffOn ℝ 2 f (ball (0 : E) ρ)) (hf0 : f 0 = e... | no |
| `exists_gauss_lemma_ball` | theorem | theorem exists_gauss_lemma_ball (g : RiemannianMetric I M) (p : M) : ∃ ρ : ℝ, 0 < ρ ∧ (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧ (∀ ... | no |
<sub>1 modules, 9 declarations, 0 admitted.</sub>

**Bonnet-Myers theorem** — `DoCarmo` — modules: `BonnetMyers`, `BonnetMyersFundamentalGroup`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `isLocalMin_deriv_deriv_nonneg` | theorem | theorem isLocalMin_deriv_deriv_nonneg {f : ℝ → ℝ} {x f'' : ℝ} (hmin : IsLocalMin f x) (hcont : ContinuousAt f x) (hf'' : HasDerivAt (deriv f) f'' x) : 0 ≤ f'' | no |
| `metricInner_smul_smul` | theorem | theorem metricInner_smul_smul (g : RiemannianMetric I M) (p : M) (c : ℝ) (v w : E) : | no |
| `curvatureFormAt_smul_snd_fth` | theorem | theorem curvatureFormAt_smul_snd_fth (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M) (c : ℝ) (v w z q : E) : | no |
| `curvatureFormAt_smul_fst_trd` | theorem | theorem curvatureFormAt_smul_fst_trd (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M) (c : ℝ) (v w z q : E) : | no |
| `continuousOn_velocity_curvature_of_parallel` | theorem | theorem continuousOn_velocity_curvature_of_parallel (g : RiemannianMetric I M) {W : ℝ → E} {γ : ℝ → M} {a b : ℝ} (hW : IsParallelFieldAlongOn (I := I) g γ W a b... | no |
| `continuousOn_velocitySeeded_curvature` | theorem | theorem continuousOn_velocitySeeded_curvature (g : RiemannianMetric I M) {γ : ℝ → M} {e₀ e : ℝ → E} {a b ℓ : ℝ} (hℓ : ℓ ≠ 0) (he : IsParallelFieldAlongOn (I := ... | no |
| `indexForm_smul_eq` | theorem | theorem indexForm_smul_eq (g : RiemannianMetric I M) (γ : ℝ → M) (e : ℝ → E) (φ : ℝ → ℝ) (a b : ℝ) : | no |
| `indexForm_smul_frame_eq` | theorem | theorem indexForm_smul_frame_eq (g : RiemannianMetric I M) (γ : ℝ → M) (e en : ℝ → E) (φ : ℝ → ℝ) (ℓ : ℝ) {a b : ℝ} (hab : a ≤ b) (hunit : ∀ t ∈ Set.Icc a b, g.... | no |
<sub>2 modules, 39 declarations, 0 admitted.</sub>

**Gauss lemma** — `Petersen` — modules: `GaussLemma`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `chartMetricInner_zero_left` | theorem | theorem chartMetricInner_zero_left (g : RiemannianMetric I M) (α : M) (y b : E) : | no |
| `chartMetricInner_zero_right` | theorem | theorem chartMetricInner_zero_right (g : RiemannianMetric I M) (α : M) (y a : E) : | no |
| `chartMetricInner_smul_left` | theorem | theorem chartMetricInner_smul_left (g : RiemannianMetric I M) (α : M) (y : E) (s : ℝ) (a b : E) : | no |
| `chartMetricInner_smul_right` | theorem | theorem chartMetricInner_smul_right (g : RiemannianMetric I M) (α : M) (y : E) (s : ℝ) (a b : E) : | no |
| `chartMetricInner_symm` | theorem | theorem chartMetricInner_symm (g : RiemannianMetric I M) (α : M) (y a b : E) : | no |
| `hasDerivAt_chartMetricInner_quadratic` | theorem | theorem hasDerivAt_chartMetricInner_quadratic (g : RiemannianMetric I M) (α : M) (y a d : E) : | no |
| `gauss_surface_computation` | theorem | theorem gauss_surface_computation (g : RiemannianMetric I M) (p : M) (f : E → E) {ρ b : ℝ} (hb : 1 < b) (hC2 : ContDiffOn ℝ 2 f (ball (0 : E) ρ)) (hf0 : f 0 = e... | no |
| `exists_gauss_lemma_ball` | theorem | theorem exists_gauss_lemma_ball (g : RiemannianMetric I M) (p : M) : ∃ ρ : ℝ, 0 < ρ ∧ (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧ (∀ ... | no |
<sub>1 modules, 9 declarations, 0 admitted.</sub>

**geometric comparison theorems** — `MorganTian` — modules: `ComparisonGeometric`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `sectional_curvature_comparison_of_not_conjugate` | theorem | theorem sectional_curvature_comparison_of_not_conjugate {g : RiemannianMetric I M} {γ : ℝ → M} {a b B r₀ k : ℝ} (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ ... | no |
| `ricci_curvature_comparison_of_not_conjugate` | theorem | theorem ricci_curvature_comparison_of_not_conjugate {g : RiemannianMetric I M} {γ : ℝ → M} {a b B r₀ k : ℝ} (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc... | no |
<sub>1 modules, 2 declarations, 0 admitted.</sub>

**curvature evolution under Ricci flow** — `Topping` — modules: `CurvatureVariationFromFlow`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `riemannCurvatureAt_chartBasis_expansion` | theorem | theorem riemannCurvatureAt_chartBasis_expansion (g : RiemannianMetric I M) (alpha p : M) (i j k l : Fin (Module.finrank ℝ E)) (hp : p ∈ (chartAt H alpha).source... | no |
| `mtRicciTensorAt_eq_ricciTensorAt` | theorem | theorem mtRicciTensorAt_eq_ricciTensorAt (g : RiemannianMetric I M) (p : M) (x y : TangentSpace I p) : | no |
| `sum_chartCurvatureCoef_mul_neg_two_mtRicci_eq` | theorem | theorem sum_chartCurvatureCoef_mul_neg_two_mtRicci_eq (g : RiemannianMetric I M) (alpha p : M) (i j k l : Fin (Module.finrank ℝ E)) (hp : p ∈ (chartAt H alpha).... | no |
| `hasDerivAt_riemannCurvatureAt_chartBasis` | theorem | theorem hasDerivAt_riemannCurvatureAt_chartBasis {g : ℝ → RiemannianMetric I M} {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ} {J : Set ℝ} (hg : Mor... | no |
| `chartTangentCoeff` | def | noncomputable def chartTangentCoeff (alpha p : M) (i : Fin (Module.finrank ℝ E)) (v : TangentSpace I p) : ℝ | no |
| `riemannCurvatureAt_eq_chartBasis_sum` | theorem | theorem riemannCurvatureAt_eq_chartBasis_sum (g : RiemannianMetric I M) (alpha p : M) (x y z w : TangentSpace I p) (hp : p ∈ (chartAt H alpha).source) : | no |
| `pointwiseValue_eq_chartBasis_sum_four` | theorem | theorem pointwiseValue_eq_chartBasis_sum_four {A : CovTensorField I M 4} {p : M} (hA : IsPointwiseMultilinear A p) (alpha : M) (x y z w : TangentSpace I p) (hp ... | no |
| `chartRiemannBasisVariation` | def | noncomputable def chartRiemannBasisVariation (g : ℝ → RiemannianMetric I M) (h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ) (t : ℝ) (alpha p : M) (i ... | no |
<sub>1 modules, 25 declarations, 0 admitted.</sub>

**DeTurck trick / Picard iteration** — `Topping` — modules: `DeTurckPicard`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `isMetricVariationOn_of_intervalIntegral` | theorem | theorem isMetricVariationOn_of_intervalIntegral {g₀ : RiemannianMetric I M} {g : ℝ → RiemannianMetric I M} {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p... | no |
| `initial_metricInner_of_intervalIntegral` | theorem | theorem initial_metricInner_of_intervalIntegral {g₀ : RiemannianMetric I M} {g : ℝ → RiemannianMetric I M} {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p... | no |
| `RicciDeTurckPicardModel` | structure | structure RicciDeTurckPicardModel (g₀ : RiemannianMetric I M) (X : Type*) [MetricSpace X] | no |
| `fixedPoint` | def | noncomputable def fixedPoint : X | no |
| `fixedPoint_mem` | theorem | theorem fixedPoint_mem : P.fixedPoint ∈ P.contraction.carrier | no |
| `fixedPoint_isFixedPt` | theorem | theorem fixedPoint_isFixedPt : | no |
| `fixedPoint_unique_of_fixed` | theorem | theorem fixedPoint_unique_of_fixed {x : X} (hx : x ∈ P.contraction.carrier) (hfix : IsFixedPt P.contraction.map x) : | no |
| `fixedPoint_section_smooth` | theorem | theorem fixedPoint_section_smooth : | no |
<sub>1 modules, 30 declarations, 0 admitted.</sub>

**noncollapsing** — `KleinerLott` — modules: `Noncollapsing`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `ball` | def | def ball {M : Type*} (flow : RicciFlowData M) (t : ℝ) (x₀ : M) (r : ℝ) : | no |
| `HasCurvatureBoundOnParabolicBall` | def | def HasCurvatureBoundOnParabolicBall {M : Type*} (flow : RicciFlowData M) (x₀ : M) (t₀ r bound : ℝ) : Prop | no |
| `IsKappaNoncollapsedOnScale` | def | def IsKappaNoncollapsedOnScale {M : Type*} (flow : RicciFlowData M) (n : ℕ) (T kappa rho : ℝ) : Prop | no |
| `IsKappaCollapsedAt` | def | def IsKappaCollapsedAt {M : Type*} (flow : RicciFlowData M) (n : ℕ) (kappa r t₀ : ℝ) (x₀ : M) : Prop | no |
<sub>1 modules, 4 declarations, 0 admitted.</sub>

### 5.2 pde/heat

**heat equation: initial value problem** — `Evans` — modules: `HeatIVP`, `HeatIVPBounded`, `HeatIVPLimit`, `HeatIVPSmooth`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `hasDerivAt_integral_mul_hasCompactSupport` | lemma | lemma hasDerivAt_integral_mul_hasCompactSupport {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) {K K' : ℝ → Euclidean... | no |
| `heatSolution` | def | def heatSolution (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) : | no |
| `heatKernelSpatial_pos` | lemma | lemma heatKernelSpatial_pos {n : ℕ} {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) : | no |
| `continuous_heatKernelSpatial_sub` | lemma | lemma continuous_heatKernelSpatial_sub {n : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : | no |
| `heatSolution_integrable` | lemma | lemma heatSolution_integrable {n : ℕ} (t : ℝ) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin n)) ... | no |
| `heatSolution_pos` | theorem | theorem heatSolution_pos {n : ℕ} {t : ℝ} (ht : 0 < t) {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) (hg0 : 0 ≤ g) {x₀ : Euc... | no |
| `heatKernelSpatial_hasDerivAt_time` | lemma | lemma heatKernelSpatial_hasDerivAt_time {n : ℕ} {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) : | no |
| `heatKernelSpatial_sub_continuousOn` | lemma | lemma heatKernelSpatial_sub_continuousOn {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : | no |
<sub>4 modules, 55 declarations, 0 admitted.</sub>

**heat maximum principle** — `Evans` — modules: `HeatMaxPrinciple`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `deriv_deriv_nonpos_of_isLocalMax` | lemma | lemma deriv_deriv_nonpos_of_isLocalMax {g : ℝ → ℝ} {a : ℝ} (h : IsLocalMax g a) (hg : ContinuousAt g a) : | no |
| `deriv_nonneg_of_eventually_le_left` | lemma | lemma deriv_nonneg_of_eventually_le_left {g : ℝ → ℝ} {a c : ℝ} (hg : HasDerivAt g c a) (h : ∀ᶠ s in 𝓝[<] a, g s ≤ g a) : 0 ≤ c | no |
| `hasDerivAt_comp_single_line` | lemma | lemma hasDerivAt_comp_single_line {m : ℕ} {u : EuclideanSpace ℝ (Fin m) → ℝ} {i : Fin m} {p : EuclideanSpace ℝ (Fin m)} {s₀ : ℝ} (hu : DifferentiableAt ℝ u (p +... | no |
| `partialDeriv_nonneg_of_section_eventually_le_left` | lemma | lemma partialDeriv_nonneg_of_section_eventually_le_left {m : ℕ} {u : EuclideanSpace ℝ (Fin m) → ℝ} {p : EuclideanSpace ℝ (Fin m)} {i : Fin m} (hu : Differentiab... | no |
| `partialDeriv_iterate_two_nonpos_of_section_max` | lemma | lemma partialDeriv_iterate_two_nonpos_of_section_max {m : ℕ} {u : EuclideanSpace ℝ (Fin m) → ℝ} {p : EuclideanSpace ℝ (Fin m)} {i : Fin m} (hu : ContDiffAt ℝ 2 ... | no |
| `partialDeriv_fun_sub` | lemma | lemma partialDeriv_fun_sub {m : ℕ} {f g : EuclideanSpace ℝ (Fin m) → ℝ} {x : EuclideanSpace ℝ (Fin m)} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g ... | no |
| `partialDeriv_iterate_two_fun_sub` | lemma | lemma partialDeriv_iterate_two_fun_sub {m : ℕ} {f g : EuclideanSpace ℝ (Fin m) → ℝ} {x : EuclideanSpace ℝ (Fin m)} (i : Fin m) (hf : ∀ᶠ y in 𝓝 x, Differentiable... | no |
| `differentiableAt_partialDeriv_of_contDiffAt` | lemma | lemma differentiableAt_partialDeriv_of_contDiffAt {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ} {x : EuclideanSpace ℝ (Fin m)} (hf : ContDiffAt ℝ 2 f x) (i : Fin m... | no |
<sub>1 modules, 31 declarations, 0 admitted.</sub>

**Cauchy maximum principle** — `Evans` — modules: `HeatCauchyMaxPrinciple`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `spacePartL` | def | def spacePartL : SpaceTime n →L[ℝ] EuclideanSpace ℝ (Fin n) | no |
| `contDiff_spacePart` | lemma | lemma contDiff_spacePart {k : WithTop ℕ∞} : | no |
| `compKernelSpaceTime` | def | def compKernelSpaceTime (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) (τ : ℝ) : SpaceTime n → ℝ | no |
| `compKernelSpaceTime_eq_exp` | lemma | lemma compKernelSpaceTime_eq_exp {y : EuclideanSpace ℝ (Fin n)} {τ : ℝ} {p : SpaceTime n} (hp : p 0 < τ) : | no |
| `compKernelSpaceTime_contDiffAt` | lemma | lemma compKernelSpaceTime_contDiffAt {y : EuclideanSpace ℝ (Fin n)} {τ : ℝ} {p : SpaceTime n} (hp : p 0 < τ) {k : WithTop ℕ∞} : | no |
| `compKernelSpatial_hasDerivAt_time` | lemma | lemma compKernelSpatial_hasDerivAt_time {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) : | no |
| `compKernelSpatial_partialDeriv` | lemma | lemma compKernelSpatial_partialDeriv {s : ℝ} (hs : 0 < s) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) : | no |
| `partialDeriv_eq_of_hasDerivAt_line` | lemma | lemma partialDeriv_eq_of_hasDerivAt_line {m : ℕ} {g : EuclideanSpace ℝ (Fin m) → ℝ} {q : EuclideanSpace ℝ (Fin m)} {i : Fin m} {d : ℝ} (hg : DifferentiableAt ℝ ... | no |
<sub>1 modules, 15 declarations, 0 admitted.</sub>

**mean-value formula for the heat equation** — `Evans` — modules: `HeatMeanValue`, `HeatMeanValueNormalization`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `heatMeanValueWeight` | def | def heatMeanValueWeight (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) (p : SpaceTime n) : ℝ | no |
| `heatMeanValueIntegral` | def | def heatMeanValueIntegral (u : SpaceTime n → ℝ) (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) : ℝ | no |
| `heatParabolicDilation` | def | def heatParabolicDilation (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (p : SpaceTime n) : SpaceTime n | no |
| `heatParabolicDilationInv` | def | def heatParabolicDilationInv (x : EuclideanSpace ℝ (Fin n)) (t r : ℝ) (q : SpaceTime n) : SpaceTime n | no |
| `heatParabolicScale` | def | def heatParabolicScale (r : ℝ) : Fin (n + 1) → ℝ | no |
| `heatParabolicScale_prod` | lemma | lemma heatParabolicScale_prod (r : ℝ) : | no |
| `heatParabolicLinear` | def | def heatParabolicLinear (r : ℝ) : SpaceTime n →ₗ[ℝ] SpaceTime n | no |
| `heatParabolicLinear_det` | lemma | lemma heatParabolicLinear_det (r : ℝ) : | no |
<sub>2 modules, 72 declarations, 0 admitted.</sub>

**maximum principle (Riemannian)** — `Topping` — modules: `Riemannian`, `RiemannianMeasureSigmaFinite`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `metricLaplacianAt` | def | noncomputable def metricLaplacianAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : Mod... | no |
| `metricLaplacianAt_neg` | theorem | theorem metricLaplacianAt_neg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWith... | no |
| `metricLaplacianAt_add` | theorem | theorem metricLaplacianAt_add {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWith... | no |
| `metricLaplacianAt_const_mul` | theorem | theorem metricLaplacianAt_const_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : Mod... | no |
| `metricLaplacianAt_finsetSum` | theorem | theorem metricLaplacianAt_finsetSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : Mod... | no |
| `metricLaplacianAt_nonpos_of_isLocalMax` | theorem | theorem metricLaplacianAt_nonpos_of_isLocalMax {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace ... | no |
| `time_deriv_le_reaction_of_isLocalMax` | theorem | theorem time_deriv_le_reaction_of_isLocalMax {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ... | no |
| `contMDiff_spatial_slice_of_contMDiffOn_spacetime` | theorem | theorem contMDiff_spatial_slice_of_contMDiffOn_spacetime {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCor... | no |
<sub>2 modules, 21 declarations, 0 admitted.</sub>

**higher-derivative estimates** — `Topping` — modules: `HigherDerivativeEstimate`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `shiAux` | def | def shiAux (c : ℝ) (k : ℕ) : ℕ → ℝ \| 0 => 1 \| d + 1 => (1 + c + ((k - d : ℕ) : ℝ)) * shiAux c k d / 2 | no |
| `shiCoeff` | def | def shiCoeff (c : ℝ) (k j : ℕ) : ℝ | no |
| `shiCoeff_top` | theorem | theorem shiCoeff_top (c : ℝ) (k : ℕ) : shiCoeff c k k = 1 | no |
| `shiCoeff_of_le` | theorem | theorem shiCoeff_of_le (c : ℝ) {k j : ℕ} (h : k ≤ j) : shiCoeff c k j = 1 | no |
| `shiCoeff_succ` | theorem | theorem shiCoeff_succ (c : ℝ) {k j : ℕ} (h : j < k) : | no |
| `shiCoeff_pos` | theorem | theorem shiCoeff_pos {c : ℝ} (hc : 0 ≤ c) (k : ℕ) : ∀ j, 0 < shiCoeff c k j | no |
| `shiCoeff_telescope` | theorem | theorem shiCoeff_telescope {c : ℝ} (hc : 0 ≤ c) {k j : ℕ} (h : j < k) : ((j + 1 : ℕ) : ℝ) * shiCoeff c k (j + 1) + (1 + c) * shiCoeff c k (j + 1) | no |
| `shiCombination` | def | def shiCombination (c : ℝ) (k : ℕ) (w : ℕ → M → ℝ → ℝ) (x : M) (t : ℝ) : ℝ | no |
<sub>1 modules, 23 declarations, 0 admitted.</sub>

**Gilbarg-Trudinger Ch5 (elliptic PDE)** — `GilbargTrudinger` — modules: `BanachSpaces`, `CompactSpectrum`, `FredholmAlternative`, `HilbertFredholm`, `HilbertSpaces`, `MethodOfContinuity`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `IsContraction` | def | def IsContraction (T : E → E) : Prop | no |
| `contraction_mapping_principle` | theorem | theorem contraction_mapping_principle [CompleteSpace E] (T : E → E) (hT : IsContraction T) : ∃! x, Function.IsFixedPt T x | no |
| `BoundedLinearOperator` | abbrev | abbrev BoundedLinearOperator (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] | no |
| `operatorNormRatios` | def | def operatorNormRatios (T : E →L[ℝ] F) : Set ℝ | no |
| `operator_norm_eq_sSup_ratio` | theorem | theorem operator_norm_eq_sSup_ratio (T : E →L[ℝ] F) : | no |
| `bounded_linear_iff_linear_continuous` | theorem | theorem bounded_linear_iff_linear_continuous (T : E → F) : | no |
| `IsCompactMap` | def | def IsCompactMap (T : E → F) : Prop | no |
| `MapsBoundedSequencesToConvergentSubsequences` | def | def MapsBoundedSequencesToConvergentSubsequences (T : E → F) : Prop | no |
<sub>6 modules, 63 declarations, 0 admitted.</sub>

**Han-Lin elliptic PDE chapters** — `HanLinLectureNotes` — modules: `AbsoluteGradientBound`, `AbsoluteGradientEstimate`, `BallMoments`, `ConverseMeanValue`, `GradientEstimate`, `Harmonic` (+28 more)

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `IsHarmonicOn.fderiv_norm_le_of_norm_le_on_closedBall` | theorem | theorem IsHarmonicOn.fderiv_norm_le_of_norm_le_on_closedBall [Nonempty (Fin n)] {u : EuclideanSpace Real (Fin n) -> Real} {x : EuclideanSpace Real (Fin n)} {R M... | no |
| `IsHarmonicOn.fderiv_norm_le_ball` | theorem | theorem IsHarmonicOn.fderiv_norm_le_ball [Nonempty (Fin n)] {u : EuclideanSpace Real (Fin n) -> Real} {x : EuclideanSpace Real (Fin n)} {R : Real} (hR : 0 < R) ... | no |
| `exists_interior_gradient_holder_const` | theorem | theorem exists_interior_gradient_holder_const [Nonempty (Fin n)] : ∃ c : Real, 0 < c ∧ ∀ (u : EuclideanSpace Real (Fin n) → Real), | no |
| `setIntegral_ball_comp_isometry` | lemma | lemma setIntegral_ball_comp_isometry (e : EuclideanSpace Real (Fin n) ≃ₗᵢ[Real] EuclideanSpace Real (Fin n)) (f : EuclideanSpace Real (Fin n) -> Real) (r : Real... | no |
| `setIntegral_ball_clm` | lemma | lemma setIntegral_ball_clm (L : EuclideanSpace Real (Fin n) →L[Real] Real) (r : Real) : | no |
| `coordReflect` | def | def coordReflect (i : Fin n) : | no |
| `coordReflect_apply` | lemma | lemma coordReflect_apply (i j : Fin n) (z : EuclideanSpace Real (Fin n)) : | no |
| `coordSwap` | def | def coordSwap (i j : Fin n) : | no |
<sub>34 modules, 313 declarations, 0 admitted.</sub>

### 5.3 topology

**CW complexes** — `Hatcher` — modules: `CellComplexes`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `IsCWComplex` | abbrev | abbrev IsCWComplex {X : Type u} [TopologicalSpace X] (C : Set X) | no |
| `CharacteristicMap` | abbrev | abbrev CharacteristicMap {X : Type u} [TopologicalSpace X] (C : Set X) [Topology.CWComplex C] (n : ℕ) (i : Topology.CWComplex.cell C n) | no |
| `IsFiniteDimensionalCW` | abbrev | abbrev IsFiniteDimensionalCW {X : Type u} [TopologicalSpace X] (C : Set X) [Topology.CWComplex C] | no |
| `IsCWSubcomplex` | def | def IsCWSubcomplex {X : Type u} [TopologicalSpace X] [T2Space X] (C A : Set X) [Topology.CWComplex C] : Prop | no |
| `IsCWPair` | abbrev | abbrev IsCWPair {X : Type u} [TopologicalSpace X] [T2Space X] (A : Set X) [Topology.CWComplex (Set.univ : Set X)] : Prop | no |
| `IsCWSubcomplex.isClosed` | theorem | theorem IsCWSubcomplex.isClosed {X : Type u} [TopologicalSpace X] [T2Space X] {C A : Set X} [Topology.CWComplex C] (h : IsCWSubcomplex C A) : IsClosed A | no |
| `IsCWPair.isClosed` | theorem | theorem IsCWPair.isClosed {X : Type u} [TopologicalSpace X] [T2Space X] {A : Set X} [Topology.CWComplex (Set.univ : Set X)] (h : IsCWPair A) : IsClosed A | no |
| `Skeleton` | abbrev | abbrev Skeleton {X : Type u} [TopologicalSpace X] [T2Space X] (C : Set X) [Topology.CWComplex C] (n : ℕ∞) | no |
<sub>1 modules, 21 declarations, 0 admitted.</sub>

**covering spaces** — `Hatcher` — modules: `CoveringSpaces`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `CoveringMap` | abbrev | abbrev CoveringMap (p : E → X) : Prop | no |
| `EvenlyCovered` | abbrev | abbrev EvenlyCovered (p : E → X) (x : X) : Prop | no |
| `CoveringMap.surjective_of_pathConnectedSpace` | theorem | theorem CoveringMap.surjective_of_pathConnectedSpace (cov : CoveringMap p) [PathConnectedSpace X] (e₀ : E) : | no |
| `localSectionPathBasis` | def | private def localSectionPathBasis (p : E → X) : Set (Set E) | no |
| `locPathConnectedSpace_of_isLocalHomeomorph` | theorem | theorem locPathConnectedSpace_of_isLocalHomeomorph (hp : IsLocalHomeomorph p) [LocallyPathConnectedSpace X] : | no |
| `CoveringMap.locPathConnectedSpace` | theorem | theorem CoveringMap.locPathConnectedSpace (cov : CoveringMap p) [LocallyPathConnectedSpace X] : LocallyPathConnectedSpace E | no |
| `IsLift` | def | def IsLift (p : E → X) (f : C(A, X)) (f' : C(A, E)) : Prop | no |
| `liftHomotopy` | def | noncomputable def liftHomotopy (cov : CoveringMap p) (H : C(↑unitInterval × A, X)) (f : C(A, E)) (h₀ : ∀ a, H (0, a) = p (f a)) : C(↑unitInterval × A, E) | no |
<sub>1 modules, 19 declarations, 0 admitted.</sub>

**universal cover construction** — `Hatcher` — modules: `UniversalCoverConstruction`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `Fiber` | abbrev | abbrev Fiber (x₀ x : X) | no |
| `fiberTopology` | def | def fiberTopology (x₀ x : X) : TopologicalSpace (Fiber x₀ x) | no |
| `fiberTopologicalSpace` | instance | local instance fiberTopologicalSpace (x₀ x : X) : TopologicalSpace (Fiber x₀ x) | no |
| `fiberDiscreteTopology` | instance | local instance fiberDiscreteTopology (x₀ x : X) : DiscreteTopology (Fiber x₀ x) | no |
| `Space` | abbrev | abbrev Space (x₀ : X) | no |
| `endpoint` | def | def endpoint {x₀ : X} : Space x₀ → X | no |
| `pathInSet` | def | def pathInSet {U : Set X} (hU : IsPathConnected U) (a b : U) : Path a b | no |
| `pathInSetVal` | def | def pathInSetVal {U : Set X} (hU : IsPathConnected U) (a b : U) : Path a.1 b.1 | no |
<sub>1 modules, 52 declarations, 0 admitted.</sub>

**spheres and simply-connectedness** — `Hatcher` — modules: `Sphere`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `loop_nullhomotopic_of_isSimplyConnected` | theorem | theorem loop_nullhomotopic_of_isSimplyConnected {X : Type u} [TopologicalSpace X] {A : Set X} {x : X} (hx : x ∈ A) (hA : IsSimplyConnected A) (γ : Loop x) (hγ :... | no |
| `coveredLoopProduct_nullhomotopic` | theorem | theorem coveredLoopProduct_nullhomotopic {X : Type u} [TopologicalSpace X] {x : X} {ι : Type v} (carrier : ι → Set X) (hx : ∀ i, x ∈ carrier i) (hsc : ∀ i, IsSi... | no |
| `simplyConnectedSpace_of_pathConnectedOpenCover` | theorem | theorem simplyConnectedSpace_of_pathConnectedOpenCover {X : Type u} [TopologicalSpace X] [PathConnectedSpace X] {x₀ : X} {ι : Type v} (cover : PathConnectedOpen... | no |
| `sphereComplementHomeomorphEuclidean` | theorem | theorem sphereComplementHomeomorphEuclidean {n : ℕ} (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) : | no |
| `sphereComplementTwoPointsHomeomorphPuncturedEuclidean` | theorem | theorem sphereComplementTwoPointsHomeomorphPuncturedEuclidean {n : ℕ} (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1) : | no |
| `standardSpherePole` | def | def standardSpherePole (k : ℕ) : | no |
| `standardSphereBasepoint` | def | def standardSphereBasepoint (k : ℕ) : | no |
| `standardSphereBasepoint_ne_pole` | theorem | private theorem standardSphereBasepoint_ne_pole (k : ℕ) : | no |
<sub>1 modules, 26 declarations, 0 admitted.</sub>

**the circle** — `Hatcher` — modules: `Circle`

| declaration | kind | statement (head) | admitted upstream |
|---|---|---|---|
| `UnitCircle` | abbrev | abbrev UnitCircle | no |
| `CircleFiber` | abbrev | abbrev CircleFiber | no |
| `unitCircleCover` | def | def unitCircleCover : C(ℝ, UnitCircle) | no |
| `unitCircleCov` | def | def unitCircleCov : IsCoveringMap ((↑) : ℝ → UnitCircle) | no |
| `fiberPoint` | def | def fiberPoint (e : ((↑) : ℝ → UnitCircle) ⁻¹' ({0} : Set UnitCircle)) : CircleFiber | no |
| `endpointFiber` | def | def endpointFiber (g : FundamentalGroup UnitCircle 0) : CircleFiber | no |
| `endpointFiber_one` | theorem | theorem endpointFiber_one : endpointFiber (1 : FundamentalGroup UnitCircle 0) = 0 | no |
| `fiberLoop` | def | def fiberLoop (z : CircleFiber) : FundamentalGroup UnitCircle 0 | no |
<sub>1 modules, 51 declarations, 0 admitted.</sub>

## 6. Coverage gaps found by the inventory

Keyword hits are over all 23,478 scanned top-level declarations (case-insensitive, name match):

| concept | matching declarations |
|---|---:|
| surgery | 0 |
| entropy | 0 |
| sobolev | 0 |
| moise | 0 |
| perelman | 0 |
| canonical neighbourhood | 0 |
| hamilton-ival | 0 |

- The primary `PoincareConjecture` package is an empty stub: 3 files / 37 lines / 0
  declarations, and its blueprint has 278 of 279 environments marked `\notready`.
- `Thurston`, `CaoZhu`, `CheegerGromovTaylor`, `ChowEtAl` are blueprint-only stubs
  (0 declarations each).
- Noncollapsing exists only as four *definitions* in KleinerLott (`RicciFlow/Noncollapsing.lean`, 45 lines: `HasCurvatureBoundOnParabolicBall`, `IsKappaNoncollapsedOnScale`, `IsKappaCollapsedAt`) with no theorem attached.
- The three Topping modules that would be most interesting for parabolic PDE
  (`ParabolicPDE/Scalar.lean`, `ParabolicPDE/Vector.lean`, `ParabolicPDE/Contraction.lean`)
  begin with `import Mathlib`, i.e. a probe would have to build the whole library;
  they are left `conditional` rather than probed. No selected probe closure imports
  `Mathlib` wholesale.

## 7. Adapter probes and compile evidence

The probe package `probes/` (Lake package `D13Probes`) requires the upstream
packages by path and pins Lean v4.32.1. Probes only `#check` upstream
declarations, build adapter terms from them, and `#print axioms` their
footprint; no proof is restated and no upstream file is modified.

### 7.1 Import closures (admitted-proof exclusion)

Token scan of the D13 Lean sources (`probes/`): 6 files, hard matches 0, soft matches 0 — verdict **clean**.

| probe | direct imports | upstream modules in closure | mathlib imports in closure | modules with hard tokens |
|---|---:|---:|---:|---:|
| `ComparisonProbe.lean` | 4 | 325 | 155 | 0 |
| `GeometryProbe.lean` | 7 | 197 | 108 | 0 |
| `HeatProbe.lean` | 7 | 16 | 21 | 0 |
| `PetersenProbe.lean` | 3 | 80 | 79 | 0 |
| `SharedProbe.lean` | 5 | 10 | 13 | 0 |
| `TopologyProbe.lean` | 3 | 13 | 33 | 0 |

Verdict: **clean** — no probe transitively imports a module that contains an admitted step.

### 7.2 Compile exits

| target | exit | seconds | #check-ed | #print axioms | probes' own warnings | sorryAx in log |
|---|---:|---:|---:|---:|---:|---|
| `D13Probes.ComparisonProbe` | 0 | 4 | 8 | 97 | 0 | no |
| `D13Probes.GeometryProbe` | 0 | 4 | 27 | 5 | 0 | no |
| `D13Probes.HeatProbe` | 0 | 3 | 16 | 5 | 0 | no |
| `D13Probes.PetersenProbe` | 0 | 3 | 6 | 4 | 0 | no |
| `D13Probes.SharedProbe` | 0 | 3 | 16 | 5 | 0 | no |
| `D13Probes.TopologyProbe` | 0 | 4 | 26 | 5 | 0 | no |

All exits zero: **True**; `sorryAx` seen anywhere in the build logs: **False**.

Durable artifact evidence: **461** upstream modules and **3151** mathlib modules have an `.olean` on disk produced by these runs (a module is only listed if it elaborated successfully).  The final re-run of each target was incremental, so the per-target seconds above are not the full build times; run-1 times were SharedProbe (post-update hook failure), TopologyProbe 522 s, HeatProbe 164 s, PetersenProbe 216 s, GeometryProbe 254 s, ComparisonProbe 172 s (failed on a probe typo) and 0 failures after the fix.

Upstream modules elaborated here, by package:

| package | modules built |
|---|---:|
| `DoCarmo` | 206 |
| `MorganTian` | 136 |
| `Petersen` | 80 |
| `Evans` | 16 |
| `Hatcher` | 13 |
| `shared` | 10 |

`#print axioms` footprints requested by the probes (`propext`, `Classical.choice`, `Quot.sound` are mathlib's standard axioms):

| declaration | axioms |
|---|---|
| `BilinearForm.riesz` | propext, Classical.choice, Quot.sound |
| `BilinearForm.riesz_unique` | propext, Classical.choice, Quot.sound |
| `EvansLib.exists_parabolicBoundary_isMaxOn` | propext, Classical.choice, Quot.sound |
| `EvansLib.heatKernelSpatial_solves_heat` | propext, Classical.choice, Quot.sound |
| `EvansLib.heatSolution_isSolutionOfIVP` | propext, Classical.choice, Quot.sound |
| `EvansLib.heatSolution_solves_heat` | propext, Classical.choice, Quot.sound |
| `EvansLib.heat_cauchy_maxPrinciple_smallTime` | propext, Classical.choice, Quot.sound |
| `FiberBundle.t2Space_totalSpace` | propext, Classical.choice, Quot.sound |
| `HatcherLib.CoveringMap.surjective_of_pathConnectedSpace` | propext, Classical.choice, Quot.sound |
| `HatcherLib.IsCWSubcomplex.isClosed` | propext, Classical.choice, Quot.sound |
| `HatcherLib.coveringPiOneMap_injective` | propext, Classical.choice, Quot.sound |
| `HatcherLib.existsUnique_liftHomotopy` | propext, Classical.choice, Quot.sound |
| `HatcherLib.sphereSimplyConnected_of_two_le` | propext, Classical.choice, Quot.sound |
| `MorganTianLib.bishop_gromov_radial` | propext, Classical.choice, Quot.sound |
| `MorganTianLib.ricci_curvature_comparison_of_not_conjugate` | propext, Classical.choice, Quot.sound |
| `MorganTianLib.sectional_curvature_comparison_of_not_conjugate` | propext, Classical.choice, Quot.sound |
| `PetersenLib.compactManifold_geodesicallyComplete` | propext, Classical.choice, Quot.sound |
| `PetersenLib.gaussLemma` | propext, Classical.choice, Quot.sound |
| `PetersenLib.hopfRinowTheorem` | propext, Classical.choice, Quot.sound |
| `PetersenLib.maximalGeodesic_leavesCompactSet` | propext, Classical.choice, Quot.sound |
| `Riemannian.AffineConnection.isAlgCurvatureForm_curvatureFormAt` | propext, Classical.choice, Quot.sound |
| `Riemannian.AffineConnection.koszul_formula` | propext, Classical.choice, Quot.sound |
| `Riemannian.AffineConnection.leviCivita_cov_inner_unique` | propext, Classical.choice, Quot.sound |
| `Riemannian.Exponential.exists_gauss_lemma_ball` | propext, Classical.choice, Quot.sound |
| `Riemannian.Geodesic.exists_global_geodesic` | propext, Classical.choice, Quot.sound |
| `Shared.LengthSpace.edist_le_pathLength` | propext, Classical.choice, Quot.sound |
| `TangentBundle.t2Space` | propext, Classical.choice, Quot.sound |

Upstream **self-audits** that executed during the ComparisonProbe build: 94 `#print axioms` commands in MorganTian sources, all reporting axiom sets {propext, Classical.choice, Quot.sound}. None reports an admitted-proof axiom.

## 8. Declaration classification

| class | meaning |
|---|---|
| `compiled` | the containing module was elaborated by our own build in the pinned environment and the declaration has no admitted step |
| `conditional` | statement present, proof not checked by this invocation (`reason` records why) |
| `model` | data/structure declaration: definitional vocabulary rather than an assertion |
| `statement-only` | upstream declaration whose body carries an admitted step, or an `axiom` |
| `upstream source claim` | asserted in upstream blueprint/prose with no Lean declaration (the `\notready` entries of section 4) |

Upstream modules built here: 461. Declaration counts: `compiled` 3404, `model` 891, `conditional` 18912, `statement-only` 271, plus 669 blueprint `upstream source claim` entries.

| package | compiled | model | conditional | statement-only |
|---|---:|---:|---:|---:|
| `DoCarmo` | 1561 | 338 | 905 | 0 |
| `MorganTian` | 894 | 148 | 3454 | 0 |
| `Petersen` | 585 | 139 | 3770 | 0 |
| `Hatcher` | 151 | 158 | 871 | 0 |
| `Evans` | 187 | 83 | 678 | 0 |
| `shared` | 26 | 25 | 0 | 0 |
| `ChowKnopf` | 0 | 0 | 23 | 0 |
| `GilbargTrudinger` | 0 | 0 | 63 | 0 |
| `HanLinLectureNotes` | 0 | 0 | 314 | 0 |
| `KleinerLott` | 0 | 0 | 96 | 0 |
| `LeeRiemannian` | 0 | 0 | 1447 | 0 |
| `LeeSmooth` | 0 | 0 | 5574 | 271 |
| `Topping` | 0 | 0 | 1717 | 0 |

## 9. Reuse assessment against the local release pin

The local release package (`release/`) is pinned to Lean `v4.34.0-rc2` + mathlib
`7974e751bece493b6ff508039423ca9fa2452fa8`. The upstream snapshot is pinned to Lean
`v4.32.1` + mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`. The pins differ in
both Lean and mathlib, so **no upstream module can be imported into `release/`**, and
changing either pin is out of scope for this task. Consequences:

- upstream material is usable as *specification and proof-design reference* only;
- any port must be re-elaborated against the release pin, at which point the ported
  declaration becomes original work, not an import;
- adapter probes therefore live in their own package under the upstream pin, which is
  exactly what makes their exit codes meaningful evidence about upstream, not about
  the release package.

### 9b. Per-package port guidance (evidence-based)

| package | best use for a future port | caveat |
|---|---|---|
| `shared` | smallest token-free unit (877 lines, 51 decls): bilinear-form/Riesz API, length-space predicate, T2 instance for tangent bundles | none; ideal first port |
| `DoCarmo` | deepest chart-level Riemannian core (293 files, token-free): `AffineConnection`/`IsLeviCivita`/`koszul_formula`, geodesic ODE and completeness, exponential/Gauss lemma, Jacobi fields, Bonnet-Myers | very large; duplicated with Petersen |
| `Petersen` | cleanest headline manifold-level statements: `gaussLemma`, `hopfRinowTheorem`, `compactManifold_geodesicallyComplete` | duplicates DoCarmo vocabulary |
| `MorganTian` | Bishop-Gromov radial comparison and sectional/Ricci comparison; Ch2-Ch5 Ricci-flow machinery (573 files, token-free) | depends on DoCarmoLib |
| `Topping` | parabolic PDE toolkit (Holder spaces, scalar/vector estimates), curvature evolution, DeTurck existence | 3 core modules start with `import Mathlib` |
| `Evans` | self-contained heat kernel / Cauchy problem / maximum principles / mean value (65 files, token-free) | Euclidean (not manifold) setting |
| `Hatcher` | covering-space lifting, `PiOne` functoriality, sphere simple connectivity, CW complexes (58 files, token-free) | topology only; no smooth structure |
| `KleinerLott` | statement-level noncollapsing vocabulary (`IsKappaNoncollapsedOnScale`) and a Hopf-Rinow variant | definitions only, no theorems attached |
| `LeeSmooth` | smooth-manifold vocabulary (552 files) | **271 admitted declarations**; must not be imported as proof |
| `PoincareConjecture`, `Thurston`, `CaoZhu`, `CheegerGromovTaylor`, `ChowEtAl` | blueprint only | 0 Lean declarations |

## 10. Environment blockers and workarounds

- `release.lean-lang.org` does not resolve in this sandbox, so `elan toolchain install`
  fails; the v4.32.1 tarball is downloaded from the GitHub release through the
  sandbox's SOCKS proxy and unpacked into a workspace-local `ELAN_HOME`
  (`.elan-home/`), leaving the global elan installation untouched.
- `cache.lean-lang.org` and `mathlib4.azureedge.net` are unreachable, so mathlib
  olean caches cannot be fetched; mathlib must be built from source at the pinned rev.
- The v4.32.1 toolchain is not preinstalled (only `v4.34.0-rc2`), so all compile
  evidence depends on the proxy download above; this is an environment limitation,
  not a mathematical one.

## 11. Reproduction

```bash
python3 tools/d13_provenance_check.py          # snapshot vs upstream git tree
python3 tools/d13_scan_upstream.py third_party/frenzymath/Poincare-Conjecture manifest
python3 tools/d13_api_inventory.py             # topic-tagged API inventory
python3 tools/d13_blueprint_inventory.py       # \notready statement-level entries
python3 tools/d13_probe_import_closure.py      # admitted-proof exclusion for probes
tools/d13_fetch_mathlib.sh                     # pinned mathlib 520045ab (shallow)
tools/d13_fetch_deps.sh                        # pinned transitive deps
tools/d13_build_probes.sh D13Probes.SharedProbe D13Probes.HeatProbe \
    D13Probes.TopologyProbe D13Probes.GeometryProbe D13Probes.PetersenProbe \
    D13Probes.ComparisonProbe
python3 tools/d13_collect_probe_results.py     # exit codes + classification
python3 tools/d13_make_result_card.py          # this card
```

