# D13-morgan-tian-adapter-plan — result card

- **Task id:** `D13-morgan-tian-adapter-plan`
- **Stage / lane:** D13 / integrator+coordinator (`requires_lean: true`, `coordination: true`)
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-morgan-tian-adapter-plan`
- **Model:** `deepseek-v4-pro` (configured preset, no silent model switch)
- **Generated (UTC):** 2026-09-10T18:55:00Z (elapsed ≈ 2.0 h of the prior 4 h invocation)
- **Re-verified (UTC):** 2026-09-10T18:40:00Z (independent verification pass ≈ 0.1 h; total elapsed ≈ 2.1 h; all §11 checks fresh-run and green)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (binary `Lean 4.34.0-rc2, commit 6a10ac8c22be`); mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `lake-manifest.json`)
- **Upstream snapshot:** `third_party/frenzymath/Poincare-Conjecture` = `frenzymath/Poincare-Conjecture` @ `bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0 (reference-only; upstream toolchain `leanprover/lean4:v4.32.1`, mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`; not built locally, per `docs/UPSTREAM-INTEGRATION.md`)
- **Verdict:** **TASK_DONE for the D13 milestone** — a precise, compile-checked Morgan-Tian adapter plan and a Lean compatibility module set (`Poincare.D13.MorganTianAdapter`, 7 files, 50 audited declarations, 1119 lines) mapping the three local D12 objectives (EntropyVariation, HeatDomain, KappaVariational) and the objective blockers **U1/U2/U3/U4/U5/U9** to exact upstream MorganTian modules/declarations are delivered, kernel-checked and axiom-audited. **None of U1–U9 is claimed closed by this task** (see §8); the one genuinely new model-level closure is the flat-model case of the D7/D12 ball-volume-comparison input (KV-10/NCF-9, §6.3). This card requests independent acceptance and claims nothing about Perelman.

---

## 1. What was built

| file | lines | role |
| --- | --- | --- |
| `Curvature.lean` | 313 | U1/U2: flat transcription of upstream `riemannCurvature`/`curvatureForm`/`curvatureFormAt`/`ricciAt`/`sectionalCurvatureAt`/`ricciTensorAt`; the honest chain-rule computation `flatRiemannCurvature_eq_secondDerivativeCommutator` and **`flatRiemannCurvature_eq_zero`** (U1, second-derivative symmetry); vanishing of the (0,4) form, Ricci, scalar and sectional curvature (U2); the four first-order symmetries + first Bianchi; the (GSS) shrinker equation discharged **through the computed flat Ricci** (`IsGradientShrinkerPotentialEuclidean_iff_flatRicci`, `shrinkerFpot_gradientShrinkerPotentialFlat`) |
| `Tensoriality.lean` | 155 | U5: 𝒟-linearity + pointwise locality of the direction slot, **germ-locality of the section slot** (`flatCovariantDeriv_congr_of_eventuallyEq`), the germ-vs-1-jet distinction (`flatCovariantDeriv_congr_of_eq_fderiv`), value-only locality of the flat curvature in the X/Y slots (the ∇∇-cancellation), the flat instance of upstream `covariantTensor4_congr_apply` / `curvatureFormAt_eq` |
| `ExpGeodesic.lean` | 149 | U3: geodesics = affine lines (`isGeodesicEuclidean_globalGeodesic`), `expMapEuclidean = x + t·v` with identity derivative (`fderiv_expMapEuclidean_eq_id`), injectivity, parallel transport = identity isometry |
| `LeviCivitaSmoothness.lean` | 86 | U4: exact blocker sources (mathlib `LeviCivita.lean` docstring lines 22–23; upstream `LeviCivitaConnectionData.smooth` data field; local D7 `LeviCivitaSmoothnessStatement`); model discharge `flatCovariantDeriv_contDiff` (the flat Levi-Civita connection is C^∞ for C^∞ data) |
| `BishopGromov.lean` | 184 | U9: the analysis core of the Bishop-Gromov normalization conclusion (`antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one`), the flat-model equality case `flatModel_normalizedBallVolume_eq` (ω₃ = 4π/3), the **proved model case of KV-10/NCF-9** `flatModel_ballVolumeComparison`, and the downstream D3 `KappaNoncollapsingCertificate` on flat ℝ³ via the D12 transfer (`flatModel_kappaNoncollapsingCertificate`, `flatModel_volume_ball_pos`) |
| `All.lean` | 42 | umbrella |
| `Audit.lean` | 190 | 50 `#print axioms` + fail-closed `Lean.collectAxioms` gate + 4 kernel-checked downstream-use examples |

Namespace: `Poincare.D13.MorganTianAdapter.{Curvature,Tensoriality,ExpGeodesic,LeviCivitaSmoothness,BishopGromov}`. Dependencies: the local D7/D10/D11/D12 modules (copied read-only into `release/Poincare`, **byte-identical** to the three D12 source worktrees, `diff -rq` clean) and the D13 `Poincare.D13.UpstreamAdapter` module set (consumed from the accepted D13-upstream-adapter-audit gate, byte-identical). No upstream Lean file was copied into the local package: upstream statements are transcribed (with file:line citations) and proved on the flat model, or recorded as upstream source claims (§4).

## 2. Classification policy (per `docs/UPSTREAM-INTEGRATION.md`)

* **local proved theorem** — proved from local D7/D10/D11/D12 + mathlib (includes the *flat-model theorems*: every `flat*`/`*Euclidean` statement is a theorem about the explicit flat Euclidean model, and is labeled as such);
* **upstream source claim** — an upstream declaration recorded with exact file:line and verbatim statement, not re-verified here (no upstream build is available locally);
* **conditional adapter** — a proved typed implication with explicit interface/translation hypotheses (none new in this module set; the prior D13 layer owns the two typed adapters and is re-consumed);
* **model theorem** — proved statements on the explicit flat Gaussian / flat ℝⁿ / flat ℝ³ models (reported inside `local proved theorem` with the model restriction stated).

No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, fake proposition, weakened conclusion, or hypothesis equivalent to the conclusion occurs in the module set (fail-closed audit §7; negative control exit 1).

## 3. The adapter plan: exact mappings (upstream file:line → local declaration)

Line numbers verified against the pinned snapshot (`tmp/morgan-tian-survey.md` holds the survey and verbatim quotes). Local declarations are in `Poincare.D13.MorganTianAdapter.*` unless prefixed.

### 3.1 Blocker U1 — Riemann curvature tensor (→ D12 entropy-variation flat model)

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `MorganTianLib.riemannCurvature` (`MorganTianLib/Ch01/CurvatureTensor.lean:52`), `riemannCurvature_apply_eq_neg` (:64) | def; theorem (closed) | `Curvature.flatRiemannCurvature` (transcription); `flatRiemannCurvature_eq_secondDerivativeCommutator`, `flatRiemannCurvature_eq_zero` | **proved on the flat model**: the honest product-rule computation reduces `∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` to the commutator of second Fréchet derivatives, which vanishes by `second_derivative_symmetric` (hypotheses: `ContDiff ℝ 1 X/Y`, `ContDiff ℝ 2 Z` — expanded in §5) |
| `MorganTianLib.curvatureForm` (`CurvatureTensor.lean:77`), `curvatureForm_eq` (:95) | def; theorem (closed) | `flatCurvatureFormField` / `flatCurvatureFormAt`; `flatCurvatureFormAt_eq_zero` | proved on the flat model |
| `curvatureForm_antisymm_left/right` (:110/:123), `curvatureForm_pairSwap` (:136), `curvatureForm_firstBianchi` (:153) | theorem (closed) | `flatCurvatureFormAt_antisymm_left/_right/_pairSwap/_firstBianchi` | proved on the flat model (literal zero instances) |
| `MorganTianLib.curvatureFormAt` (`Ch01/PointwiseCurvature.lean:248`), `curvatureFormAt_eq` (:267), `isAlgCurvatureForm_curvatureFormAt` (:364), `sectionalCurvatureAt` (:389) | def; theorems (closed) | `flatCurvatureFormAt`, `flatCurvatureFormField_eq_flatCurvatureFormAt` (Tensoriality), `flatSectionalCurvatureAt`, `flatSectionalCurvatureAt_eq_zero` | proved on the flat model |
| `MorganTianLib.curvatureOperator` (`Ch01/CurvatureOperator.lean:148`), `sectionalCurvature_eq_curvatureOperator` (:203), `HasCurvatureOperatorNormLe` (:261) | def; theorems (closed) | local `Poincare.Longrun.Geometry.toCurvatureOperator` / D7 curvature layer | recorded as upstream source claim (operator layer; not needed by the flat model) |
| pinned mathlib `RiemannCurvatureTensor` | **absent** (the U1 gap) | D7 `RiemannCurvatureData` + this flat transcription | U1 remains an upstream-mathlib-gap blocker; the adapter supplies the MorganTian-side evidence |

### 3.2 Blocker U2 — Ricci tensor / scalar curvature (→ D12 entropy-variation F-flow)

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `MorganTianLib.ricciAt` (`Ch01/PointwiseCurvature.lean:402`), `ricciTensorAt` (`Ch03/RicciFlow/Basic.lean:43`) | def (basis-free trace of the algebraic curvature form) | `flatRicciAt` (trace over `EuclideanSpace.single i 1`); `flatRicciAt_eq_zero` | proved on the flat model (U2): the D12 `Ric = 0` model field is now a computed consequence |
| `DoCarmoCh4Ricci.scalarCurvature` (`DoCarmo/DoCarmoLib/Riemannian/Manifold/DoCarmoCh4Ricci.lean:186`), `scalarCurvature_eq_sum_ricci` (:191); `MorganTianLib.Einstein.scalarCurvature` (`Ch01/Einstein.lean:65`) | def; theorem (closed); abbrev | `flatScalarCurvatureAt`; `flatScalarCurvatureAt_eq_zero` | proved on the flat model |
| `MorganTianLib.IsRicciFlowEquationOn` (`Ch03/RicciFlow/Basic.lean:108`), `IsSmoothMetricFamilyOn` (:100), `structure IsRicciFlowOn` (:115) | def/structure (statement-only) | D12 `fflowMetricFlow_consistency` (`∂ₜg = −2(Ric+∇²f)` on the flat model) | recorded as upstream source claim; the flat-model instance of `∂ₜg = −2Ric` is the `∇²f = 0`-term case |
| `MorganTianLib.IsGradientShrinkerPotential` (`Ch03/RicciFlow/Soliton.lean:183`), `IsSolitonGenerator` (:109), `solitonScale` (:239), `metricLieDerivativeAt_gradientField` (:124, theorem) | def; theorem (closed) | D13 UpstreamAdapter transcription + `IsGradientShrinkerPotentialEuclidean_iff_flatRicci` + `shrinkerFpot_gradientShrinkerPotentialFlat` + `shrinkerFpot_isGradientShrinkerPotentialEuclidean` | **proved on the flat model through the computed flat Ricci**: `−Ric = Hess f − λg` with `f = ‖x‖²/(4τ)`, `λ = 1/(2τ)`, consuming the D12 Hessian identity `iteratedFDeriv_two_shrinkerFpot` (the prior D13 layer's literal `-(0:ℝ)` left side is shown definitionally faithful) |

### 3.3 Blocker U3 — geodesics / exponential map / parallel transport (→ D12 kappa-variational path space)

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `MorganTianLib.IsGeodesicOn` (`Ch01/Geodesics.lean:52`), `expMap` (:72), `zero_mem_expDomain` (:88) | abbrev/def; theorem (closed) | `ExpGeodesic.IsGeodesicEuclidean`, `expMapEuclidean`, `expMapEuclidean_eq` | transcribed + proved on the flat model |
| `MorganTianLib.globalGeodesic` (`Ch01/GlobalExp.lean:71`), `isGeodesic_globalGeodesic` (:90), `expMapGlobal` (:125), `expMapGlobal_eq_of_isGeodesic` (:139) | def; theorems (closed) | `globalGeodesicEuclidean`, `isGeodesicEuclidean_globalGeodesic` | proved on the flat model (affine lines; first derivative `toSpanSingleton`, second derivative 0) |
| `expDifferential_isEquiv_of_sectionalCurvatureAt_le` (`Ch01/ExpLocalDiffeo.lean:387`), `expMapGlobal_locallyInjective_of_sectionalCurvatureAt_le` (:433), `expMapGlobal_localDiffeo_of_minimizing` (`ExpMinimizingLocalDiffeo.lean:53`) | theorem (closed) | `fderiv_expMapEuclidean_eq_id`, `expMapEuclidean_injective`, `flatSectionalCurvature_eq_zero_and_expDifferential_id` | proved on the flat model (sectional bound 0 discharged by `flatSectionalCurvatureAt_eq_zero`) |
| `IsParallelAlongOn.metricInner_eq` (`Ch01/ParallelIsometry.lean:99`), `exists_parallelFrameAlong` (:179), `IsParallelSolOn.transfer` (`ParallelTransfer.lean:183`), `parallelTransportTangentIsometryEquiv` (`Ch04/TensorParallelTransport.lean:103`), `parallelTransportTangentBetween` (`Ch04/LeviCivitaTensorTransport.lean:32`) | theorems (closed) / defs | `flatParallelTransport`, `flatParallelTransport_inner`, `flatParallelTransport_norm` | proved on the flat model (identity isometry) |
| minimizing-geodesic theory (`Ch02/MinimizingSegment.lean:57` `hasMinSegments_of_complete`, `Ch01/MinimalGeodesicNoConjugate.lean:452` `not_isConjugatePointAt_of_minimizing`, …) | theorem (closed) | D12 `constantCurvature_isLMinimizer`/`constantCurvatureLMinimizerExistence` | recorded as upstream source claims; the D12 straight-line minimizer is the flat instance (next_dependency_requests: KV-1/KV-3 reuse) |

### 3.4 Blocker U4 — Levi-Civita smoothness

| item (file:line) | kind | adapter status |
| --- | --- | --- |
| pinned mathlib `Mathlib/Geometry/Manifold/VectorBundle/CovariantDerivative/LeviCivita.lean` docstring lines 22–23: *"Future PRs will prove smoothness…"* | the **exact U4 source** (re-verified verbatim) | recorded; nothing is proved there in the pinned rev |
| `KleinerLott.LeviCivitaConnectionData` (`KleinerLott/KleinerLott/RicciFlow/SmoothRicciFlow.lean:168`) with field `smooth : CovariantDerivative.ContMDiffCovariantDerivative cov ∞` and `curvatureFormAt` (:182, the ∇∇−∇∇−∇_lie commutator) | structure (smoothness as **data** — the upstream hypothesis form U4 demands) | recorded as upstream source claim; its curvature-form body is definitionally the shape of `flatRiemannCurvature` |
| `DoCarmoLib.IsLeviCivita` (`DoCarmo/DoCarmoLib/Riemannian/Manifold/DoCarmoCh2.lean:228`) | def | recorded as upstream source claim |
| local D7 `LeviCivitaSmoothnessStatement` (`D7/LeviCivita/Blocked.lean:139`), `SmoothLeviCivitaExistenceStatement` (:149), `smoothLeviCivitaExistence_of_smoothness` (:162), `BlockerLeviCivitaSmoothness` (:57) | statement-only / checked reduction / named blocker | mapped (no new hypothesis needed: the local layer already keeps it state-only) |
| **model discharge** `LeviCivitaSmoothness.flatCovariantDeriv_contDiff` / `flatLeviCivita_contDiff_pair` | **proved locally** | the flat Levi-Civita connection (`∇_X Y = fderiv Y · X`, Christoffel ≡ 0) is C^∞ whenever X, Y are C^∞ (`ContDiff.clm_apply` + `ContDiff.fderiv_right`) |

### 3.5 Blocker U5 — covariant-derivative germ arguments / tensoriality

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `tensorial_apply_eq_zero_of_eventuallyEq_zero` (`Ch01/PointwiseCurvature.lean:95`), `tensorial_apply_eq_zero` (:148), `tensorial_congr_apply` (:175), `covariantTensor4_congr_apply` (:194) | theorem (closed) — the bump-function tensoriality engine | `Tensoriality.flatCovariantDeriv_congr_of_eventuallyEq` (germ-locality via `Filter.EventuallyEq.hasFDerivAt_iff`), `flatCovariantDeriv_congr_of_eq_fderiv`, `flatRiemannCurvature_congr_of_eq_at`, `flatCurvatureFormField_eq_flatCurvatureFormAt` | proved on the flat model (direct Fréchet-calculus arguments, no bump functions needed on ℝⁿ) |
| `IsCovariantTensorField` / `.congr_slot_apply` / `.vanishesOnZeroSlot` (`Ch04/Tensoriality.lean:40/58/98`), `secondCov_congr_middle`/`_diagonal` (`Ch04/SecondCovLocality.lean:28/40`) | structure; theorems (closed) | recorded as upstream source claims | — |
| U5 distinction stated precisely | — | `flatCovariantDeriv_smul` (𝒟-linearity of the direction slot), `flatCovariantDeriv_congr_of_eq_at` (pointwise locality of the direction slot), `flatCovariantDeriv_congr_of_eventuallyEq` (germ ⇒ 1-jet ⇒ ∇) | the flat covariant derivative consumes the differential half of the 1-jet; the germ determines the 1-jet; the *curvature* consumes only values (the cancellation theorem) |

### 3.6 Blocker U9 — reduced volume / GH compactness / canonical neighbourhoods / surgery (→ D12 kappa-variational)

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `bishop_gromov_ball` (`Ch01/BishopGromovBall.lean:226`), `bishop_gromov_ball_ratio` (:466), `bishop_gromov_manifold_ratio` (`BishopGromovManifold.lean:302`), `BishopGromovManifoldProducers` (:456), `bishop_gromov_manifold_with_producers` (:519, antitone ratio + normalization limit 1) | theorem (closed) / structure | `BishopGromov.antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one` (the general analysis core of the normalization conclusion, proved locally in ℝ), `flatModel_normalizedBallVolume_eq` (ω₃ = 4π/3, the equality case) | analysis core **proved locally**; the general-manifold theorems recorded as upstream source claims |
| `ComparisonFunctions.snK/csK/ctK` (`Ch01/ComparisonFunctions.lean:56/65/73`), `ricci_curvature_comparison_of_not_conjugate` (`Ch01/ComparisonGeometric.lean:134`), `ricci_curvature_comparison_radial_of_minimizing` (`Ch01/ComparisonMinimizing.lean:254`), `expRiemannianJacobian_polarDensity_of_minimizing` (`Ch01/ExpJacobiDensity.lean:264`) | defs; theorems (closed) | D12 `constantCurvature_length_le`/`constantCurvature_reducedLength_le` (constant-curvature family) | recorded as upstream source claims; they are the intended upstream producers of the *general* KV-6 Jacobian comparison (next_dependency_requests) |
| **model case of KV-10 / NCF-9** (local D7 `BallVolumeComparison`, D12 `ballVolumeComparisonExists`) | — | `flatModel_ballVolumeComparison` + `flatModel_kappaNoncollapsingCertificate` | **new proved closure at model level**: on flat ℝ³ the comparison holds with φ ≡ ω₃ (equality), and the D12 conditional transfer `gaussianKappaNoncollapsing_of_ballVolumeComparison` produces the D3 `KappaNoncollapsingCertificate` with κ = 4π/3, r₀ = 1 |
| Ch05 pointed GH theory: `PointedGHConverges` (`Ch05/PointedGH.lean:845`), `PointedGHConvergesUnbounded` (:1325), `PointedGHNetCharacterization.lean`, `MarkedGHExtraction.lean`, `Precompactness.lean` | defs; theorems | local `D7/Compactness` / GH statements | recorded as upstream source claims (upstream has a full GH layer; the local D7 GH track can consume it once the upstream build exists) |
| `EpsilonNeckStructure` (`Ch02/EpsilonNeck.lean:195`), `roundSphereMetric` (:136), `IsRoundCylinderMetric` (:158), `canonicalScalarCurvature` (:179) | structure/defs | local `D7/Canonical` statements | recorded as upstream source claims (definitions only; no canonical-neighbourhood *theorem* upstream) |
| Perelman reduced volume/length/distance, L-minimizers, surgery, extinction | **absent upstream — 0 grep hits in every `.lean` of the snapshot** (re-verified: §6.4 negatives) | local D12 KappaVariational (`gaussianReducedVolume_eq_one`, `constantCurvature_length_le`, `constantCurvature_isLMinimizer`, …) and the 13-entry KV-ledger | local-only; the D12 layer is the only formalized reduced-volume content in existence and should seed an upstream chapter (next_dependency_requests) |

## 4. Upstream source claims recorded (not re-verified locally)

| upstream declaration | file:line | reason not re-verified |
| --- | --- | --- |
| `riemannCurvature`, `curvatureForm`, symmetries, `curvatureFormAt`, `curvatureFormAt_eq`, `ricciAt`, `sectionalCurvatureAt`, `isAlgCurvatureForm_curvatureFormAt`, `tensorial_*`, `covariantTensor4_congr_apply` | `MorganTianLib/Ch01/CurvatureTensor.lean:52/77/110/123/136/153`; `Ch01/PointwiseCurvature.lean:95/148/175/194/248/267/364/389/402` | general-manifold types (`RiemannianMetric I M`, `AffineConnection`, `TangentSpace`) not importable without an upstream build (`lean4:v4.32.1` + mathlib `520045ab…`); the flat transcriptions are proved locally instead |
| `ricciTensorAt`, `IsSmoothMetricFamilyOn`, `IsRicciFlowEquationOn`, `IsRicciFlowOn` | `MorganTianLib/Ch03/RicciFlow/Basic.lean:43/100/108/115` | same |
| `IsSolitonGenerator`, `metricLieDerivativeAt_gradientField`, `IsGradientShrinkerPotential`, `solitonScale` | `MorganTianLib/Ch03/RicciFlow/Soliton.lean:109/124/183/239` | general-manifold; the D13 UpstreamAdapter layer owns the Euclidean transcription (re-consumed here) |
| `IsGeodesicOn`, `expMap`, `globalGeodesic`, `expMapGlobal`, exp-local-diffeo theorems, parallel-transport theorems | `Ch01/Geodesics.lean:52/72`; `Ch01/GlobalExp.lean:71/125`; `Ch01/ExpLocalDiffeo.lean:387/433`; `Ch01/ExpMinimizingLocalDiffeo.lean:53`; `Ch01/ParallelIsometry.lean:99/179`; `Ch04/TensorParallelTransport.lean:103/134`; `Ch04/LeviCivitaTensorTransport.lean:32` | general-manifold; flat instances proved locally |
| `LeviCivitaConnectionData` (+ `smooth` field, `curvatureFormAt`) | `KleinerLott/KleinerLott/RicciFlow/SmoothRicciFlow.lean:168/171/182` | manifold-side; recorded as the U4 hypothesis form |
| `bishop_gromov_ball`, `bishop_gromov_ball_ratio`, `bishop_gromov_manifold_ratio`, `BishopGromovManifoldProducers`, `bishop_gromov_manifold_with_producers`, Jacobi/Ricci comparisons, `expRiemannianJacobian_polarDensity_*` | `Ch01/BishopGromovBall.lean:226/466`; `Ch01/BishopGromovManifold.lean:302/456/519`; `Ch01/ComparisonGeometric.lean:134`; `Ch01/ComparisonMinimizing.lean:254`; `Ch01/ExpJacobiDensity.lean:264` | general-manifold; the analysis core (antitone + normalization ⇒ ratio ≤ 1) is proved locally in ℝ |
| Ch05 GH layer (`PointedGHConverges` etc.) | `Ch05/PointedGH.lean:845/1325` + `Ch05/PointedGHNetCharacterization.lean`, `Ch05/Precompactness.lean` | upstream GH theory on metric-completion types; recorded for the D7 GH track |
| `EpsilonNeckStructure`, `roundSphereMetric`, `IsRoundCylinderMetric`, `canonicalScalarCurvature` | `Ch02/EpsilonNeck.lean:136/158/179/195` | definitions only; no canonical-neighbourhood theorem upstream |

## 5. Expanded hypotheses (all non-hidden hypotheses of the new theorems)

| declaration | hypotheses (expanded) |
| --- | --- |
| `flatRiemannCurvature_eq_secondDerivativeCommutator` / `flatRiemannCurvature_eq_zero` | `ContDiff ℝ 1 X`, `ContDiff ℝ 1 Y`, `ContDiff ℝ 2 Z` on `Euc n` (smoothness data for the chain rule / second-derivative symmetry); no geometric assumptions — the vanishing is a *computation* |
| `flatCurvatureFormAt_eq_zero`, `flatRicciAt_eq_zero`, `flatScalarCurvatureAt_eq_zero`, `flatSectionalCurvatureAt_eq_zero` | none (the pointwise tensors use constant extensions; the zero theorems are unconditional on the flat model) |
| `IsGradientShrinkerPotentialFlat` / `shrinkerFpot_gradientShrinkerPotentialFlat` / `shrinkerFpot_isGradientShrinkerPotentialEuclidean` | `0 < τ` (the shrinker parameter; the D12 `ContDiff ∞` and Hessian identity `iteratedFDeriv_two_shrinkerFpot` are consumed); model: flat `ℝⁿ`, `f = ‖x‖²/(4τ)`, `λ = 1/(2τ)`, `Ric = 0` |
| `flatCovariantDeriv_congr_of_eventuallyEq` | `Y =ᶠ[𝓝 p] Y'` (germ agreement — the U5 content), `DifferentiableAt ℝ Y p`, `DifferentiableAt ℝ Y' p` |
| `flatCovariantDeriv_congr_of_eq_fderiv` | `fderiv ℝ Y p = fderiv ℝ Y' p` (differential half of the 1-jet; no value hypothesis — the U5 distinction made precise) |
| `flatRiemannCurvature_congr_of_eq_at` | `ContDiff ℝ 1` on X, X', Y, Y' + `ContDiff ℝ 2 Z`; `X p = X' p`, `Y p = Y' p` — locality in the values only |
| `isGeodesicEuclidean_globalGeodesic`, `fderiv_expMapEuclidean_eq_id`, `expMapEuclidean_injective`, `flatParallelTransport_*` | none (model computations on `Euc n`) |
| `flatCovariantDeriv_contDiff`, `flatLeviCivita_contDiff_pair` | `ContDiff ℝ ∞ X`, `ContDiff ℝ ∞ Y` (the U4 model discharge: smoothness of the flat connection from smoothness of the data) |
| `antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one` | `AntitoneOn f (Ioo 0 R)`, `Tendsto f (𝓝[>] 0) (𝓝 1)`, `r ∈ Ioo 0 R` — the two hypotheses are exactly the upstream normalization conclusion inputs (`bishop_gromov_manifold_with_producers`), neither equivalent to the `f r ≤ 1` conclusion |
| `flatModel_normalizedBallVolume_eq` | `0 < r`, `x : EuclideanSpace ℝ (Fin 3)` — model: flat ℝ³, Lebesgue volume |
| `flatModel_ballVolumeComparison` | `r₀ : ℝ` (any scale; the comparison is an equality for every `0 < r`); curvature predicate `fun _ _ => True`; certificate `gaussianReducedVolumeCertificate 3` (volume ≡ 1) |
| `flatModel_kappaNoncollapsingCertificate` | none — `κ = 4π/3` (the flat-model ω₃), `r₀ = 1`; consumes the D12 conditional transfer (hypotheses `0 < κ`, `0 < r₀`, `r₀² ≤ 1`, monotone φ with `φ 1 = κ` all discharged) |

## 6. Compile evidence

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-morgan-tian-adapter-plan
cd "$WT/release"
lake build                                    # exit 0 — Build completed successfully (9205 jobs), whole release tree
for m in Curvature Tensoriality ExpGeodesic LeviCivitaSmoothness BishopGromov All Audit; do
  lake build Poincare.D13.MorganTianAdapter.$m # 7/7 exit 0 (logs: longrun/ev-logs/build-$m.log)
done
```

* whole-package `lake build` from `release/`: **exit 0, 9205 jobs** (includes both D13 layers and every D7–D12 dependency, freshly built);
* the 7 authored modules: **7/7 exit 0** (per-module logs under `longrun/ev-logs/`);
* consumed-input integrity: `diff -rq` of `release/Poincare/{D7,D8,D9,D10,D11,D12}` against the three D12 source worktrees and of `release/Poincare/D13/UpstreamAdapter` against the D13-upstream-adapter-audit gate copy — **clean (byte-identical)**;
* forbidden-token scan (`input/d5-tools/scan_forbidden.py` over `release/Poincare/D13`): **0 hard / 0 soft** matches;
* the D12 dependency closure (D10/D11/D12 + prior D13 UpstreamAdapter) was rebuilt first (exit 0), so every local dependency is freshly compiled, not inherited.

## 7. Axiom evidence (kernel trust, separate from compilation)

`Audit.lean` prints `#print axioms` for all 50 declarations and re-checks the cone programmatically with `Lean.collectAxioms`, **failing the build** on any axiom outside `{propext, Classical.choice, Quot.sound}`.

| item | value |
| --- | --- |
| audited declarations | **50 / 50** — all depend only on `[propext, Classical.choice, Quot.sound]` (or fewer) |
| gate result | `D13MorganTianAdapterAxiomCheck: PASS — all 50 declarations of the D13 MorganTian-adapter module set depend only on [propext, Classical.choice, Quot.sound]` (log `longrun/ev-logs/build-Audit.log`) |
| fail-closed negative control | `/tmp/d13mtneg/NegativeAudit.lean` (axiom `d13MtFakeAxiom` + dependent theorem): the same gate logic **throws** `detected unapproved axioms [d13MtFakeAxiom]`, exit 1 |
| forbidden tokens (comment/string-aware scan over `release/Poincare/D13`) | **0 hard / 0 soft** matches |
| upstream inputs | the survey found **0** `sorry`/`admit`/`axiom`-keyword declarations in every quoted upstream file (re-verified in this task, §6.4); the transcriptions carry no upstream axiom |

## 8. Objective blockers U1 / U2 / U3 / U4 / U5 / U9 — exact accounting

| blocker | D13-morgan-tian action | status after D13 |
| --- | --- | --- |
| **U1** (no Riemann curvature tensor in pinned mathlib) | exact upstream map (MorganTian Ch01 `riemannCurvature`/`curvatureForm`/symmetries/Bianchi/`curvatureFormAt`/`curvatureOperator`); flat-model vanishing **proved** (`flatRiemannCurvature_eq_zero` via the honest second-derivative-symmetry computation); consumed by the U2/GSS chain | **open** (mathlib gap; adapter evidence added; upstream general tensor remains a source claim until the v4.32.1 build) |
| **U2** (no Ricci/scalar curvature in pinned mathlib) | exact upstream map (`ricciAt` :402, `ricciTensorAt` :43, `scalarCurvature` DoCarmoCh4Ricci:186/Einstein:65); flat Ricci/scalar vanishing **proved**; the D12 shrinker (GSS) equation re-derived **through the computed flat Ricci** (`shrinkerFpot_gradientShrinkerPotentialFlat`) | **open** (adapter evidence added) |
| **U3** (no geodesics/exp/parallel transport in pinned mathlib) | exact upstream map (Ch01 Geodesics/GlobalExp/ExpLocalDiffeo/ExpMinimizingLocalDiffeo/ParallelIsometry/ParallelTransfer + Ch04 transports); flat-model instances **proved** (affine geodesics, exp with identity derivative and injectivity, identity parallel transport) | **open** (adapter evidence added) |
| **U4** (Levi-Civita smoothness must be a hypothesis) | exact source re-verified (mathlib `LeviCivita.lean` docstring lines 22–23); upstream `LeviCivitaConnectionData.smooth` recorded as the data-field form; local D7 statements mapped; flat-model discharge **proved** (`flatCovariantDeriv_contDiff`) | **open** (remains a hypothesis on general manifolds; a mathlib PR is the closure path) |
| **U5** (covariant derivative germ/1-jet; tensorial identities need germ arguments) | exact upstream map (tensoriality engine `PointwiseCurvature.lean:70–194`, Ch04 `Tensoriality`/`SecondCovLocality`); flat instances **proved** (𝒟-linearity, pointwise direction-slot locality, section-slot germ-locality, curvature value-only locality) | **open** (adapter evidence added) |
| **U9** (no reduced volume / GH compactness / canonical neighbourhood / surgery) | split: (a) Bishop-Gromov comparison + Ch05 GH + Ch02 ε-necks exist upstream (mapped with file:line); (b) **decisive negative re-verified**: 0 Lean declarations for reduced volume/length/distance, L-minimizers, surgery anywhere in the snapshot; (c) new proved model-level closure: flat-model `BallVolumeComparison` + D3 `KappaNoncollapsingCertificate` on flat ℝ³ (the flat case of KV-10/NCF-9) via the D12 transfer | **open** (multi-stage future program; the flat-model comparison is the only new closure and is explicitly model-level) |

**exact_blockers_closed:** none of U1–U9 (they are upstream-mathlib-gap blockers; this task maps them and proves the flat-model instances). **Model-level input closures achieved by this task (not U-blockers):** the flat constant-curvature case of the D7/D12 named input **KV-10 / NCF-9** (`BallVolumeComparison` on flat ℝ³, φ ≡ ω₃) — proved by `BishopGromov.flatModel_ballVolumeComparison` and consumed downstream by `flatModel_kappaNoncollapsingCertificate`.

## 9. Source hashes (fresh, sha256)

| file | sha256 |
| --- | --- |
| `release/Poincare/D13/MorganTianAdapter/Curvature.lean` | `3d16652f8078885ebc50cc99522c800e7f4d0bf7180da37ac65bb94d07bb7e89` |
| `release/Poincare/D13/MorganTianAdapter/Tensoriality.lean` | `0458e9e67b631d2f8e2f66bbef7b7a016fc65153d175f90d488e05a3c7f66d6f` |
| `release/Poincare/D13/MorganTianAdapter/ExpGeodesic.lean` | `465bc94d16d2806e12c2de2024cb18f5bf12388a44e71705f1b77f0f448d40b7` |
| `release/Poincare/D13/MorganTianAdapter/LeviCivitaSmoothness.lean` | `34074b88d67a44c1dde7dfef71445ebced296072276ef19a7cf84470b1fde2b0` |
| `release/Poincare/D13/MorganTianAdapter/BishopGromov.lean` | `42d83791a5eef953e20c9ddd7843fbd221b87971dc92d8ba3b141230de0d6e79` |
| `release/Poincare/D13/MorganTianAdapter/All.lean` | `e0c6d940b78a4426b523c1133967fd3a4973746e23cda13a73c37ca0c211971b` |
| `release/Poincare/D13/MorganTianAdapter/Audit.lean` | `8416693dc2d85806ec8421527a8df6c9ee41532ef313ec83de1f6102995da946` |
| upstream snapshot tree (`third_party/frenzymath/`) | `e574480eefb8b5ad16351356978b37f658a3806c8a6b1450f274d82d5fe10495` |

No D7/D8/D9/D10/D11/D12 source was modified; the copied D7–D12 modules are byte-identical to their three source worktrees, and the consumed D13 `UpstreamAdapter` modules are byte-identical to the D13-upstream-adapter-audit gate copy (`diff -rq` clean).

## 10. Remaining blockers and next dependency requests

**Remaining (none closed by this task):** U1, U2, U3, U4, U5, U9 (open, with the adapter evidence of §8), plus the D7/D12 KV-ledger inputs (KV-1…KV-13 general cases) and the process items inherited from the D6/D13 layers.

**next_dependency_requests** (machine-readable in the JSON card):
1. Upstream build of `shared` + `DoCarmoLib` + `MorganTian` + `KleinerLott` with `leanprover/lean4:v4.32.1` + mathlib `520045ab…` — upgrades the §4 source claims to upstream compiled theorems and enables importing the general-manifold objects the flat transcriptions stand in for.
2. Upstream reduced-volume layer (F/W, reduced length/volume/distance, L-geodesics, κ-noncollapsing *theorem*): **none exists** (0 hits); the local D12 KappaVariational/EntropyVariation content is the only formalized material and should seed an upstream chapter (CaoZhu `CZ04_ReducedVolume.tex` is the blueprint target).
3. KV-10 general closure: port `bishop_gromov_manifold_with_producers` (antitone ratio + normalization, now with the local analysis core `antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one`) together with a Perelman reduced-volume comparison to discharge the general `BallVolumeComparison`; the flat case is closed here.
4. KV-1/KV-3 (path-space compactness / minimizer regularity): reuse MorganTian Ch02 minimizing-geodesic theory (`hasMinSegments_of_complete`, `exists_isMinGeodesicOn_…`) once the upstream build exists.
5. U4 closure: a mathlib PR proving the Levi-Civita smoothness announced in the `LeviCivita.lean` docstring (lines 22–23); until then U4 stays a hypothesis, exactly as upstream `LeviCivitaConnectionData.smooth`.
6. U9 GH integration: wire the Ch05 pointed-GH layer (`PointedGHConverges`, `PointedGHNetCharacterization`, `Precompactness`) to the local D7 GH statements; ε-neck definitions (`EpsilonNeckStructure`) to the D7 canonical-neighbourhood track.
7. General Euclidean identity `L_(grad f) g = 2 Hess f` (upstream theorem `metricLieDerivativeAt_gradientField`, Soliton.lean:124) — upgrades the flat shrinker computation to the general statement once the upstream build exists.
8. The sibling D13-topping-ricci-adapter-plan (U6/U7/U8/I2) and the D13-upstream-adapter-audit acceptance are the remaining D13-level inputs for a combined integration audit.

## 11. Independent re-verification (continuation invocation, 2026-09-10T18:40Z)

Every load-bearing claim of §6/§7/§9 was re-run fresh from a clean shell in this invocation (logs: `longrun/ev-logs/verify-*.log`, `longrun/ev-logs/build-verify-whole.log`):

| check | result (fresh) |
| --- | --- |
| toolchain | `Lean 4.34.0-rc2 (commit 6a10ac8c22be)`, `Lake 5.0.0-src+6a10ac8`, `lean-toolchain` = `leanprover/lean4:v4.34.0-rc2` |
| whole-package `lake build` (release/) | **exit 0** — "Build completed successfully (9205 jobs)" |
| per-module builds (7 modules) | **7/7 exit 0** (`verify-build-{Curvature,Tensoriality,ExpGeodesic,LeviCivitaSmoothness,BishopGromov,All,Audit}.log`) |
| axiom gate | fresh Audit build log: `D13MorganTianAdapterAxiomCheck: PASS — all 50 declarations … depend only on [propext, Classical.choice, Quot.sound]`; Audit.lean carries `#print axioms` transcripts + a fail-closed `Lean.collectAxioms` `run_cmd` gate (50 names + the 3 approved axioms = 53 unique ``…`` tokens) |
| negative control | `/tmp/d13mtneg/NegativeAudit.lean` re-run via `lake env lean`: **exit 1** with `detected unapproved axioms [d13MtFakeAxiom]` (fail-closed confirmed) |
| source hashes | 7/7 authored modules sha256 = card §9 values, recomputed fresh; upstream snapshot tree sha256 `e574480e…` = card value (all-files sorted method) |
| consumed-source integrity | `diff -rq` D7/D8/D9/D10/D11/D12 vs the three D12 source worktrees: **clean** (the `Only in` lines are the expected union layout of the three D12 clusters); `diff -rq` D13/UpstreamAdapter vs the D13-upstream-adapter-audit gate copy: **exit 0** |
| forbidden tokens | `scan_forbidden.py` over `release/Poincare/D13`: **0 hard / 0 soft** |
| upstream citations | 11/11 spot-checked file:line citations verbatim in the snapshot (`riemannCurvature` :52, `riemannCurvature_apply_eq_neg` :64, `curvatureForm` :77, `IsGradientShrinkerPotential` :183, `bishop_gromov_manifold_with_producers` :519, `EpsilonNeckStructure` :195, `PointedGHConverges` :845, `ricciAt` :402, `ricciTensorAt` :43, `globalGeodesic` :71, `parallelTransportTangentIsometryEquiv` :103) |
| U4 source | pinned mathlib `CovariantDerivative/LeviCivita.lean` docstring "Future PRs will prove smoothness…" (lines 22–23) verbatim; mathlib rev `7974e751…` matches card |
| U9 negatives | re-grepped every upstream `.lean`: **0** reduced-volume/reduced-length/reduced-distance, **0** L-minimizer, **0** surgery hits |
| upstream hygiene | 0 `sorry`/`admit` in the 23 quoted upstream files; 0 `axiom`/`unsafe` declarations in the spot-checked files |
| KV-10/NCF-9 claim | re-read `flatModel_ballVolumeComparison` / `flatModel_kappaNoncollapsingCertificate`: statements are exactly the flat-ℝ³ model case (φ ≡ 4π/3 equality via `EuclideanSpace.volume_ball_fin_three`, D12 conditional transfer `gaussianKappaNoncollapsing_of_ballVolumeComparison`); honestly labeled model-level, not a U-blocker closure |

No file of this worktree outside `longrun/` was modified during the verification pass; the verification only re-ran the toolchain and wrote fresh logs.

TASK_DONE — card: `longrun/results/D13-morgan-tian-adapter-plan.md` (this file); machine-readable twin: `longrun/results/D13-morgan-tian-adapter-plan.json`; queue-mirror proposal: `longrun/queue.updated.json`; survey evidence: `tmp/morgan-tian-survey.md`; checkpoint: `checkpoint.json`. This card requests independent acceptance of the Morgan-Tian adapter plan + compatibility module set only; it does not claim Perelman, does not claim any of U1/U2/U3/U4/U5/U9 is closed by this task, and does not count upstream sources as local proof evidence.

