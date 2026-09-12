# D13-upstream-adapter-audit — result card

- **Task id:** `D13-upstream-adapter-audit`
- **Stage / lane:** D13 / auditor+integrator (`requires_lean: true`, `coordination: true`)
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-upstream-adapter-audit`
- **Model:** `deepseek-v4-pro` (configured preset, no silent model switch)
- **Generated (UTC):** 2026-09-10T19:20:00Z (elapsed ≈ 2.4 h of the 4 h invocation)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (binary `Lean 4.34.0-rc2, commit 6a10ac8c22be`); mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `lake-manifest.json`)
- **Upstream snapshot:** `third_party/frenzymath/Poincare-Conjecture` = `frenzymath/Poincare-Conjecture` @ `bb91a091f0b968f8bbe8d861e025a88d82b161be`, Apache-2.0 (reference-only; toolchain `leanprover/lean4:v4.32.1`, mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`; not built locally, per `docs/UPSTREAM-INTEGRATION.md`)
- **Verdict:** **TASK_DONE for the D13 milestone** — a precise, compile-checked upstream-adapter plan and a small Lean compatibility module (`Poincare.D13.UpstreamAdapter`, 6 files, 36 audited declarations, 1129 lines) mapping all three local D12 objectives (EntropyVariation, HeatDomain, KappaVariational) to exact upstream modules/declarations are delivered, kernel-checked and axiom-audited. The objective blockers A1/A2/A3/P1/P5 are each accounted for with fresh evidence; **none is claimed closed by this task** (see §8). This card requests independent acceptance and claims nothing about Perelman.

---

## 1. What was built

| file | lines | role |
| --- | --- | --- |
| `EvansHeat.lean` | 457 | Evans Ch02 heat-kernel chain (definitions `heatKernelSpatial`/`heatSolution`, normalization, bounded initial-condition theorem re-proved locally, bounded test-function class as a D12 v1 `AdmissibleTestClass`, compact finite-measure equivalence) |
| `EvansParametric.lean` | 105 | upstream Evans `hasDerivAt_integral_mul_hasCompactSupport` re-proved **through** the local D12 `hasDerivAt_weightedIntegral_constWeight` |
| `MorganTianShrinker.lean` | 221 | MorganTian Ch03 (GSS)/soliton-generator/`solitonScale` equations in Euclidean transcription, satisfied by the local D12 Gaussian shrinker |
| `KleinerLottKappa.lean` | 140 | KleinerLott κ-noncollapsing predicates transcribed verbatim + conditional adapter to the local D3/D7 `KappaNoncollapsingCertificate` |
| `All.lean` | 28 | umbrella |
| `Audit.lean` | 178 | 36 `#print axioms` + fail-closed `Lean.collectAxioms` gate + 4 kernel-checked downstream-use examples |

Namespace: `Poincare.D13.UpstreamAdapter.{Evans,MorganTian,KleinerLott}`. Dependencies: local D7/D10/D11/D12 modules (copied read-only into `release/Poincare`, byte-identical across the three D12 source worktrees) + mathlib. No upstream Lean file was copied into the local package: the upstream statements are transcribed (with file:line citations) and re-proved locally, or recorded as upstream source claims (§4).

## 2. Classification policy (per `docs/UPSTREAM-INTEGRATION.md`)

Every declaration in the module set carries one class, recorded in the docstrings and the JSON card:

* **local proved theorem** — a theorem proved from local D7/D10/D11/D12 + mathlib;
* **upstream compiled theorem (locally re-verified)** — the upstream statement transcribed verbatim, with a closed proof re-verified by the local kernel (upstream file:line cited);
* **upstream source claim** — an upstream declaration recorded with exact file:line and verbatim statement, not re-verified here (only the transcription predicates/defs and the items listed in §4);
* **conditional adapter** — a locally proved typed implication with explicit interface/translation hypotheses, each expanded and justified;
* **model theorem** — a proved statement on the explicit flat Gaussian/one-point models.

No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, fake proposition, weakened conclusion, or hypothesis equivalent to the conclusion occurs in the module set (fail-closed audit §6).

## 3. The adapter plan: exact mappings (upstream file:line → local declaration)

Line numbers verified against the pinned snapshot (`tmp/upstream-survey.md` holds the full verbatim quotes).

### 3.1 D12-entropy-variation (`Poincare.D12.EntropyVariation`)

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `EvansLib.hasDerivAt_integral_mul_hasCompactSupport` (`formalized-sources/Evans/EvansLib/Ch02/HeatIVP.lean:55`) | theorem (closed) | `Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral` / `_constWeight` (`WeightedIntegral.lean:58/83`) | **re-proved locally through the local D12 theorem** (`EvansParametric.lean`) — downstream use of the local theorem in the upstream statement's exact form |
| `EvansLib.hasFDerivAt_parametricIntegral_iteratedFDeriv` (`…/Ch02/ParametricIntegral.lean:143`), `contDiff_parametricIntegral` (:263) | theorem (closed) | same mathematical family (compact-parameter all-orders smoothness; the local theorems are the 1-D `HasDerivAt` form needed by Perelman's F-derivative) | recorded as upstream source claim (spherical-mean chain; not required by local D12) |
| `MorganTianLib.IsGradientShrinkerPotential` (`…/MorganTian/MorganTianLib/Ch03/RicciFlow/Soliton.lean:183`), `IsSolitonGenerator` (:109), `solitonScale` (:239) | defs (predicates) | `GaussianShrinker.iteratedFDeriv_two_shrinkerFpot`, `FFlowModel.fflowMetricScale` | **Euclidean transcription proved on the model**: `shrinkerFpot_isGradientShrinkerPotentialEuclidean`, `shrinkerGrad_isSolitonGeneratorEuclidean`, `solitonScale_eq_fflowMetricScale` (`MorganTianShrinker.lean`) |
| F/W functionals, monotonicity, `dF/dt = 2∫|Ric+∇²f|²`, second moment `2nτ` | **absent upstream** (0 grep hits in every package; only CaoZhu blueprint LaTeX `CZ04_ReducedVolume.tex`) | local D12 FFlowModel/GaussianShrinker | local-only; new upstream work required (next_dependency_requests) |

### 3.2 D12-heat-domain-repair (`Poincare.D12.HeatDomain`)

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `EvansLib.heatKernelSpatial` (`…/Ch02/Heat.lean:32`), `heatKernel` (:124) | def | `Poincare.D10.HeatKernelEuclidean.gaussianKernel` / D11 `flatKernel` | **proved definitional identity** `heatKernelSpatial_eq_gaussianKernel` |
| `EvansLib.heatKernelSpatial_integral` (`Heat.lean:47`) | theorem (closed) | D10 `gaussianKernel_integral`; D12 KappaVariational `gaussianReducedVolume_eq_one` | **re-proved locally** (`heatKernelSpatial_integral`) |
| `EvansLib.heatSolution` (`HeatIVP.lean:110`) | def | D11 bridge convolution | **proved identity** `heatSolution_eq_flatKernelConv` (t > 0) |
| `EvansLib.heatSolution_tendsto_initial_of_bounded` (`HeatIVPBounded.lean:916`) | theorem (closed) | the bounded-continuous admissible class of the D12 v1 repair | **re-proved locally** (`heatSolution_tendsto_initial_of_bounded`, plus joint form) using D11 Gaussian tail lemmas + D10 mass |
| `EvansLib.heatSolution_tendsto_initial_pt` (`HeatIVPLimit.lean:61`) | lemma (closed) | D11 `flatKernel_tendsto_integral_of_hasCompactSupport` | re-typed locally (`heatSolution_tendsto_initial_of_integrable`) |
| upstream bounded class as a **v1 `AdmissibleTestClass`** | — | `AdmissibleTestClass.continuousIntegrableClass` | **`boundedContinuousClass` is admissible iff the measure is finite; on compact finite-measure spaces it equals the D12 integrable class and `WeakInitialConditionFor D (bounded class) ↔ D.FullInitialCondition`** (proved) |

### 3.3 D12-kappa-variational (`Poincare.D12.KappaVariational`)

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `KleinerLott.RicciFlowData` (`…/KleinerLott/KleinerLott/RicciFlow/FlowData.lean:16`), `RicciFlowData.ball` (`Noncollapsing.lean:15`), `HasCurvatureBoundOnParabolicBall` (:21), `IsKappaNoncollapsedOnScale` (:30), `IsKappaCollapsedAt` (:39) | structure + defs (predicates; the snapshot proves no κ-noncollapsing theorem) | `Poincare.Longrun.Topology.KappaNoncollapsingCertificate` / `CurvatureBoundedOn`; D7 `kappaNoncollapsing_of_entropy_and_volumeComparison` | **transcribed verbatim + conditional adapter** `isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate` (expanded translation hypotheses `hcurv`, `hvol`, domain/scale alignment) |
| Gaussian reduced volume `Ṽ(τ) = ∫ (4πτ)^(-n/2) e^(-‖q‖²/4τ) = 1` | present only as Evans `heatKernelSpatial_integral`; nothing upstream is *called* reduced volume | D12 KappaVariational `gaussianReducedVolume_eq_one` | identity via the Evans theorem (rfl-transport) |
| L-length bound, `IsLMinimizer`, reduced distance, κ-noncollapsing *theorem* | **absent upstream** (0 hits; only blueprint LaTeX in CaoZhu `CZ04_ReducedVolume.tex` and MorganTian Ch08/Ch16) | D12 KappaVariational `constantCurvature_length_le`, `constantCurvature_isLMinimizer`, … | local-only; upstream KleinerLott `HasRadialDistancePathsOn`/MorganTian Ch01/Ch02 minimizing-geodesic theory are the intended building blocks (next_dependency_requests) |

**Decisive negative (verified by the full-snapshot survey, `tmp/upstream-survey.md`):** the snapshot contains **no Lean declaration** for Perelman `F`/`W` entropy, reduced distance/length/volume, L-minimizers, or κ-noncollapsing theorems (0 grep hits for `WEntropy|Fentropy|ntropy|reducedVolume|reducedLength|L-length|IsLMinimizer` in every package; 0 `sorry`/`admit`/`axiom`-keyword in every quoted upstream file). Integration therefore proceeds *from the local D12 results into* the upstream geometry (MorganTian soliton chapter, KleinerLott predicates, Evans Ch02), not by importing missing upstream theorems.

## 4. Upstream source claims recorded (not re-verified locally)

| upstream declaration | file:line | reason not re-verified |
| --- | --- | --- |
| `EvansLib.hasFDerivAt_parametricIntegral_iteratedFDeriv`, `hasFTaylorSeriesUpTo_parametricIntegral`, `contDiff_parametricIntegral(_of_order)` | `formalized-sources/Evans/EvansLib/Ch02/ParametricIntegral.lean:143/237/263/272/302` | compact-parameter spherical-mean chain; not needed by the three D12 objectives (the local D12 ℝ-parameter theorem is the needed form) |
| `EvansLib.heatSolution_solves_heat(_of_bounded)`, `heatSolution_isSolutionOfIVP` | `…/Ch02/HeatIVP.lean:382`, `HeatIVPBounded.lean:737`, `HeatIVPSmooth.lean:197` | heat-equation fields of the D7 datum; D11 already proves `∂ₜK = ΔK` locally; transcription is mechanical, deferred to the heat-semigroup track |
| `MorganTianLib.metricLieDerivativeAt_gradientField` (theorem), `GradientShrinkingRicciSoliton`, `GeneratesGradientShrinkingSoliton` | `…/Ch03/RicciFlow/Soliton.lean:124/224/215` | general-manifold types (`RiemannianMetric I M`, `TangentSpace I p`, `SmoothVectorField I M`) not importable without an upstream build; the Euclidean transcription exposes the identity as the explicit hypothesis `hgradLie` in the conditional adapter |
| `KleinerLott.MetricFamily`/`toFlowData`, `SmoothCompleteRicciFlowOn`/`toFlowData` | `…/RicciFlow/MetricFamily.lean:15/51`, `SmoothRicciFlow.lean:221/258` | manifold-side producers of `RicciFlowData`; the `induced_distance` field (SmoothRicciFlow.lean:236) is the upstream justification of the adapter's `hvol` translation |
| KleinerLott `HasRadialDistancePathsOn` / `HasAlmostRadialDistancePathsOn`, `IsProperAt` | `…/RicciFlow/PointSelection.lean:299/317/293` | minimizer-existence-like hypotheses; mapped to local KV-1/KV-3 (path-space compactness/minimizer regularity) as future inputs |
| CaoZhu blueprint theorems (L-length variations, reduced-volume monotonicity, κ-noncollapsing) | `formalized-sources/CaoZhu/blueprint/src/chapters/CZ04_ReducedVolume.tex:60/78/213/241/261` | LaTeX with `\sketch` proofs; no Lean counterpart in the snapshot |

## 5. Compile evidence

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-upstream-adapter-audit
cd "$WT/release"
lake build Poincare.D13.UpstreamAdapter.All      # exit 0 — Build completed successfully (8909 jobs)
for f in Poincare/D13/UpstreamAdapter/{EvansHeat,EvansParametric,MorganTianShrinker,KleinerLottKappa,All,Audit}.lean; do
  lake env lean "$f"                             # 6/6 exit 0
done
# D12 dependency closure (three D12 All targets) also rebuilt from scratch: exit 0 (8960 jobs)
```

Per-file logs: `longrun/ev-logs/lean-{EvansHeat,EvansParametric,MorganTianShrinker,KleinerLottKappa,All,Audit}.log` (each exit 0, 0 warnings). The three D12 `All` modules (`HeatDomain`, `EntropyVariation`, `KappaVariational`) were rebuilt first (8960 jobs, exit 0), so every local dependency is freshly compiled, not inherited.

## 6. Axiom evidence (kernel trust, separate from compilation)

`Audit.lean` prints `#print axioms` for all 36 declarations and re-checks the cone programmatically with `Lean.collectAxioms`, **failing the build** on any axiom outside `{propext, Classical.choice, Quot.sound}`.

| item | value |
| --- | --- |
| audited declarations | **36 / 36** — all depend only on `[propext, Classical.choice, Quot.sound]` |
| gate result | `D13UpstreamAdapterAxiomCheck: PASS — all 36 declarations … depend only on [propext, Classical.choice, Quot.sound]` (log `longrun/ev-logs/lean-Audit.log`) |
| fail-closed negative control | `/tmp/d13neg/NegativeAudit.lean` (axiom `d13AuditFakeAxiom` + dependent theorem): the same gate logic **throws** `detected unapproved axioms [d13AuditFakeAxiom]`, exit 1 |
| forbidden tokens (comment/string-aware `input/d5-tools/scan_forbidden.py` over `release/Poincare/D13`) | **0 hard / 0 soft** matches |
| upstream inputs | the survey found **0** `sorry`/`admit`/`axiom`-keyword declarations in every quoted upstream file; the transcriptions carry no upstream axiom |

## 7. Semantic classification

| declaration group | class | justification |
| --- | --- | --- |
| `heatKernelSpatial`, `heatSolution`, `solitonScale`, `metricLieDerivativeFlat`, `shrinkerGradientField`, `IsSolitonGeneratorEuclidean`, `IsGradientShrinkerPotentialEuclidean`, `RicciFlowData`, `ball`, `HasCurvatureBoundOnParabolicBall`, `IsKappaNoncollapsedOnScale`, `IsKappaCollapsedAt` | upstream source claim (definitions/structures, transcribed with file:line) | definitional; no statement is asserted true by fiat |
| `heatKernelSpatial_eq_gaussianKernel`, `heatSolution_eq_flatKernelConv`, `heatKernelSpatial_integral`, `solitonScale_eq_fflowMetricScale` | local proved theorem (definitional correspondence) | rfl-level identities between transcribed and local definitions |
| `heatSolution_approx_bound_at_of_bounded`, `heatSolution_tendsto_initial_of_bounded`, `heatSolution_tendsto_initial_joint_of_bounded` | upstream compiled theorem (locally re-verified) | upstream statement re-proved from D10 mass + D11 Gaussian tail lemmas (the upstream proof engine, `GaussianFourier.integral_rexp_neg_mul_sq_norm`, is available at the local mathlib rev but was not needed) |
| `hasDerivAt_integral_mul_hasCompactSupport` | upstream compiled theorem (locally re-verified **through the local D12 theorem**) | the local D12 `hasDerivAt_weightedIntegral_constWeight` is consumed to prove the upstream statement — downstream use of the D12 deliverable |
| `boundedContinuousClass` (finite measures), `boundedClass_cls_iff_integrableClass_cls_of_compactSpace_finiteMeasure`, `weakInitialConditionFor_boundedClass_iff_full_of_compact_finiteMeasure` | local proved theorem, expanded hypotheses `[CompactSpace X] [IsFiniteMeasure μ] [OpensMeasurableSpace X]` | boundedness from compactness (`IsCompact.exists_bound_of_continuousOn` on `univ`), integrability from boundedness + finite measure (`BoundedContinuousFunction.integrable`); hypotheses are expanded and automatic in the compact-manifold scope |
| `heatSolution_tendsto_initial_of_integrable` | local proved theorem (general, all `n`) | re-typing of the D11 weak initial condition through the solution identity |
| `shrinkerGradientField_isGradient`, `fderiv_shrinkerGrad`, `metricLieDerivativeFlat_shrinkerGrad`, `shrinkerFpot_isGradientShrinkerPotentialEuclidean`, `shrinkerGrad_isSolitonGeneratorEuclidean`, `shrinkerFpot_GSS_and_solitonGenerator`, `heatKernelSpatial_contDiff_compat`, `heatKernelSpatial_bound_compat` | model theorems (explicit flat Gaussian model, `τ > 0`) | nontrivial: the D12 Hessian identity `iteratedFDeriv_two_shrinkerFpot` and the D12 F-derivative identity `hasFDerivAt_shrinkerFpot` are consumed |
| `isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean` | conditional adapter | typed implication with the upstream Lie-derivative identity `hgradLie` exposed (it is a *theorem* upstream, Soliton.lean:124); discharged on the model by the computation above |
| `isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate` | conditional adapter | typed implication; translation hypotheses `hcurv` (curvature predicate → upstream parabolic bound), `hvol` (upstream ball volume ≤ measure of the containing local closed ball — an *upper* comparison, not the κ-lower-bound conclusion), plus domain/scale alignment `t₀ < T`, `r₀ < ρ`, `ρ² ≤ t₀`; justified by the upstream `induced_distance` field (SmoothRicciFlow.lean:236) |

## 8. Objective blockers A1 / A2 / A3 / P1 / P5 — exact accounting

| blocker | D13 action | status after D13 |
| --- | --- | --- |
| **A1** (overstrong `1 < c` in `perelmanF_step_lt`, `gibbsTerm_strictAnti`, `gibbsTerm_step_lt`) | fresh compile-check of the corrected theorems `perelmanF_step_le` (Discrete.lean:48), `gibbsTerm_antitone` (Gibbs.lean:76), `gibbsTerm_step_le` (Gibbs.lean:158) — all with the sharp `1 ≤ c` hypothesis, `lake env lean` exit 0 each. Upstream restatement: the snapshot has **no** corresponding theorem (no entropy content upstream — §3 survey), so there is nothing to restate against; the corrected local theorems remain the restatement. | open (verified-corrected); restatement recorded |
| **A2** (sign convention: released toy functional nonincreasing vs Perelman's increasing F) | adapter evidence: the upstream shrinking-soliton scale `solitonScale λ t = 1 - 2λt` with `λ > 0` (Soliton.lean:239) equals the local F-flow scale `fflowMetricScale` at `λ = 1/(2τ₀)` (`solitonScale_eq_fflowMetricScale`), and the (GSS) equation holds on the shrinker model — the geometric sign conventions agree; the local corrected convention (increasing Perelman F, derivative `= +FDissipation`) is recorded in D12 `SignDistinction` and remains the target convention for any future upstream F/W layer (which does not exist yet). | documented (unchanged); convention alignment recorded |
| **A3** (adversarial audit only covers D4; D2/D3 have no counterexample search) | D13 contributes the upstream-side hygiene evidence (0 sorry/admit/axiom in every quoted upstream file; 36/36 local adapter declarations in the approved cone; fail-closed negative control) but does **not** replace the D2/D3 adversarial audit. | **open** — owned by `VERIFIER-D7-adversarial-audit-d2d3` |
| **P1** (stale shared queue.json) | mirrored proposal `longrun/queue.updated.json` (D13 marked `complete-with-delivery-note` pending acceptance; the shared `longrun/queue.json` is outside the `workspace-write` sandbox — same delivery pattern as D6). | resolved-in-worktree; integrator promotion pending |
| **P5** (release-source delta must be re-hashed on every release) | fresh hash re-check performed: promoted D1–D4 sources (`Longrun/`, `Stage1/`, `Stage6/`, `Basic.lean`) byte-identical to the D12 scaffold source; the D6 drivers (`D6AuditReport.lean`, `D6LedgerProbe.lean`, `ReleaseAudit.lean`, `ReleaseCheck.lean`, `ReleaseClaims.lean`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) byte-identical to `D6_weekly_release/release`. The D13 delta is exactly the new `Poincare/D13/UpstreamAdapter/` module set (6 files, hashes in §9). | check re-run successfully for this release (PASS) |

## 9. Source hashes (fresh, sha256)

| file | sha256 |
| --- | --- |
| `release/Poincare/D13/UpstreamAdapter/EvansHeat.lean` | `76879ce72056cd094a9ef32154245ed97c3af2c18b206a7ce75ded7b557d9a03` |
| `release/Poincare/D13/UpstreamAdapter/EvansParametric.lean` | `0428553e8fe67adb6b86ed79c6f4e1409ee0d3cf9e36cfa4bdd3ba513e9b3e72` |
| `release/Poincare/D13/UpstreamAdapter/MorganTianShrinker.lean` | `1b0d72481d9bb4d08e91d8cc51504ad32b7da415950c6eba5e5c6d0e02fdd427` |
| `release/Poincare/D13/UpstreamAdapter/KleinerLottKappa.lean` | `747dd56dd70b9a6d70f8a82f1bd634247050d0f137257c03f4ea6eb4213f28df` |
| `release/Poincare/D13/UpstreamAdapter/All.lean` | `f967b9be2ef866306f4fed882bbe24fa03657fca42020e8b35dcc603013342cb` |
| `release/Poincare/D13/UpstreamAdapter/Audit.lean` | `46b84ada8dc83f7d07af62dfa8305bddc48c6e9225f73c4e286e27450e1dfd06` |

No D7/D8/D9/D10/D11/D12 source was modified (only the six files under `release/Poincare/D13/UpstreamAdapter/` are new; the copied D7–D12 modules are byte-identical to their three source worktrees, `diff -rq` clean).

## 10. Remaining blockers and next dependency requests

**Remaining (none closed by this task):** A1 (restatement recorded, remains open), A2 (documented), A3 (open), P1 (integrator promotion), P5 (per-release check), plus the D7/D12 mathematical inputs listed below.

**next_dependency_requests** (machine-readable in the JSON card):
1. Upstream build of `shared` + `Evans` + `KleinerLott` + `MorganTian` packages with `leanprover/lean4:v4.32.1` + mathlib `520045ab…` (network verified reachable; full mathlib build ≈ stretch beyond this invocation) — would upgrade the "upstream source claim" rows of §4 to upstream compiled theorems.
2. An upstream (KleinerLott or new) **proved** κ-noncollapsing theorem (predicate ⇒ volume lower bound), or the local discharge of the adapter's `hvol`/`hcurv` hypotheses from `SmoothCompleteRicciFlowOn` (needs the upstream manifold build first).
3. F/W entropy, reduced distance/volume and L-geodesics upstream: none exists; the local D12 EntropyVariation/KappaVariational results are currently the only formalized content and should seed an upstream chapter (CaoZhu `CZ04_ReducedVolume.tex` is the blueprint target).
4. Local KV-1/KV-3 (path-space compactness, minimizer regularity) can reuse KleinerLott `HasRadialDistancePathsOn`/`HasAlmostRadialDistancePathsOn` (PointSelection.lean:299/317) and MorganTian Ch01/Ch02 minimizing-geodesic theorems once the upstream build exists.
5. General Euclidean identity `L_(grad f) g = 2 Hess f` (discharging `hgradLie` in general, upgrading the shrinker computation to a general theorem; needs the second-derivative symmetry lemma on `ContDiff` functions).

TASK_DONE — card: `longrun/results/D13-upstream-adapter-audit.md` (this file); machine-readable twin: `longrun/results/D13-upstream-adapter-audit.json`. This card requests independent acceptance of the adapter plan + compatibility module only; it does not claim Perelman, does not claim any of A1/A2/A3/P1/P5 is closed by this task, and does not count upstream sources as local proof evidence.
