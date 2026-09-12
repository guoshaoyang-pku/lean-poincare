# D13-topping-ricci-adapter-plan — result card

- **Task id:** `D13-topping-ricci-adapter-plan`
- **Stage / lane:** D13 / coordination+integration (`coordination: true`)
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-topping-ricci-adapter-plan`
- **Model:** `deepseek-v4-pro` (configured preset; never switched)
- **Generated (UTC):** 2026-09-10T20:00:00Z (elapsed ≈ 3.4 h of the 4 h invocation)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (binary `Lean 4.34.0-rc2, commit 6a10ac8c22be`); mathlib `7974e751bece493b6ff508039423ca9fa2452fa8` (pinned by `lake-manifest.json`, inherited from the accepted D12 scaffold)
- **Upstream snapshot:** `third_party/frenzymath/Poincare-Conjecture` = `frenzymath/Poincare-Conjecture` @ `bb91a091f0b968f8bbe8d861e025a88d82b161be` (Apache-2.0; reference-only; toolchain `leanprover/lean4:v4.32.1`, mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6`; not built locally, per `docs/UPSTREAM-INTEGRATION.md`)
- **Verdict:** **TASK_DONE for the D13 milestone** — a precise, compile-checked adapter plan and a small Lean compatibility module (`Poincare.D13.ToppingAdapter`, 7 files, 50 audited declarations, 1723 lines) mapping the local D12 objectives to the upstream **Topping** package for the objective blockers **U6 / U7 / U8 / I2** are delivered, kernel-checked and axiom-audited. **No objective blocker is claimed closed** (see §8); each is accounted for with fresh evidence. This card requests independent acceptance of the adapter plan + compatibility module only and claims nothing about Perelman.

---

## 1. What was built

| file | lines | role |
| --- | --- | --- |
| `Core.lean` | 476 | **verbatim transcription, locally re-verified** of the compact-space weak maximum principle, `Topping/Topping/MaximumPrinciple/Core.lean` (10 theorems, upstream file:line cited), plus the local expanded-hypothesis variant `nonpos_of_forall_isMax_time_deriv_le_of_pos'` (time differentiability only at positive times) |
| `Slab.lean` | 306 | the **I2 adapter**: second-derivative test at a local maximum + the continuous heat weak maximum principle on `[a,b] × [0,T]` for classical solutions (`SlabRegularity` expanded hypotheses), proved via the transcribed Topping core |
| `Scalar.lean` | 372 | **verbatim transcription, locally re-verified** of `Topping/ParabolicPDE/Scalar.lean` (`heatCoefficients` uniformly parabolic, symbol covariance) + the **U6/U8 symbol-level correspondence** with the local D9 `flowSymbol`/`laplacianSymbol` |
| `ShortTime.lean` | 215 | the **U8 mapping**: upstream source claims (Topping Ch. 5 split interface, MorganTian DeTurck-Picard, `canonicalRicciDeTurckStrictParabolic`) + closed local theorems `shortTimeRicciFlow_of_splitInputs` (the upstream assembly over the local D7 abstraction) and `localDeTurckStrictParabolic` (the upstream coercivity certificate on the flat model) |
| `Volume.lean` | 133 | the **U7 mapping**: upstream source claims (volume derivative, volume density, tensor divergences) + `hasVolumeDerivativeOn_of_weightedDensity_local`, the upstream volume-evolution theorem re-proved **through the local D12 theorem** `hasDerivAt_weightedIntegral_constWeight` |
| `All.lean` | 41 | umbrella |
| `Audit.lean` | 180 | 50 `#print axioms` + fail-closed `Lean.collectAxioms` gate |

Namespace: `Poincare.D13.ToppingAdapter.{Core,Slab,Scalar,ShortTime,Volume}`. Dependencies: local D2/D7/D9/D12 modules (copied byte-identical from the accepted D12 scaffold, `diff -rq` clean) + mathlib. No upstream Lean file was copied into the local package: the upstream statements are transcribed with file:line citations and re-proved locally (Core, Scalar), recorded as upstream source claims (ShortTime, Volume), or assembled through the local layers.

## 2. Classification policy (per `docs/UPSTREAM-INTEGRATION.md`)

* **upstream compiled theorem, locally re-verified** — the transcribed Topping statements with their upstream proof bodies, kernel-checked by the local build;
* **upstream source claim** — an upstream declaration recorded with exact file:line, not re-verified here (needs the upstream manifold build at Lean 4.32.1);
* **local proved theorem, expanded hypotheses** — proved from local layers + mathlib, with every added hypothesis expanded and justified;
* **conditional adapter** — a locally proved typed implication whose antecedents are the split inputs, never the conclusion.

No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, fake proposition, weakened conclusion, or hypothesis equivalent to the conclusion occurs in the module set (fail-closed audit §6, token scan §6).

## 3. The adapter plan: exact mappings (upstream file:line → local declaration)

Line numbers verified against the pinned snapshot. The D12 objectives mapped: `D12-heat-domain-repair` (module `Poincare.D12.HeatDomain`), `D12-heat-semigroup-analysis` (`Poincare.D12.HeatSemigroup`), `D12-parabolic-local-existence` (`Poincare.D12.ParabolicLocal`), `D12-entropy-variation` (`Poincare.D12.EntropyVariation`), `D12-kappa-variational` (`Poincare.D12.KappaVariational`).

### 3.1 Blocker I2 — continuous parabolic maximum principle

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `Topping.time_deriv_nonneg_of_isMaxOn_Icc`, `nonpos_of_forall_isMax_time_deriv_le_of_pos`, `nonpos_of_forall_isMax_time_deriv_le`, `exists_nonneg_reaction_bound_on_rectangle`, `exists_common_value_interval`, `le_ode_solution_of_forall_isMax_time_deriv_le_of_pos`/`_le`, `nonneg_of_forall_isMin_time_deriv_ge` (`Topping/MaximumPrinciple/Core.lean:28/53/159/176/200/240/292/314`) | theorem (closed) | D2 `ContinuousHeatMaximumPrincipleInterface` (`Poincare.Longrun.PDE.ContinuousInterface`), D7 `ContinuousHeatMaximumPrincipleConjecture` (`D7/Limit/Blocked.lean:54`) | **transcribed verbatim + locally re-verified** (`Core.lean`); the local variant `nonpos_of_forall_isMax_time_deriv_le_of_pos'` matches the D2 time-derivative domain (`Ioo 0 T` only) |
| `Core` machinery + second-derivative test | — | `Slab.continuousHeatMaximumPrinciple_of_topping` — for every `u` with the D2 `ContinuousHeatHypotheses` **and** the expanded `SlabRegularity` (C¹-in-time, C²-in-space `HasDerivAt` at interior points) and `a ≤ b`, the D2 conclusion `∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, u x t ≤ 0` holds | **local proved theorem, expanded hypotheses** (`Slab.lean`) — the mathematical content of I2 for classical solutions, proved by the upstream Topping argument + `deriv_deriv_nonpos_of_isLocalMax`; the literal D2/D7 statement (without the regularity package) remains statement-only |

### 3.2 Blocker U6 — heat-equation theory / parabolic PDE layer

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `Topping.ParabolicPDE.ScalarSecondOrderCoefficients`, `euclideanNormSq`, `symbol`, `principalSymbol`, `IsPositiveDefinite`, `PointwiseParabolic`, `UniformlyParabolic` (`Topping/ParabolicPDE/Scalar.lean:13/72/76/80/86/91/96`) | defs | D12 `ParabolicLocal` Duhamel/symbol layer, D9 `flowSymbol` | transcribed verbatim |
| `pointwiseParabolic_iff_symbol_positive`, `symbol_zero/add/smul/one`, `euclideanNormSq_nonneg/pos`, `uniformlyParabolic_pointwiseParabolic` (Scalar.lean:101/107/111/123/168/173/177/188) | theorem (closed) | — | transcribed verbatim, locally re-verified |
| `heatCoefficients`, `heatCoefficients_uniformlyParabolic`, `heatCoefficients_pointwiseParabolic` (Scalar.lean:198/210/217) | def + theorems (closed) | the D12 heat operator `heatOperator` (proved positivity/L∞-L¹ contraction/semigroup in `D12-heat-semigroup-analysis`); D9 `laplacianSymbol` | transcribed + re-verified; **`heatPrincipalSymbol_eq_localLaplacianCoeff`**: the upstream heat principal symbol equals the local D9 Laplacian coefficient `|ξ|²_g` on the flat model — the same symbol object |
| `symbol_congruence`, `IsPositiveDefinite.congruence` (Scalar.lean:231/252) | theorem (closed) | chart-transition law needed by the D12 parabolic layer | transcribed + re-verified |
| `laplaceBeltramiChartCoefficients_principalSymbol`, `laplacianAt_eq_laplaceBeltramiChart_applyJet` (`Topping/ParabolicPDE/LaplaceBeltrami.lean:56/285`); `hasCurvatureEvolutionOn_iff_heat_type` (`Topping/RicciFlow/Evolution.lean:76`) | theorem (closed) | D11 `laplacianLinearMap`; D7 `TensorLaplacian` | recorded as upstream source claims (manifold level; needs upstream build) |
| remaining `ParabolicPDE/` (66 files: Hölder spaces, Schauder, Picard solvers) | theorems/defs, closed where stated; `SchauderEstimateContract` takes the estimate as input | D12 `mildToClassicalBridge` / `derivativeLossBarrier` (named obligations) | recorded as upstream source claims; the upstream Schauder layer is likewise conditional on the estimate contract |

### 3.3 Blocker U7 — volume form / divergence / IBP / Bochner

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `HasVolumeDerivativeOn` (`Topping/MaximumPrinciple/Volume.lean:59`), `hasVolumeDerivativeOn_of_weightedDensity` (:76), `hasDerivWithinAt_integral_of_dominated_of_derivWithin_le` (:130), `derivWithin_volume_nonpos_of_scalarCurvature_nonneg` (:235), `volume_antitoneOn_of_scalarCurvature_initial_nonneg` (:259) | def + theorems (closed) | D12 `hasDerivAt_weightedIntegral`/`_constWeight` (`EntropyVariation/WeightedIntegral.lean:58/83`) | **`Volume.hasVolumeDerivativeOn_of_weightedDensity_local`**: the upstream volume-evolution theorem re-proved **through the local D12 theorem** — downstream use of the D12 deliverable in the upstream statement's form |
| `chartVolumeDensityAt` / `selfChartVolumeDensityAt` (`Topping/Riemannian/Variation.lean:212/219`) | defs | D7 `Volume` interfaces (statement-only) | recorded as upstream source claims |
| `divergence_ricciTensorField` (`Topping/Riemannian/VariationScalar.lean:173`), `divergence_differentialOneForm` (:262) | theorem (closed) | D7 `Divergence`/`Bochner` (statement-only) | recorded as upstream source claims — the divergence-of-tensor identities (contracted Bianchi, `div(df) = Δf`); **the global divergence theorem, IBP and the Bochner formula are absent upstream too** (0 hits in the snapshot survey), so U7's IBP half stays open on both sides |

### 3.4 Blocker U8 — Hamilton short-time existence

| upstream declaration (snapshot file:line) | kind upstream | local counterpart | adapter status |
| --- | --- | --- | --- |
| `Topping.exists_localRicciFlow_of_splitHamiltonGauge` (`Topping/RicciFlow/Existence/ShortTimeExistence.lean:34`), `isRicciFlowOn_of_splitHamiltonGauge` (:45) | theorem (closed assembly; antecedents `RicciDeTurckLocalSolution`/`HamiltonGaugeTransport` assert no existence, `LocalExistence.lean:9-12`) | D7 `DeTurckShortTimeExistence` / `DeTurckToRicciConversion` (statement-only Props, `D7/ShortTime/Statements.lean:98/110`) | recorded as upstream source claim; **`ShortTime.shortTimeRicciFlow_of_splitInputs`** — the same closed assembly proved over the local D7 abstraction (conditional adapter; the antecedents are the split inputs, not the conclusion) |
| `MorganTianLib.RicciDeTurckStrictParabolic`, `canonicalRicciDeTurckStrictParabolic` (`MorganTian/MorganTianLib/Ch03/RicciFlow/PDE/LocalExistence.lean:42/50`) | structure + theorem (closed) | D9 `flowSymbol`: `σ(-2Ric + L_W g) = -|ξ|²·Id` (`D9/DeTurck/SymbolModel.lean:200`) | **`Scalar.flowSymbol_eq_neg_heatPrincipalSymbol`** and **`ShortTime.localDeTurckStrictParabolic`** — the upstream coercivity certificate in local terms (sign conventions matched) |
| `MorganTianLib.exists_ricciDeTurckLocalSolution_of_picard` / `exists_classicalOutput` (`…/PDE/DeTurckPicard.lean:223/237`) | theorem (closed from a `RicciDeTurckPicardModel`) | D12 `existsUnique_heatMildSolution` (Banach contraction on BUC; `D12-parabolic-local-existence`), D9 strict parabolicity | recorded as upstream source claim — **no upstream declaration produces a Picard model from an arbitrary metric**; U8 stays open on both sides, with the identical split architecture |

## 4. Upstream source claims recorded (not re-verified locally)

| upstream declaration | file:line | reason |
| --- | --- | --- |
| Topping Ch. 5 split interface + MorganTian LocalExistence/DeTurckPicard (§3.4) | as above | need the upstream manifold build (`RiemannianMetric I M`, `SmoothVectorField`, mathlib 4.32.1 rev) |
| Topping volume-derivative/volume-density/divergence theorems (§3.3) | as above | same; the analytic half is re-proved locally through D12 |
| Topping LaplaceBeltrami + curvature-evolution heat-type theorems (§3.2) | as above | same |
| Topping `Scalar.lean` exponential-conjugation jet block (`conjugatedScalarOperator_eq_quadratic_plus_lower`, Scalar.lean:265ff) | as above | not needed by the mapped D12 objectives; mechanical transcription deferred |

**Decisive survey findings (this task):** the Topping package (184 files) has **no** sorry/admit/axiom declarations (the 5 keyword hits are docstring text); it has **no** Perelman entropy/reduced-volume/κ content (as in the sibling D13 survey); its short-time existence is **split** exactly like the local D7/D12 layer; and its maximum-principle core is fully proved.

## 5. Compile evidence

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
WT=/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-topping-ricci-adapter-plan
cd "$WT/release"
lake build Poincare.D13.ToppingAdapter.Audit   # exit 0, "Build completed successfully (8912 jobs)"
for f in Core Slab Scalar ShortTime Volume Audit; do
  lake env lean "Poincare/D13/ToppingAdapter/$f.lean"   # 6/6 exit 0
done
```

Per-file logs: `tmp/lean-{Core,Slab,Scalar,ShortTime,Volume,Audit}.log` (each exit 0; build log `tmp/build-Audit.log`). The local D2/D7/D9/D12 dependency closure (8912 jobs) was rebuilt fresh from the accepted D12 scaffold sources (byte-identical copy, `diff -rq` clean against `D13-upstream-adapter-audit/release`).

## 6. Axiom evidence (kernel trust, separate from compilation)

| item | value |
| --- | --- |
| audited declarations | **50 / 50** — all depend only on `[propext, Classical.choice, Quot.sound]` |
| gate result | `D13ToppingAdapterAxiomCheck: PASS — all 50 declarations … depend only on [propext, Classical.choice, Quot.sound]` (build log) |
| fail-closed negative control | `/tmp/d13neg/NegativeAudit.lean` (axiom `d13AuditFakeAxiom` + dependent theorem): the same gate logic throws `detected unapproved axioms [d13AuditFakeAxiom]`, exit 1 |
| forbidden tokens (comment/string-aware `input/d5-tools/scan_forbidden.py` over `release/Poincare/D13/ToppingAdapter`) | **0 hard / 0 soft** matches (7 files) |
| upstream inputs | the quoted upstream files carry 0 `sorry`/`admit`/`axiom` declarations; the transcriptions import no upstream axiom |

## 7. Semantic classification

| declaration group | class | justification |
| --- | --- | --- |
| `Core.*` (10 transcribed Topping maximum-principle theorems) | upstream compiled theorem, locally re-verified | upstream proof bodies kernel-checked by the local build; upstream file:line cited |
| `Core.nonpos_of_forall_isMax_time_deriv_le_of_pos'` | local proved theorem, expanded hypotheses | upstream proof with the time-differentiability hypothesis restricted to positive times (the D2 interface provides `deriv` only in `Ioo 0 T`) — a weakening of a hypothesis, not of the conclusion |
| `Slab.deriv_deriv_nonpos_of_isLocalMax`, `iteratedDeriv_two_nonpos_of_isLocalMax` | local proved theorem | second-derivative test (Fermat + slope limit + convex mean-value growth) |
| `Slab.SlabRegularity` | expanded-hypothesis package (def) | C¹-time / C²-space regularity of the classical weak maximum principle; strictly not equivalent to the conclusion |
| `Slab.slab_nonpos_of_lt`, `Slab.continuousHeatMaximumPrinciple_of_topping` | local proved theorem, expanded hypotheses | the D2 conclusion from `ContinuousHeatHypotheses` + `SlabRegularity` + `a ≤ b` via the transcribed Topping core |
| `Scalar.*` (definitions + 13 transcribed theorems) | upstream compiled theorem / definition, locally re-verified | verbatim transcription |
| `Scalar.euclideanMetricData`, `covectorOf`, `covectorNormSq_euclidean_eq_euclideanNormSq`, `heatPrincipalSymbol_eq_localLaplacianCoeff`, `flowSymbol_eq_neg_heatPrincipalSymbol` | local proved theorem (adapter) | flat-model correspondence between the upstream scalar layer and the local D9 symbol layer |
| `ShortTime.SplitShortTimeInputs`, `shortTimeRicciFlow_of_splitInputs` | conditional adapter | typed implication with the two split antecedents (D7 `DeTurckShortTimeExistence` + `DeTurckToRicciConversion`), exactly mirroring the upstream Topping theorem |
| `ShortTime.bilinPairing`, `bilinPairing_pos_of_ne_zero`, `localDeTurckStrictParabolic`, `deTurckLinearisationSymbol_strictParabolic_heatCoefficients` | local proved theorem (adapter) | the upstream `canonicalRicciDeTurckStrictParabolic` coercivity in local terms, via D9 `flowSymbol` |
| `Volume.HasVolumeDerivativeOn`, `hasVolumeDerivativeOn_of_weightedDensity_local` | local proved theorem (adapter, downstream use of D12) | the upstream Volume.lean:76 theorem re-proved through the local D12 weighted-integral theorem |

## 8. Objective blockers U6 / U7 / U8 / I2 — exact accounting

| blocker | D13 action | status after D13 |
| --- | --- | --- |
| **I2** (ContinuousHeatMaximumPrincipleInterface statement-only) | the upstream Topping compact-space weak maximum principle is transcribed and locally re-verified; with the expanded `SlabRegularity` the D2 slab conclusion is now a **proved theorem** (`continuousHeatMaximumPrinciple_of_topping`). The *literal* D2/D7 statement (without the regularity package) remains statement-only, and the D7 discrete-to-continuous route is untouched. | **partially discharged — not closed.** The remaining gap is exact: the D2/D7 hypotheses record `deriv`/`iteratedDeriv 2` *values* (zero-fallback convention), which do not imply genuine differentiability; closing the literal interface requires adding the standard C¹/C² regularity to the hypothesis package (upstream restatement recommendation). |
| **U6** (heat/parabolic layer) | the Topping scalar parabolic layer (`heatCoefficients`, uniform parabolicity, symbol covariance) is transcribed and re-verified; the symbol-level correspondence with the local D12/D9 layer is proved. The manifold heat-kernel / Hölder-Schauder / LaplaceBeltrami theorems are recorded as upstream source claims (need the upstream build). | **open** (mapped, not closed). |
| **U7** (volume form / divergence / IBP / Bochner) | the upstream volume-evolution theorem is re-proved locally **through** the D12 weighted-integral theorem; the volume-density and tensor-divergence theorems recorded as upstream claims. | **open** (analytic half mapped; the divergence theorem / IBP / Bochner formula are absent upstream too). |
| **U8** (Hamilton short-time existence) | the upstream split architecture is transcribed at the local level (`shortTimeRicciFlow_of_splitInputs`, closed) and the strict-parabolicity certificate is proved on the flat model. The analytic antecedents (`RicciDeTurckPicardModel`-producer upstream; `DeTurckShortTimeExistence` locally) are missing on **both** sides. | **open** (mapped; split inputs remain antecedents). |

`exact_blockers_closed`: **none** (empty list — none of U6/U7/U8/I2 is fully closed by this task; I2 is partially discharged, recorded above).

## 9. Source hashes (fresh, sha256)

| file | sha256 |
| --- | --- |
| `release/Poincare/D13/ToppingAdapter/All.lean` | `a4fa5411b70edf258dfd3606342b9327b4d6cf6279fedd11f1c4d17748f0095a` |
| `release/Poincare/D13/ToppingAdapter/Audit.lean` | `76e1c0f6a2a83c80c12acace43da2fdcde6853590f7ee33091fddc2412e30240` |
| `release/Poincare/D13/ToppingAdapter/Core.lean` | `50e2666111c7919eaf87fe916ae0bc3714b1408fb647ebd3c4727bd3c5eeab4a` |
| `release/Poincare/D13/ToppingAdapter/Scalar.lean` | `c1349b814f6238f10efdd5ce6d2c358cad4fc327c6cc46a9ae4b0b4a643a28ee` |
| `release/Poincare/D13/ToppingAdapter/ShortTime.lean` | `2a8a78b724cf655c003b7cf69c701e2b934aec4297f2261abdbb19c25539c369` |
| `release/Poincare/D13/ToppingAdapter/Slab.lean` | `f0d3b7fff0fe90ba835f25749d26ea671835e4d634c6388064b602935e3a2c22` |
| `release/Poincare/D13/ToppingAdapter/Volume.lean` | `5aedda14dab635be8f923af21fa792dfe76bf6a2044f4cf59107ad46cc6d9531` |

No D2/D7/D9/D12 source was modified: only the seven files under `release/Poincare/D13/ToppingAdapter/` are new; the copied D2–D13 sources are byte-identical to the accepted scaffold (`diff -rq` clean against `D13-upstream-adapter-audit/release`).

## 10. Remaining blockers and next dependency requests

**Remaining:** U6, U7, U8 (open), I2 (partially discharged; literal D2/D7 statement still statement-only).

**next_dependency_requests** (machine-readable in the JSON card):
1. Upstream build of `DoCarmo` + `MorganTian` + `Topping` at `leanprover/lean4:v4.32.1` / mathlib `520045ab…` — upgrades the §4 upstream source claims to upstream compiled theorems.
2. Upstream restatement of the D2/D7 `ContinuousHeatHypotheses` package: add the C¹-time / C²-space `HasDerivAt` regularity (the `SlabRegularity` fields) so the *literal* interface becomes provable — the local theorem `continuousHeatMaximumPrinciple_of_topping` is then the direct closure of I2.
3. A producer of the analytic antecedent (`RicciDeTurckPicardModel` from an arbitrary metric upstream; `DeTurckShortTimeExistence` locally) — the missing half of U8 on both sides; the local D12 Banach-contraction mild solution and the D9 strict-parabolicity certificate are the designated building blocks.
4. Global divergence theorem / IBP / Bochner formula (absent in both the pinned mathlib and the snapshot): a local manifold-integration layer is the unblocked next step for U7 and the D7 `Divergence`/`Bochner` interfaces.
5. Full transcription of the remaining Topping `ParabolicPDE` layer (Hölder/Schauder/Picard) once the upstream build exists — the U6 parabolic half.

TASK_DONE — card: `longrun/results/D13-topping-ricci-adapter-plan.md` (this file); machine-readable twin: `longrun/results/D13-topping-ricci-adapter-plan.json`. This card requests independent acceptance of the adapter plan + compatibility module only; it does not claim Perelman, does not claim U6/U7/U8/I2 is closed by this task, and does not count upstream sources as local proof evidence.
