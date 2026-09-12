# Independent adversarial audit — three ophis-gpu D13 adapter-plan result cards

Auditor: independent cross-audit agent (read-only except this file).
Workspace: `/data/home/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-cross-audit-ophis-cards`.

Cards audited (paths below are relative to the workspace root):

1. `audit/ophis/D13-upstream-adapter-audit/longrun/results/D13-upstream-adapter-audit.md` (160 lines) + `.json`
2. `audit/ophis/D13-morgan-tian-adapter-plan/longrun/results/D13-morgan-tian-adapter-plan.md` (227 lines) + `.json`
3. `audit/ophis/D13-topping-ricci-adapter-plan/longrun/results/D13-topping-ricci-adapter-plan.md` (162 lines) + `.json`

Lean sources audited (paths relative to workspace root):

* card 1: `audit/ophis/D13-upstream-adapter-audit/release/Poincare/D13/UpstreamAdapter/{EvansHeat,EvansParametric,MorganTianShrinker,KleinerLottKappa,All,Audit}.lean` (6 files, 1129 lines — `wc -l` reproduces the card's count exactly)
* card 2: `audit/ophis/D13-morgan-tian-adapter-plan/release/Poincare/D13/MorganTianAdapter/{Curvature,Tensoriality,ExpGeodesic,LeviCivitaSmoothness,BishopGromov,All,Audit}.lean` (7 files, 1119 lines — matches)
* card 3: `audit/ophis/D13-topping-ricci-adapter-plan/release/Poincare/D13/ToppingAdapter/{Core,Slab,Scalar,ShortTime,Volume,All,Audit}.lean` (7 files, 1723 lines — matches)

## 0. Method and transport limitations

* **Third-party snapshot.** No `third_party/` directory exists under any of the three per-task trees (`find audit -maxdepth 4 -name third_party` → empty). However, the same frenzymath snapshot **is relayed at the workspace root**: `third_party/frenzymath/Poincare-Conjecture/` with `third_party/frenzymath/SOURCE.json` recording `commit bb91a091f0b968f8bbe8d861e025a88d82b161be`, matching all three cards. I therefore **verified upstream file:line citations directly against the snapshot**, rather than treating them as untestable. Result in §7 below: every cited upstream declaration exists; line numbers are exact except one off-by-one (§7).
* **Per-task `tmp/`** is not relayed in any of the three tasks; the cards cite `tmp/upstream-survey.md`, `tmp/morgan-tian-survey.md`, `tmp/lean-*.log`, `tmp/build-Audit.log` there. Any claim resting only on those files is marked "not relayed".
* **Pinned mathlib source** (`mathlib 7974e751…`) is not relayed; claims about mathlib docstrings/declarations are marked "undetermined from relayed snapshot" (corroborating copies do exist inside the relayed D7 layer, quoted below).
* **Per-task `negcontrol/NegativeControl.lean`** (relayed, 1868 bytes, identical in all three tasks) is a **D5-era generic** audit control containing `negControl_sorry` and `negControl_nativeDecide` (lines 25/27). It is *not* the D13 fail-closed control the cards name (`/tmp/d13neg/NegativeAudit.lean`, `/tmp/d13mtneg/NegativeAudit.lean`, axiom `d13AuditFakeAxiom`); those are not relayed.
* **Forbidden-token scan.** I re-ran the relayed scanner `audit/ophis/<task>/input/d5-tools/scan_forbidden.py` (comment/string-aware, regex `\bsorry\b|\baxiom\b|\bunsafe\b|\bnative_decide\b|\bproof_wanted\b|\bsorryAx\b|\badmit\b`; `implemented_by`/`extern` soft). Results in §5/§6/§8: **0 hard / 0 soft matches** in every case. No `file:line` is reportable because there are zero matches.
* **Source hashes.** All 20 sha256 values printed in the three cards' hash tables were recomputed with `sha256sum` and **all match exactly** (card 1 §9 lines 140–145; card 2 §9 lines 179–185; card 3 §9 lines 141–147).
* **Audit inventories.** Card 1 `#print axioms` lines = 36 and `d13UpstreamAdapterAuditedDeclarations.length` = 36 (Audit.lean:84–159). Card 2 = 50/50 (Audit.lean:68–171). Card 3 = 50/50 (Audit.lean:58–161). All counts match the cards.
* **Byte-identity claims.** `diff -rq` of `release/Poincare/D13/UpstreamAdapter` between the upstream-audit task and each of the two other tasks → clean. `diff -rq` of the copied `Poincare/{D7,D9,D10,D11,D12}` between the topping and upstream-audit releases → clean; `Poincare/{D7,D10,D11,D12}` between morgan-tian and topping → clean.

---

# 1. Card 1 — `D13-upstream-adapter-audit`

## 1.A Headline claims (verbatim, with `.md` line numbers)

C1.1 (line 10, Verdict): "**TASK_DONE for the D13 milestone** — a precise, compile-checked upstream-adapter plan and a small Lean compatibility module (`Poincare.D13.UpstreamAdapter`, 6 files, 36 audited declarations, 1129 lines) mapping all three local D12 objectives (EntropyVariation, HeatDomain, KappaVariational) to exact upstream modules/declarations are delivered, kernel-checked and axiom-audited. The objective blockers A1/A2/A3/P1/P5 are each accounted for with fresh evidence; **none is claimed closed by this task** (see §8). This card requests independent acceptance and claims nothing about Perelman."

C1.2 (lines 18–23, §1 table): "`EvansHeat.lean` | 457 | Evans Ch02 heat-kernel chain (definitions `heatKernelSpatial`/`heatSolution`, normalization, bounded initial-condition theorem re-proved locally, bounded test-function class as a D12 v1 `AdmissibleTestClass`, compact finite-measure equivalence)"; "`EvansParametric.lean` | 105 | upstream Evans `hasDerivAt_integral_mul_hasCompactSupport` re-proved **through** the local D12 `hasDerivAt_weightedIntegral_constWeight`"; "`MorganTianShrinker.lean` | 221 | MorganTian Ch03 (GSS)/soliton-generator/`solitonScale` equations in Euclidean transcription, satisfied by the local D12 Gaussian shrinker"; "`KleinerLottKappa.lean` | 140 | KleinerLott κ-noncollapsing predicates transcribed verbatim + conditional adapter to the local D3/D7 `KappaNoncollapsingCertificate`"; "`Audit.lean` | 178 | 36 `#print axioms` + fail-closed `Lean.collectAxioms` gate + 4 kernel-checked downstream-use examples".

C1.3 (line 37, §2): "No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, fake proposition, weakened conclusion, or hypothesis equivalent to the conclusion occurs in the module set (fail-closed audit §6)."

C1.4 (line 47, §3.1): upstream `EvansLib.hasDerivAt_integral_mul_hasCompactSupport` (`…/HeatIVP.lean:55`) "**re-proved locally through the local D12 theorem** (`EvansParametric.lean`) — downstream use of the local theorem in the upstream statement's exact form".

C1.5 (line 49, §3.1): "**Euclidean transcription proved on the model**: `shrinkerFpot_isGradientShrinkerPotentialEuclidean`, `shrinkerGrad_isSolitonGeneratorEuclidean`, `solitonScale_eq_fflowMetricScale` (`MorganTianShrinker.lean`)".

C1.6 (lines 56–61, §3.2): "**proved definitional identity** `heatKernelSpatial_eq_gaussianKernel`"; "**re-proved locally** (`heatKernelSpatial_integral`)"; "**proved identity** `heatSolution_eq_flatKernelConv` (t > 0)"; "**re-proved locally** (`heatSolution_tendsto_initial_of_bounded`, plus joint form) using D11 Gaussian tail lemmas + D10 mass"; "re-typed locally (`heatSolution_tendsto_initial_of_integrable`)"; "**`boundedContinuousClass` is admissible iff the measure is finite; on compact finite-measure spaces it equals the D12 integrable class and `WeakInitialConditionFor D (bounded class) ↔ D.FullInitialCondition`** (proved)".

C1.7 (line 67, §3.3): "**transcribed verbatim + conditional adapter** `isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate` (expanded translation hypotheses `hcurv`, `hvol`, domain/scale alignment)".

C1.8 (line 68, §3.3): "Gaussian reduced volume … | present only as Evans `heatKernelSpatial_integral`; nothing upstream is *called* reduced volume | D12 KappaVariational `gaussianReducedVolume_eq_one` | identity via the Evans theorem (rfl-transport)".

C1.9 (line 71, §3.3): "**Decisive negative (verified by the full-snapshot survey …):** the snapshot contains **no Lean declaration** for Perelman `F`/`W` entropy, reduced distance/length/volume, L-minimizers, or κ-noncollapsing theorems (0 grep hits for `WEntropy|Fentropy|ntropy|reducedVolume|reducedLength|L-length|IsLMinimizer` in every package; 0 `sorry`/`admit`/`axiom`-keyword in every quoted upstream file)."

C1.10 (lines 91–107, §5/§6): "`lake build Poincare.D13.UpstreamAdapter.All      # exit 0 — Build completed successfully (8909 jobs)`"; "6/6 exit 0"; "per-file logs … (each exit 0, 0 warnings)"; "audited declarations | **36 / 36** — all depend only on `[propext, Classical.choice, Quot.sound]`"; gate PASS string; "fail-closed negative control | `/tmp/d13neg/NegativeAudit.lean` (axiom `d13AuditFakeAxiom` + dependent theorem)"; "forbidden tokens … **0 hard / 0 soft** matches".

C1.11 (lines 116–124, §7): classification rows quoted in §1.C below.

C1.12 (lines 130–134, §8): A1 "open (verified-corrected); restatement recorded" with `perelmanF_step_le` (Discrete.lean:48), `gibbsTerm_antitone` (Gibbs.lean:76), `gibbsTerm_step_le` (Gibbs.lean:158) "all with the sharp `1 ≤ c` hypothesis"; A2 "documented (unchanged)"; A3 "**open** — owned by `VERIFIER-D7-adversarial-audit-d2d3`"; P1 "resolved-in-worktree; integrator promotion pending"; P5 "check re-run successfully for this release (PASS)".

C1.13 (line 160, close): "it does not claim Perelman, does not claim any of A1/A2/A3/P1/P5 is closed by this task, and does not count upstream sources as local proof evidence."

## 1.B Declaration census (full signatures; file paths under `audit/ophis/D13-upstream-adapter-audit/release/Poincare/D13/UpstreamAdapter/`)

Every declaration named in card 1 exists. No F-finding for a missing local declaration name.

`EvansHeat.lean`:
* `heatKernelSpatial` — declared 51:
  `noncomputable def heatKernelSpatial (n : ℕ) (t : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=`
* `heatSolution` — 58: `noncomputable def heatSolution (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) : EuclideanSpace ℝ (Fin n) → ℝ → ℝ :=`
* `heatKernelSpatial_eq_gaussianKernel` — 67: `theorem … (n : ℕ) (t : ℝ) : heatKernelSpatial n t = Poincare.D10.HeatKernelEuclidean.gaussianKernel n t := rfl`
* `integrable_heatKernelSpatial` — 74: `lemma … (n : ℕ) {t : ℝ} (ht : 0 < t) : Integrable (heatKernelSpatial n t) := by`
* `heatKernelSpatial_integral` — 85: `theorem … (n : ℕ) {t : ℝ} (ht : 0 < t) : ∫ x, heatKernelSpatial n t x = 1 := by`
* `heatSolution_eq_convolution` — 121: `lemma … (n : ℕ) (g : …) (x : …) (t : ℝ) : heatSolution n g x t = ∫ z, heatKernelSpatial n t z * g (x - z) := by`
* `heatSolution_eq_flatKernelConv` — 134: `theorem … (n : ℕ) (g : …) (x : …) {t : ℝ} (ht : 0 < t) : heatSolution n g x t = ∫ y, Poincare.D11.HeatKernelBridge.flatKernel n x y t * g y := by`
* `heatSolution_approx_bound_at_of_bounded` — 150: `lemma … {n : ℕ} {g : …} (hg : Continuous g) {M η δ : ℝ} (hM : ∀ y, |g y| ≤ M) (hη : 0 ≤ η) {x₀ : …} (hosc : ∀ y, ‖y - x₀‖ < δ → |g y - g x₀| ≤ η) {t : ℝ} (ht : 0 < t) {x : …} (hx : ‖x - x₀‖ < δ / 2) : |heatSolution n g x t - g x₀| ≤ η + 2 * M * ∫ z in (Metric.ball (0 : …) (δ / 2))ᶜ, heatKernelSpatial n t z := by`
* `heatSolution_tendsto_initial_of_bounded` — 271: `theorem … (n : ℕ) {g : …} (hg : Continuous g) {M : ℝ} (hM : ∀ y, |g y| ≤ M) (x₀ : …) : Tendsto (fun t => heatSolution n g x₀ t) (𝓝[>] (0 : ℝ)) (𝓝 (g x₀)) := by`
* `heatSolution_tendsto_initial_joint_of_bounded` — 320: same hypotheses; conclusion `Tendsto (fun p : … × ℝ => heatSolution n g p.1 p.2) (𝓝 x₀ ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (g x₀)) := by`
* `boundedContinuousClass` — 375: `def … (X : Type*) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] : Poincare.D12.HeatDomain.AdmissibleTestClass X μ where`
* `boundedClass_cls_iff_integrableClass_cls_of_compactSpace_finiteMeasure` — 400: `theorem … {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ} : (boundedContinuousClass X μ).cls f ↔ (Poincare.D12.HeatDomain.AdmissibleTestClass.continuousIntegrableClass μ).cls f := by`
* `weakInitialConditionFor_boundedClass_iff_full_of_compact_finiteMeasure` — 421: `theorem … {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {D : Poincare.D11.HeatKernelBridge.HeatKernelCore X} [IsFiniteMeasure D.volume] : Poincare.D12.HeatDomain.WeakInitialConditionFor D (boundedContinuousClass X D.volume) ↔ D.FullInitialCondition := by`
* `heatSolution_tendsto_initial_of_integrable` — 446: `theorem … (n : ℕ) (x : …) {f : …} (hf : Continuous f) (hfi : Integrable f volume) : Tendsto (fun t : ℝ => heatSolution n f x t) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by`
* `heatKernelSpatial_contDiff_compat` — 92: `lemma … (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (heatKernelSpatial n 1) := by`
* `heatKernelSpatial_bound_compat` — 105: `lemma … (n : ℕ) : ∃ M : ℝ, ∀ y : …, |heatKernelSpatial n 1 y| ≤ M := by`

`EvansParametric.lean`:
* `hasDerivAt_integral_mul_hasCompactSupport` — 48: `lemma … {n : ℕ} {g : …} (hg : Continuous g) (hgc : HasCompactSupport g) {K K' : ℝ → … → ℝ} {U : Set ℝ} (hU : IsOpen U) {s₀ : ℝ} (hs₀ : s₀ ∈ U) (hKcont : ∀ s ∈ U, Continuous (fun y => K s y)) (hK'cont : ContinuousOn (fun p : ℝ × … => K' p.1 p.2) (U ×ˢ Set.univ)) (hderiv : ∀ s ∈ U, ∀ y, HasDerivAt (fun s => K s y) (K' s y) s) : HasDerivAt (fun s => ∫ y, K s y * g y) (∫ y, K' s₀ y * g y) s₀ := by` (body calls `Poincare.D12.EntropyVariation.hasDerivAt_weightedIntegral_constWeight` at line 98 — verified).

`MorganTianShrinker.lean`:
* `solitonScale` — 56: `def solitonScale (lambda t : ℝ) : ℝ :=`
* `metricLieDerivativeFlat` — 62: `noncomputable def … {n : ℕ} (X : Euc n → Euc n) (x v w : Euc n) : ℝ :=`
* `shrinkerGradientField` — 71: `noncomputable def … (n : ℕ) (τ : ℝ) : Euc n → Euc n :=`
* `IsSolitonGeneratorEuclidean` — 77: `noncomputable def … (n : ℕ) (X : Euc n → Euc n) (lambda : ℝ) : Prop :=` (body: `∀ x v w, -(0 : ℝ) = (1 / 2 : ℝ) * metricLieDerivativeFlat X x v w - lambda * ⟪v, w⟫_ℝ`)
* `IsGradientShrinkerPotentialEuclidean` — 85: `noncomputable def … (n : ℕ) (f : Euc n → ℝ) (lambda : ℝ) : Prop :=` (body: `ContDiff ℝ (⊤ : ℕ∞) f ∧ 0 < lambda ∧ ∀ x v w, -(0 : ℝ) = iteratedFDeriv ℝ 2 f x ![v, w] - lambda * ⟪v, w⟫_ℝ`)
* `solitonScale_eq_fflowMetricScale` — 96: `theorem … (τ₀ t : ℝ) : solitonScale (1 / (2 * τ₀)) t = Poincare.D12.EntropyVariation.fflowMetricScale τ₀ t := by`
* `shrinkerGradientField_isGradient` — 108: `theorem … (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (x w : Euc n) : ⟪shrinkerGradientField n τ x, w⟫_ℝ = fderiv ℝ (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) x w := by`
* `fderiv_shrinkerGrad` — 120: `theorem … (n : ℕ) {τ : ℝ} : fderiv ℝ (fun x : Euc n => (1 / (2 * τ)) • x) = fun _ : Euc n => (1 / (2 * τ)) • (ContinuousLinearMap.id ℝ (Euc n)) := by`
* `metricLieDerivativeFlat_shrinkerGrad` — 132: `theorem … (n : ℕ) {τ : ℝ} (hτ : τ ≠ 0) (x v w : Euc n) : metricLieDerivativeFlat (shrinkerGradientField n τ) x v w = (1 / τ) * ⟪v, w⟫_ℝ := by`
* `shrinkerFpot_isGradientShrinkerPotentialEuclidean` — 150: `theorem … (n : ℕ) {τ : ℝ} (hτ : 0 < τ) : IsGradientShrinkerPotentialEuclidean n (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) (1 / (2 * τ)) := by`
* `shrinkerGrad_isSolitonGeneratorEuclidean` — 167: `theorem … (n : ℕ) {τ : ℝ} (hτ : 0 < τ) : IsSolitonGeneratorEuclidean n (shrinkerGradientField n τ) (1 / (2 * τ)) := by`
* `isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean` — 188: `theorem … {n : ℕ} {X : Euc n → Euc n} {f : Euc n → ℝ} {lambda : ℝ} (hgradLie : ∀ x v w, metricLieDerivativeFlat X x v w = 2 * iteratedFDeriv ℝ 2 f x ![v, w]) (h : IsGradientShrinkerPotentialEuclidean n f lambda) : IsSolitonGeneratorEuclidean n X lambda := by`
* `shrinkerFpot_GSS_and_solitonGenerator` — 203: `theorem … (n : ℕ) {τ : ℝ} (hτ : 0 < τ) : IsGradientShrinkerPotentialEuclidean n (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) (1 / (2 * τ)) ∧ IsSolitonGeneratorEuclidean n (shrinkerGradientField n τ) (1 / (2 * τ)) := by`

`KleinerLottKappa.lean`:
* `RicciFlowData` — 53: `structure RicciFlowData (M : Type*) where dist : ℝ → M → M → ℝ; curvatureNorm : M → ℝ → ℝ; volume : ℝ → Set M → ℝ`
* `RicciFlowData.ball` — 62: `def ball {M : Type*} (flow : RicciFlowData M) (t : ℝ) (x₀ : M) (r : ℝ) : Set M :=`
* `RicciFlowData.HasCurvatureBoundOnParabolicBall` — 69: `def … {M : Type*} (flow : RicciFlowData M) (x₀ : M) (t₀ r bound : ℝ) : Prop :=`
* `IsKappaNoncollapsedOnScale` — 79: `def … {M : Type*} (flow : RicciFlowData M) (n : ℕ) (T kappa rho : ℝ) : Prop :=`
* `IsKappaCollapsedAt` — 88: `def … {M : Type*} (flow : RicciFlowData M) (n : ℕ) (kappa r t₀ : ℝ) (x₀ : M) : Prop :=`
* `isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate` — 115: `theorem … {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M] (flow : RicciFlowData M) (μ : Measure M) (K : Poincare.Longrun.Topology.CurvatureBoundedOn M) {T t₀ κ ρ r₀ : ℝ} (ht₀T : t₀ < T) (hr₀ : 0 < r₀) (hr₀ρ : r₀ < ρ) (hscale : ρ ^ (2 : ℕ) ≤ t₀) (hκ : 0 < κ) (hvol : ∀ x r, 0 < r → ENNReal.ofReal (flow.volume t₀ (flow.ball t₀ x r)) ≤ μ (Metric.eball x (ENNReal.ofReal r))) (hcurv : ∀ x r, 0 < r → K x r → flow.HasCurvatureBoundOnParabolicBall x t₀ r ((r⁻¹) ^ 2)) (hkl : IsKappaNoncollapsedOnScale flow 3 T κ ρ) : Poincare.Longrun.Topology.KappaNoncollapsingCertificate M μ K κ r₀ where`

Transcription faithfulness spot-check (upstream `third_party/frenzymath/Poincare-Conjecture/formalized-sources/`): `KleinerLott/…/Noncollapsing.lean:15/21/30/39` are character-for-character the local `ball`/`HasCurvatureBoundOnParabolicBall`/`IsKappaNoncollapsedOnScale`/`IsKappaCollapsedAt` bodies (modulo `r ^ 2` vs `r ^ (2 : ℕ)`), and `Evans/…/Ch02/Heat.lean:32` (`heatKernelSpatial`) and `:124` (`heatKernel`) are correctly quoted.

## 1.C Semantic classification (exactly one class per headline declaration)

| declaration | class | justification from the type |
| --- | --- | --- |
| `heatKernelSpatial`, `heatSolution`, `solitonScale`, `metricLieDerivativeFlat`, `shrinkerGradientField`, `IsSolitonGeneratorEuclidean`, `IsGradientShrinkerPotentialEuclidean`, `RicciFlowData`, `RicciFlowData.ball`, `RicciFlowData.HasCurvatureBoundOnParabolicBall`, `IsKappaNoncollapsedOnScale`, `IsKappaCollapsedAt`, `boundedContinuousClass` | **statement-only** (definition/interface/Prop, no proof) | `def`/`structure`/`noncomputable def`; no proposition is asserted |
| `heatKernelSpatial_eq_gaussianKernel` | **general theorem** | no hypotheses; `∀ n t`, definitional (`:= rfl`) identity of two explicit kernels on `EuclideanSpace ℝ (Fin n)` |
| `integrable_heatKernelSpatial`, `heatKernelSpatial_integral`, `heatSolution_eq_convolution` | **general theorem** | quantified over all `n`; only side condition `0 < t` for the integral; no geometric hypothesis |
| `heatSolution_eq_flatKernelConv` | **general theorem** | `∀ n g x`, hypothesis `0 < t`; identity of two explicit convolutions |
| `heatKernelSpatial_contDiff_compat`, `heatKernelSpatial_bound_compat` | **general theorem** | `∀ n` at fixed `t = 1`; no hypotheses |
| `solitonScale_eq_fflowMetricScale` | **general theorem** | `∀ τ₀ t`; definitional identity (proved by `field_simp` case split, no hypotheses) |
| `heatSolution_approx_bound_at_of_bounded` | **conditional** | explicit hypotheses `hg`, `hM`, `hη`, `hosc`, `ht`, `hx`; conclusion is an ε-bound |
| `heatSolution_tendsto_initial_of_bounded`, `heatSolution_tendsto_initial_joint_of_bounded` | **conditional** | explicit hypotheses `hg : Continuous g`, `hM : ∀ y, |g y| ≤ M`; conclusion `Tendsto …` |
| `heatSolution_tendsto_initial_of_integrable` | **conditional** | `hf : Continuous f`, `hfi : Integrable f volume` |
| `boundedClass_cls_iff_integrableClass_cls_of_compactSpace_finiteMeasure` | **conditional** | typeclass hypotheses `[CompactSpace X] [IsFiniteMeasure μ]`; an `↔` between two class predicates |
| `weakInitialConditionFor_boundedClass_iff_full_of_compact_finiteMeasure` | **conditional** | `[CompactSpace X] [IsFiniteMeasure D.volume]`; an `↔` |
| `hasDerivAt_integral_mul_hasCompactSupport` | **conditional** | explicit `hg`, `hgc`, `hU`, `hs₀`, `hKcont`, `hK'cont`, `hderiv` |
| `shrinkerGradientField_isGradient` | **model** | statement about the explicit flat model, `f = ‖y‖²/(4τ)`, field `x ↦ (1/2τ)x`; hypothesis `τ ≠ 0` |
| `fderiv_shrinkerGrad` | **model** | `∀ n {τ}`, statement about the specific field `x ↦ (1/2τ)•x` |
| `metricLieDerivativeFlat_shrinkerGrad` | **model** | flat-model Lie derivative of the specific shrinker gradient; `τ ≠ 0` |
| `shrinkerFpot_isGradientShrinkerPotentialEuclidean` | **model** | (GSS) on the explicit Gaussian shrinker; `0 < τ` |
| `shrinkerGrad_isSolitonGeneratorEuclidean` | **model** | soliton-generator equation on the same explicit shrinker |
| `isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean` | **conditional** | typed implication; antecedents `hgradLie` (upstream theorem exposed as hypothesis) and `h` (the (GSS) predicate) |
| `shrinkerFpot_GSS_and_solitonGenerator` | **model** | conjunction of the two model facts on the explicit shrinker |
| `isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate` | **conditional** | typed implication; translation hypotheses `hcurv`, `hvol`, `ht₀T`, `hr₀`, `hr₀ρ`, `hscale`, `hκ` and upstream predicate `hkl` |

§7 of the card is consistent with this table (its row "upstream compiled theorem (locally re-verified)" for `heatSolution_approx_bound_at_of_bounded`/`…_of_bounded`/`…_joint_of_bounded` and `hasDerivAt_integral_mul_hasCompactSupport` is a provenance class, not a semantic one; the semantic content is conditional as noted).

## 1.D Blocker claims and hypothesis-smuggling

* No closure is claimed. `D13-upstream-adapter-audit.json` has `"exact_blockers_closed": []` and `"exact_blockers_closed_note"` explicitly listing A1 as "verified-corrected" (not closed), A3 as "remains open", P1 "mirrored in-worktree", P5 "re-run and PASS"; `.md` §10 line 151: "**Remaining (none closed by this task):** A1 … A3 (open), P1 (integrator promotion), P5 (per-release check)". The A1-corrected theorems exist with the claimed sharp hypotheses: `Discrete.lean:48` `theorem perelmanF_step_le (F : ReactionField ι) {c : ι → ℝ} (hc : ∀ i, 1 ≤ c i) …`; `Gibbs.lean:76` `theorem gibbsTerm_antitone (c : ℝ) (hc : 1 ≤ c) : Antitone (gibbsTerm c)`; `Gibbs.lean:158` `theorem gibbsTerm_step_le {c x u : ℝ} (hc : 1 ≤ c) (hu : 0 ≤ u) : …`.
* `(h : P) : P` shapes: none found. The only two conditional adapters each require a genuine bridge: `isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean` needs `hgradLie`, which is *not* the conclusion (`IsSolitonGeneratorEuclidean`) but the upstream Lie-derivative identity; `isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate` needs both `hkl` (upstream predicate) and `hvol` (an **upper** comparison `ENNReal.ofReal (flow.volume …) ≤ μ (eball …)`), while its conclusion is the **lower** bound `ENNReal.ofReal (κ*r³) ≤ μ (eball …)`.
  **Nuance (disclosed, not a defect):** the substantive κ-lower-bound content of the adapter's conclusion is *transported* from the hypothesis `hkl` through `hvol`; the adapter creates no new non-collapsing content. The card says exactly this: line 67 "conditional adapter", line 105–112 "Hypotheses (all expanded, none equivalent to the conclusion)" and lines 109–111 "`hvol` — … an *upper* comparison, while the conclusion is the κ-*lower* bound".

## 1.E Over-claim / honesty findings

* **F1-a (mapping prose not backed by a declaration).** §3.3 line 68 claims the Gaussian reduced-volume row is an "identity via the Evans theorem (rfl-transport)" against the D12 `gaussianReducedVolume_eq_one`. `grep -rn "gaussianReducedVolume" release/Poincare/D13/` → **0 hits** in the D13 module set; no D13 declaration links `heatKernelSpatial_integral` to the D12 reduced-volume theorem, and no such identity is in the 36-declaration audit list (Audit.lean:124–159). The D12 theorem itself exists (`Poincare/D12/KappaVariational/GaussianNormalization.lean:223`), but the "identity" is an unformalised mapping assertion.
* **F1-b (compile evidence partially unverifiable).** The relayed `longrun/ev-logs/lean-Audit.log` contains all 36 `#print axioms` transcripts and the PASS line (line 93: "D13UpstreamAdapterAxiomCheck: PASS — all 36 declarations …"), which independently evidences that the module set was compiled by the time the log was produced. But the `8909 jobs`/`8960 jobs` counts are **not relayed** (only per-file `lake env lean` logs exist), and the five non-Audit per-file logs (`lean-{EvansHeat,EvansParametric,MorganTianShrinker,KleinerLottKappa,All}.log`) are 0 bytes — consistent with success-with-no-output, but not independent proof of `exit 0`. → job counts "undetermined from relayed snapshot".
* **F1-c (negative control not relayed).** `/tmp/d13neg/NegativeAudit.lean` and axiom `d13AuditFakeAxiom` are not in the relayed tree; `negcontrol/NegativeControl.lean` is a *different* D5-era control (`negControl_sorry`, `negControl_nativeDecide`). The card's fail-closed negative-control row (§6 line 108) is therefore **undetermined from relayed snapshot**.
* **F1-d (P5 target not relayed).** §8 P5 claims byte-identity against `D6_weekly_release/release`; that tree is not relayed → undetermined.
* **F1-e (supported).** "0 `sorry`/`axiom`/`admit`/`unsafe`/`native_decide`/`proof_wanted`" — scanner over `release/Poincare/D13` (6 files) → hard 0 / soft 0. Upstream hygiene over the quoted packages (`Evans` 65 files, `MorganTian` 573, `KleinerLott` 11) → hard 0 / soft 0. The "decisive negative" grep pattern of line 71 → 0 hits across `formalized-sources`.
* **F1-f (minor internal count slip).** §7 line 122 groups `heatKernelSpatial_contDiff_compat`, `heatKernelSpatial_bound_compat` under "model theorems (explicit flat Gaussian model, `τ > 0`)", but those two statements are at fixed `t = 1` and do not mention `τ`. Cosmetic classification slip only.

## 1.F Downstream use of headline constructors (task release sources)

* **No consumer outside `release/Poincare/D13/UpstreamAdapter/`** exists in the relayed release: `grep -rn "UpstreamAdapter\." <release> --include=*.lean | grep -v /D13/` → empty, and `release/ReleaseCheck.lean` / `ReleaseClaims.lean` / `lakefile.toml` never mention D13.
* Kernel-checked consumers inside the module set (Audit.lean examples): `Evans.heatSolution_tendsto_initial_of_bounded` at `Audit.lean:46`; `Evans.heatSolution_tendsto_initial_of_integrable` at `Audit.lean:55`; `MorganTian.solitonScale_eq_fflowMetricScale` at `Audit.lean:62`; `KleinerLott.isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate` at `Audit.lean:79`.
* Intra-file uses: `heatKernelSpatial_integral` → `EvansHeat.lean:165`; `fderiv_shrinkerGrad` → `MorganTianShrinker.lean:137`; `metricLieDerivativeFlat_shrinkerGrad` → `:172` and `:214`; `shrinkerFpot_isGradientShrinkerPotentialEuclidean` → `:208` and `:219`; `isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean` → `:209`.
* The remaining headline declarations (`heatKernelSpatial_eq_gaussianKernel`, `heatSolution_eq_flatKernelConv`, `boundedContinuousClass`, the two `…iff…` theorems, `heatSolution_tendsto_initial_joint_of_bounded`, `shrinkerGradientField_isGradient`, `shrinkerGrad_isSolitonGeneratorEuclidean`, `shrinkerFpot_GSS_and_solitonGenerator`, …) have **no consumer at all** in the relayed release other than their `#print axioms` lines. The card does not claim external consumers, so this is a completeness observation, not an over-claim.

## 1.G Verdict (card 1)

**Claims supported**, with two caveats: one mapping-table row (`gaussianReducedVolume_eq_one` "rfl-transport") is not backed by any declaration (F1-a), and the exact `lake build` job counts / negative control are not relayed (F1-b/c/d). Blocker accounting is honest (`exact_blockers_closed: []`). No forbidden token, no hypothesis smuggling, all local declaration names present, all 20 source hashes verified, all upstream citations verified.

---

# 2. Card 2 — `D13-morgan-tian-adapter-plan`

## 2.A Headline claims (verbatim, with `.md` line numbers)

C2.1 (line 11, Verdict): "**TASK_DONE for the D13 milestone** — a precise, compile-checked Morgan-Tian adapter plan and a Lean compatibility module set (`Poincare.D13.MorganTianAdapter`, 7 files, 50 audited declarations, 1119 lines) mapping the three local D12 objectives (EntropyVariation, HeatDomain, KappaVariational) and the objective blockers **U1/U2/U3/U4/U5/U9** to exact upstream MorganTian modules/declarations are delivered, kernel-checked and axiom-audited. **None of U1–U9 is claimed closed by this task** (see §8); the one genuinely new model-level closure is the flat-model case of the D7/D12 ball-volume-comparison input (KV-10/NCF-9, §6.3)."

C2.2 (lines 19–25, §1 table): `Curvature.lean` — "the honest chain-rule computation `flatRiemannCurvature_eq_secondDerivativeCommutator` and **`flatRiemannCurvature_eq_zero`** (U1, second-derivative symmetry); vanishing of the (0,4) form, Ricci, scalar and sectional curvature (U2); the four first-order symmetries + first Bianchi; the (GSS) shrinker equation discharged **through the computed flat Ricci** (`IsGradientShrinkerPotentialEuclidean_iff_flatRicci`, `shrinkerFpot_gradientShrinkerPotentialFlat`)"; `Tensoriality.lean` — "germ-locality of the section slot (`flatCovariantDeriv_congr_of_eventuallyEq`), the germ-vs-1-jet distinction (`flatCovariantDeriv_congr_of_eq_fderiv`)"; `ExpGeodesic.lean` — "geodesics = affine lines (`isGeodesicEuclidean_globalGeodesic`), `expMapEuclidean = x + t·v` with identity derivative (`fderiv_expMapEuclidean_eq_id`), injectivity, parallel transport = identity isometry"; `LeviCivitaSmoothness.lean` — "model discharge `flatCovariantDeriv_contDiff`"; `BishopGromov.lean` — "`antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one`, the flat-model equality case `flatModel_normalizedBallVolume_eq` (ω₃ = 4π/3), the **proved model case of KV-10/NCF-9** `flatModel_ballVolumeComparison`, and the downstream D3 `KappaNoncollapsingCertificate` on flat ℝ³ … (`flatModel_kappaNoncollapsingCertificate`, `flatModel_volume_ball_pos`)"; `Audit.lean` — "50 `#print axioms` + fail-closed `Lean.collectAxioms` gate + 4 kernel-checked downstream-use examples".

C2.3 (line 36, §2): "No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, fake proposition, weakened conclusion, or hypothesis equivalent to the conclusion occurs in the module set (fail-closed audit §7; negative control exit 1)."

C2.4 (lines 46–51, §3.1): "**proved on the flat model**: the honest product-rule computation reduces `∇_X∇_Y Z − ∇_Y∇_X Z − ∇_{[X,Y]}Z` to the commutator of second Fréchet derivatives, which vanishes by `second_derivative_symmetric` (hypotheses: `ContDiff ℝ 1 X/Y`, `ContDiff ℝ 2 Z` — expanded in §5)"; "pinned mathlib `RiemannCurvatureTensor` | **absent** (the U1 gap) | D7 `RiemannCurvatureData` + this flat transcription | U1 remains an upstream-mathlib-gap blocker".

C2.5 (lines 57–60, §3.2): "`flatRicciAt` (trace over `EuclideanSpace.single i 1`); `flatRicciAt_eq_zero` | proved on the flat model (U2)"; "`flatScalarCurvatureAt`; `flatScalarCurvatureAt_eq_zero`"; "**proved on the flat model through the computed flat Ricci**: `−Ric = Hess f − λg` with `f = ‖x‖²/(4τ)`, `λ = 1/(2τ)`".

C2.6 (lines 66–69, §3.3): "transcribed + proved on the flat model"; "`globalGeodesicEuclidean`, `isGeodesicEuclidean_globalGeodesic` | proved on the flat model (affine lines …)"; "`fderiv_expMapEuclidean_eq_id`, `expMapEuclidean_injective`, `flatSectionalCurvature_eq_zero_and_expDifferential_id` | proved on the flat model"; "`flatParallelTransport`, `flatParallelTransport_inner`, `flatParallelTransport_norm` | proved on the flat model (identity isometry)".

C2.7 (lines 76–80, §3.4): mathlib `LeviCivita.lean` docstring lines 22–23 "*\"Future PRs will prove smoothness…\"* | the **exact U4 source** (re-verified verbatim) | recorded; nothing is proved there in the pinned rev"; "**model discharge** `LeviCivitaSmoothness.flatCovariantDeriv_contDiff` / `flatLeviCivita_contDiff_pair` | **proved locally**".

C2.8 (lines 86–88, §3.5): "`Tensoriality.flatCovariantDeriv_congr_of_eventuallyEq` … `flatCovariantDeriv_congr_of_eq_fderiv`, `flatRiemannCurvature_congr_of_eq_at`, `flatCurvatureFormField_eq_flatCurvatureFormAt` | proved on the flat model"; "U5 distinction stated precisely … `flatCovariantDeriv_smul` …, `flatCovariantDeriv_congr_of_eq_at` …, `flatCovariantDeriv_congr_of_eventuallyEq` (germ ⇒ 1-jet ⇒ ∇)".

C2.9 (lines 94–99, §3.6): "`BishopGromov.antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one` (the general analysis core of the normalization conclusion, proved locally in ℝ), `flatModel_normalizedBallVolume_eq` (ω₃ = 4π/3, the equality case) | analysis core **proved locally**"; "**new proved closure at model level**: on flat ℝ³ the comparison holds with φ ≡ ω₃ (equality), and the D12 conditional transfer `gaussianKappaNoncollapsing_of_ballVolumeComparison` produces the D3 `KappaNoncollapsingCertificate` with κ = 4π/3, r₀ = 1".

C2.10 (lines 138–148, §6): "`lake build` … **exit 0 — Build completed successfully (9205 jobs), whole release tree**"; "7/7 exit 0"; "forbidden-token scan … **0 hard / 0 soft** matches".

C2.11 (lines 156–160, §7): "**50 / 50** — all depend only on `[propext, Classical.choice, Quot.sound]` (or fewer)"; gate PASS string; negative control; "forbidden tokens … **0 hard / 0 soft**".

C2.12 (lines 166–173, §8): U1–U5, U9 each "**open** (adapter evidence added)" / "**open** (remains a hypothesis on general manifolds; a mathlib PR is the closure path)"; line 173: "**exact_blockers_closed:** none of U1–U9 … **Model-level input closures achieved by this task (not U-blockers):** the flat constant-curvature case of the D7/D12 named input **KV-10 / NCF-9** … proved by `BishopGromov.flatModel_ballVolumeComparison` and consumed downstream by `flatModel_kappaNoncollapsingCertificate`."

C2.13 (lines 206–222, §11 re-verification): whole build "**exit 0** — 'Build completed successfully (9205 jobs)'"; "axiom gate | fresh Audit build log: `D13MorganTianAdapterAxiomCheck: PASS — all 50 declarations …`"; "source hashes | 7/7 authored modules sha256 = card §9 values"; "upstream citations | 11/11 spot-checked file:line citations verbatim"; "U9 negatives | … **0** reduced-volume/reduced-length/reduced-distance, **0** L-minimizer, **0** surgery hits"; "KV-10/NCF-9 claim | … honestly labeled model-level, not a U-blocker closure".

## 2.B Declaration census (full signatures; paths under `audit/ophis/D13-morgan-tian-adapter-plan/release/Poincare/D13/MorganTianAdapter/`)

Every declaration named in card 2 exists. No missing-name F-finding.

`Curvature.lean`:
* `flatMetric` — 74: `def flatMetric (_p : Euc n) (v w : Euc n) : ℝ :=`
* `flatCovariantDeriv` — 81: `noncomputable def flatCovariantDeriv (X Y : Euc n → Euc n) (p : Euc n) : Euc n :=`
* `flatLieBracket` — 86: `noncomputable def flatLieBracket (X Y : Euc n → Euc n) (p : Euc n) : Euc n :=`
* `flatRiemannCurvature` — 92: `noncomputable def flatRiemannCurvature (X Y Z : Euc n → Euc n) (p : Euc n) : Euc n :=`
* `flatCurvatureFormField` — 99: `noncomputable def … (X Y Z W : Euc n → Euc n) (p : Euc n) : ℝ :=`
* `flatCurvatureFormAt` — 107: `noncomputable def … (p : Euc n) (v w z t : Euc n) : ℝ :=`
* `flatRicciAt` — 114: `noncomputable def … (p : Euc n) (v w : Euc n) : ℝ :=`
* `flatScalarCurvatureAt` — 121: `noncomputable def … (p : Euc n) : ℝ :=`
* `flatSectionalCurvatureAt` — 126: `noncomputable def … (p : Euc n) (v w : Euc n) : ℝ :=`
* `IsGradientShrinkerPotentialFlat` — 132: `noncomputable def … (f : Euc n → ℝ) (lambda : ℝ) : Prop :=` (body: `ContDiff ℝ (⊤ : ℕ∞) f ∧ 0 < lambda ∧ ∀ (p v w : Euc n), -flatRicciAt p v w = iteratedFDeriv ℝ 2 f p ![v, w] - lambda * ⟪v, w⟫_ℝ`)
* `flatRiemannCurvature_eq_secondDerivativeCommutator` — 145: `theorem … {X Y Z : Euc n → Euc n} (p : Euc n) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hZ : ContDiff ℝ 2 Z) : flatRiemannCurvature X Y Z p = ((fderiv ℝ (fun q : Euc n => fderiv ℝ Z q) p) (X p)) (Y p) - ((fderiv ℝ (fun q : Euc n => fderiv ℝ Z q) p) (Y p)) (X p) := by`
* `flatRiemannCurvature_eq_zero` — 190: `theorem … {X Y Z : Euc n → Euc n} (p : Euc n) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hZ : ContDiff ℝ 2 Z) : flatRiemannCurvature X Y Z p = 0 := by`
* `flatCurvatureFormAt_eq_zero` — 210: `theorem … (p : Euc n) (v w z t : Euc n) : flatCurvatureFormAt p v w z t = 0 := by`
* `flatRicciAt_eq_zero` — 218: `theorem … (p : Euc n) (v w : Euc n) : flatRicciAt p v w = 0 := by`
* `flatScalarCurvatureAt_eq_zero` — 223: `theorem … (p : Euc n) : flatScalarCurvatureAt p = 0 := by`
* `flatSectionalCurvatureAt_eq_zero` — 230: `theorem … (p : Euc n) (v w : Euc n) : flatSectionalCurvatureAt p v w = 0 := by`
* `flatCurvatureFormAt_antisymm_left` — 244: `theorem … (p : Euc n) (v w z t : Euc n) : flatCurvatureFormAt p v w z t = -flatCurvatureFormAt p w v z t := by`; `_antisymm_right` — 248; `_pairSwap` — 252; `_firstBianchi` — 256: `… + flatCurvatureFormAt p w z v t + flatCurvatureFormAt p z v w t = 0 := by`
* `IsGradientShrinkerPotentialEuclidean_iff_flatRicci` — 269: `theorem … (f : Euc n → ℝ) (lambda : ℝ) : UpstreamAdapter.MorganTian.IsGradientShrinkerPotentialEuclidean n f lambda ↔ IsGradientShrinkerPotentialFlat f lambda := by`
* `shrinkerFpot_gradientShrinkerPotentialFlat` — 290: `theorem … (n : ℕ) {τ : ℝ} (hτ : 0 < τ) : IsGradientShrinkerPotentialFlat (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) (1 / (2 * τ)) := by`
* `shrinkerFpot_isGradientShrinkerPotentialEuclidean` — 307: `theorem … (n : ℕ) {τ : ℝ} (hτ : 0 < τ) : UpstreamAdapter.MorganTian.IsGradientShrinkerPotentialEuclidean n (fun y : Euc n => ‖y‖ ^ 2 / (4 * τ)) (1 / (2 * τ)) :=`

`Tensoriality.lean`:
* `flatCovariantDeriv_smul` — 69: `theorem … (f : Euc n → ℝ) (X Y : Euc n → Euc n) (p : Euc n) : flatCovariantDeriv (fun q => f q • X q) Y p = f p • flatCovariantDeriv X Y p := by`
* `flatCovariantDeriv_congr_of_eq_at` — 77: `theorem … {X X' Y : Euc n → Euc n} (p : Euc n) (hX : X p = X' p) : flatCovariantDeriv X Y p = flatCovariantDeriv X' Y p := by`
* `flatCovariantDeriv_congr_of_eventuallyEq` — 90: `theorem … (X : Euc n → Euc n) (p : Euc n) {Y Y' : Euc n → Euc n} (hY : Y =ᶠ[𝓝 p] Y') (hd : DifferentiableAt ℝ Y p) (hd' : DifferentiableAt ℝ Y' p) : flatCovariantDeriv X Y p = flatCovariantDeriv X Y' p := by`
* `flatCovariantDeriv_congr_of_eq_fderiv` — 105: `theorem … (X : Euc n → Euc n) (p : Euc n) {Y Y' : Euc n → Euc n} (hD : fderiv ℝ Y p = fderiv ℝ Y' p) : flatCovariantDeriv X Y p = flatCovariantDeriv X Y' p := by`
* `flatRiemannCurvature_congr_of_eq_at` — 120: `theorem … {X X' Y Y' Z : Euc n → Euc n} (p : Euc n) (hX : ContDiff ℝ 1 X) (hX' : ContDiff ℝ 1 X') (hY : ContDiff ℝ 1 Y) (hY' : ContDiff ℝ 1 Y') (hZ : ContDiff ℝ 2 Z) (hXp : X p = X' p) (hYp : Y p = Y' p) : flatRiemannCurvature X Y Z p = flatRiemannCurvature X' Y' Z p := by`
* `flatCurvatureFormField_eq_flatCurvatureFormAt` — 134: `theorem … {X Y Z W : Euc n → Euc n} (p : Euc n) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hZ : ContDiff ℝ 2 Z) : flatCurvatureFormField X Y Z W p = flatCurvatureFormAt p (X p) (Y p) (Z p) (W p) := by`
* `flatRiemannCurvature_congr_of_eventuallyEq` — 149 (in the 50-declaration audit, not named by the card): `theorem … {X Y Z Z' : …} (p : Euc n) (hX : ContDiff ℝ 1 X) (hY : ContDiff ℝ 1 Y) (hZ : ContDiff ℝ 2 Z) (hZ' : ContDiff ℝ 2 Z') (_hZZ' : Z =ᶠ[𝓝 p] Z') : flatRiemannCurvature X Y Z p = flatRiemannCurvature X Y Z' p := by`

`ExpGeodesic.lean`:
* `IsGeodesicEuclidean` — 57: `noncomputable def … (γ : ℝ → Euc n) : Prop :=` (`∀ s, fderiv ℝ (fderiv ℝ γ) s = 0`)
* `expMapEuclidean` — 62: `noncomputable def … (t : ℝ) (v : Euc n) (x : Euc n) : Euc n :=`
* `globalGeodesicEuclidean` — 67: `noncomputable def … (x v : Euc n) (s : ℝ) : Euc n :=`
* `flatParallelTransport` — 74: `noncomputable def … (_x _y v : Euc n) : Euc n :=`
* `expMapEuclidean_eq` — 80: `theorem … (t : ℝ) (v x : Euc n) : expMapEuclidean t v x = x + t • v := rfl`
* `isGeodesicEuclidean_globalGeodesic` — 88: `theorem … (x v : Euc n) : IsGeodesicEuclidean (globalGeodesicEuclidean x v) := by`
* `fderiv_expMapEuclidean_eq_id` — 108: `theorem … (t : ℝ) (v x : Euc n) : fderiv ℝ (expMapEuclidean t v) x = ContinuousLinearMap.id ℝ (Euc n) := by`
* `expMapEuclidean_injective` — 119: `theorem … (t : ℝ) (v : Euc n) : Function.Injective (expMapEuclidean t v) := by`
* `flatParallelTransport_inner` — 130: `theorem … (x y v w : Euc n) : ⟪flatParallelTransport x y v, flatParallelTransport x y w⟫_ℝ = ⟪v, w⟫_ℝ := rfl`; `_norm` — 135.
* `flatSectionalCurvature_eq_zero_and_expDifferential_id` — 143: `theorem … (p : Euc n) (v w : Euc n) (t : ℝ) (u x : Euc n) : Curvature.flatSectionalCurvatureAt p v w = 0 ∧ fderiv ℝ (expMapEuclidean t u) x = ContinuousLinearMap.id ℝ (Euc n) :=`

`LeviCivitaSmoothness.lean`:
* `flatCovariantDeriv_contDiff` — 62: `theorem … {X Y : Euc n → Euc n} (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y) : ContDiff ℝ (⊤ : ℕ∞) (fun p : Euc n => fderiv ℝ Y p (X p)) := by`
* `flatCovariantDeriv_eq_fderiv_apply` — 73: `theorem … (X Y : Euc n → Euc n) (p : Euc n) : flatCovariantDeriv X Y p = fderiv ℝ Y p (X p) := rfl`
* `flatLeviCivita_contDiff_pair` — 81: `theorem … {X Y : Euc n → Euc n} (hX : ContDiff ℝ (⊤ : ℕ∞) X) (hY : ContDiff ℝ (⊤ : ℕ∞) Y) : ContDiff ℝ (⊤ : ℕ∞) (fun p : Euc n => flatCovariantDeriv X Y p) := by`

`BishopGromov.lean`:
* `antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one` — 83: `theorem … {R : ℝ} (_hR : 0 < R) {f : ℝ → ℝ} (hanti : AntitoneOn f (Set.Ioo 0 R)) (hlim : Tendsto f (𝓝[>] 0) (𝓝 1)) {r : ℝ} (hr : r ∈ Set.Ioo 0 R) : f r ≤ 1 := by`
* `eball_ofReal_eq_ball` — 111 (audited, not named by the card).
* `flatModel_normalizedBallVolume_eq` — 124: `theorem … {r : ℝ} (hr : 0 < r) (x : EuclideanSpace ℝ (Fin 3)) : normalizedBallVolume (volume : Measure (EuclideanSpace ℝ (Fin 3))) x r = ENNReal.ofReal (Real.pi * 4 / 3) := by`
* `flatModel_ballVolumeComparison` — 155: `theorem … (r₀ : ℝ) : BallVolumeComparison (EuclideanSpace ℝ (Fin 3)) volume (fun _ _ => True) (gaussianReducedVolumeCertificate 3) (fun _ => 4 * Real.pi / 3) r₀ := by`
* `flatModel_kappaNoncollapsingCertificate` — 168: `theorem … : KappaNoncollapsingCertificate (EuclideanSpace ℝ (Fin 3)) volume (fun _ _ => True) (4 * Real.pi / 3) 1 := by`
* `flatModel_volume_ball_pos` — 179: `theorem … {x : EuclideanSpace ℝ (Fin 3)} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) : 0 < volume (Metric.eball x (ENNReal.ofReal r)) :=`

Consumed local definitions verified where the card relies on them: `Poincare/D7/Kappa/Basic.lean:72` `structure BallVolumeComparison … where comparison : ∀ x r, 0 < r → r ≤ r₀ → K x r → ENNReal.ofReal (φ (C.volume (r ^ 2))) ≤ normalizedBallVolume μ x r`; `Poincare/D12/KappaVariational/Statements.lean:150` `theorem gaussianKappaNoncollapsing_of_ballVolumeComparison …`; `Poincare/D12/KappaVariational/Transfer.lean:62` `def gaussianReducedVolumeCertificate`; `Poincare/Longrun/Topology/Noncollapsing.lean:68` `structure KappaNoncollapsingCertificate …` with fields `kappa_pos`, `r0_pos`, `volume_ball_lower`; `Poincare/D7/LeviCivita/Blocked.lean:57/139/149/162` as cited by the card.

## 2.C Semantic classification (exactly one class per headline declaration)

| declaration | class | justification from the type |
| --- | --- | --- |
| `flatMetric`, `flatCovariantDeriv`, `flatLieBracket`, `flatRiemannCurvature`, `flatCurvatureFormField`, `flatCurvatureFormAt`, `flatRicciAt`, `flatScalarCurvatureAt`, `flatSectionalCurvatureAt`, `IsGradientShrinkerPotentialFlat`, `IsGeodesicEuclidean`, `expMapEuclidean`, `globalGeodesicEuclidean`, `flatParallelTransport` | **statement-only** | `def`/`noncomputable def`, no proof, no asserted proposition |
| `flatRiemannCurvature_eq_secondDerivativeCommutator`, `flatRiemannCurvature_eq_zero`, `flatCurvatureFormAt_eq_zero`, `flatRicciAt_eq_zero`, `flatScalarCurvatureAt_eq_zero`, `flatSectionalCurvatureAt_eq_zero`, `flatCurvatureFormAt_antisymm_left/_right/_pairSwap/_firstBianchi`, `IsGradientShrinkerPotentialEuclidean_iff_flatRicci`, `shrinkerFpot_gradientShrinkerPotentialFlat`, `shrinkerFpot_isGradientShrinkerPotentialEuclidean` | **model** | statements only about the explicit flat Euclidean model `Euc n` / flat ℝ³; regularity hypotheses `ContDiff ℝ 1/2` are smoothness data, not translation hypotheses; the zero theorems are unconditional |
| `flatCovariantDeriv_smul`, `flatCovariantDeriv_congr_of_eq_at`, `flatCovariantDeriv_congr_of_eventuallyEq`, `flatCovariantDeriv_congr_of_eq_fderiv`, `flatRiemannCurvature_congr_of_eq_at`, `flatCurvatureFormField_eq_flatCurvatureFormAt`, `flatRiemannCurvature_congr_of_eventuallyEq` | **model** | flat-model instances; `flatCovariantDeriv_congr_of_eventuallyEq` uses the germ hypothesis `Y =ᶠ[𝓝 p] Y'` but the conclusion is about the flat connection |
| `isGeodesicEuclidean_globalGeodesic`, `fderiv_expMapEuclidean_eq_id`, `expMapEuclidean_injective`, `flatParallelTransport_inner`, `flatParallelTransport_norm`, `flatSectionalCurvature_eq_zero_and_expDifferential_id` | **model** | explicit affine lines / identity transport on `Euc n` |
| `flatCovariantDeriv_contDiff`, `flatCovariantDeriv_eq_fderiv_apply`, `flatLeviCivita_contDiff_pair` | **model** | flat connection on `Euc n` (though `flatCovariantDeriv_eq_fderiv_apply` is `rfl`) |
| `antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one` | **general theorem** | arbitrary `f : ℝ → ℝ`, arbitrary `R`, hypotheses `AntitoneOn …`/`Tendsto …`/`r ∈ Ioo 0 R`; no geometric model |
| `eball_ofReal_eq_ball` | **general theorem** | arbitrary finite index type `ι`, `EuclideanSpace ℝ ι` |
| `flatModel_normalizedBallVolume_eq`, `flatModel_ballVolumeComparison`, `flatModel_kappaNoncollapsingCertificate`, `flatModel_volume_ball_pos` | **model** | statements only about flat `ℝ³` (`EuclideanSpace ℝ (Fin 3)`), Lebesgue volume |

The card's own §7/JSON classification (`local_proved_theorem_model`, `…_general`, `…_definitional_bridge`, `upstream_source_claim_transcribed_definition`) is consistent with this table.

## 2.D Blocker claims and hypothesis-smuggling

* No closure claimed. `.json` has `"exact_blockers_closed": []`; `.md` line 173: "**exact_blockers_closed:** none of U1–U9 (they are upstream-mathlib-gap blockers; this task maps them and proves the flat-model instances)"; line 192: "**Remaining (none closed by this task):** U1, U2, U3, U4, U5, U9"; line 226: "does not claim any of U1/U2/U3/U4/U5/U9 is closed by this task".
* `(h : P) : P` shapes: none. The only theorem in the module set with a translation-flavoured hypothesis is `IsGradientShrinkerPotentialEuclidean_iff_flatRicci` — an `↔` between the D13 transcription and the flat-Ricci form, with the proof transporting across `flatRicciAt_eq_zero` (lines 269–282); it is a definitional bridge, not a restatement.
* The model-level closure that *is* claimed (KV-10/NCF-9 flat case) is genuinely constructed: `flatModel_normalizedBallVolume_eq` (line 124) proves `μ(B(x,r))/r³ = ω₃` via mathlib `EuclideanSpace.volume_ball_fin_three` (line 130), `flatModel_ballVolumeComparison` (line 155) instantiates `BallVolumeComparison` with `φ ≡ 4π/3`, and `flatModel_kappaNoncollapsingCertificate` (line 168) fires the D12 conditional transfer `gaussianKappaNoncollapsing_of_ballVolumeComparison` with all its side conditions discharged (`0<κ`, `0<r₀`, `r₀²≤1`, monotone φ, φ 1 = κ at lines 171–173). The card says "model-level, not a U-blocker closure" (line 173, line 222) — accurate.

## 2.E Over-claim / honesty findings

* **F2-a (broken internal cross-reference).** `.md` line 11 cites "(KV-10/NCF-9, §6.3)"; §6 is "Compile evidence" (lines 131–148) and contains no subsection 6.3. The referenced content is §8 line 173. Documentation defect only.
* **F2-b (compile evidence verified).** `longrun/ev-logs/build-verify-whole.log` ends "Build completed successfully (9205 jobs)." and `build-Audit.log`/`verify-build-Audit.log` line 296 contain "D13MorganTianAdapterAxiomCheck: PASS — all 50 declarations of the D13 MorganTian-adapter module set depend only on [propext, Classical.choice, Quot.sound]". §6/§7/§11 counts corroborated. (The whole-build log also contains a D6AUDIT line mentioning the compiler-generated `Poincare.Longrun.Surgery.SurgeryChain.append._unsafe_rec`; that is a well-founded-recursion internal name, and the same log's D6AUDIT verdict line is "PASS — no sorryAx, no project axiom, no unsafe, no native_decide, no unapproved axiom, no proof_wanted".)
* **F2-c (negative control not relayed).** `/tmp/d13mtneg/NegativeAudit.lean` and `d13MtFakeAxiom` are not relayed → the "negative control exit 1" row (§7 line 158, §11 line 214) is undetermined from the relayed snapshot. The relayed `negcontrol/NegativeControl.lean` is the different D5-era control (see §0).
* **F2-d (tree hash not reproducible).** §9 line 186 gives the upstream snapshot tree sha256 `e574480eefb8b5ad16351356978b37f658a3806c8a6b1450f274d82d5fe10495` ("all-files sorted method", §11 line 215). The snapshot is relayed, but I could not reproduce this value with `find . -type f | sort | xargs sha256sum | sha256sum` over `third_party/frenzymath` (26959b57…) or over `…/Poincare-Conjecture` (b53fcbe5…), nor the hashes-only variant (d28f7e49…). Method unspecified → **undetermined from relayed snapshot**; not evidence of a defect.
* **F2-e (source-worktree comparison not relayed).** §11 line 216 claims `diff -rq` clean against "the three D12 source worktrees"; those worktrees are not relayed. What I could check is clean: `Poincare/{D7,D10,D11,D12}` are byte-identical across the morgan-tian and topping releases, and `D13/UpstreamAdapter` is byte-identical to the D13-upstream-adapter-audit copy.
* **F2-f (supported).** Forbidden-token scan over `release/Poincare/D13` (13 files) → hard 0 / soft 0; upstream hygiene over the quoted packages → hard 0 / soft 0; U9 negatives in the snapshot: exact card-1 pattern `WEntropy|Fentropy|ntropy|reducedVolume|reducedLength|L-length|IsLMinimizer` → 0 hits, `surgery|Surgery` → 0 hits in `formalized-sources/**/*.lean`; `LMinimizer` → 0. The 39 `minimizer` hits are the minimizing-geodesic theory the card maps as source claims.
* **F2-g (mathlib docstring claim not independently checkable).** §3.4/§11 cite mathlib `…/CovariantDerivative/LeviCivita.lean` docstring lines 22–23. The pinned mathlib checkout is not relayed → **undetermined from relayed snapshot**; corroborating identical quotes exist in the relayed local D7 layer (`release/Poincare/D7/LeviCivita/Blocked.lean:98`, `Probe.lean:59`) but those are the program's own copies.
* **F2-h (source-docstring naming slip, not a card claim).** `Curvature.lean:45` (file header comment) names `shrinkFpot_gradientShrinkerPotential_flatRicci`; the actual declaration is `shrinkerFpot_gradientShrinkerPotentialFlat` (line 290). The card `.md`/`.json` use the correct name (`shrinkerFpot_gradientShrinkerPotentialFlat`, `.md` line 19 and line 60). Not a card defect; recorded because it is a named-declaration mismatch inside the audited source.

## 2.F Downstream use of headline constructors (task release sources)

* **Cross-file consumers inside the module set (real, code-level):** `flatRiemannCurvature_eq_secondDerivativeCommutator` → `Tensoriality.lean:125,126`; `flatRiemannCurvature_eq_zero` → `Tensoriality.lean:139,142,153`; `shrinkerFpot_isGradientShrinkerPotentialEuclidean` name is reused by the D13 UpstreamAdapter file (`D13/UpstreamAdapter/MorganTianShrinker.lean:307`'s counterpart is a different declaration with the same short name — the consumer here is `Curvature.lean:307` itself).
* **Kernel-checked examples in Audit.lean:** `Curvature.shrinkerFpot_isGradientShrinkerPotentialEuclidean` at `Audit.lean:43`; `BishopGromov.flatModel_kappaNoncollapsingCertificate` at `Audit.lean:52`; `ExpGeodesic.isGeodesicEuclidean_globalGeodesic` at `Audit.lean:57`; `Curvature.flatCurvatureFormAt_firstBianchi` at `Audit.lean:64`.
* **Intra-file use:** `IsGradientShrinkerPotentialEuclidean_iff_flatRicci` and `shrinkerFpot_gradientShrinkerPotentialFlat` → `Curvature.lean:310–311`; `flatModel_ballVolumeComparison` → `BishopGromov.lean:173`; `flatModel_kappaNoncollapsingCertificate` → `BishopGromov.lean:182`; `flatSectionalCurvatureAt_eq_zero` → `ExpGeodesic.lean:147`.
* **No consumers outside `release/Poincare/D13/MorganTianAdapter/`**: `grep -rn "MorganTianAdapter\." <morgan-tian release> --include=*.lean | grep -v /D13/` → empty; `ReleaseCheck.lean`/`ReleaseClaims.lean`/`lakefile.toml` contain no D13 reference.
* The other U1–U5/U9 headline theorems (e.g. `flatRicciAt_eq_zero`, `flatScalarCurvatureAt_eq_zero`, the Tensoriality locality lemmas, `expMapEuclidean_injective`, `flatCovariantDeriv_contDiff`, `antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one`, the flat-model ℝ³ theorems outside BishopGromov's internal chain) have **no consumer at all** in the relayed release besides `#print axioms`. The card does not claim external consumers.

## 2.G Verdict (card 2)

**Claims supported.** Compile evidence is relayed and matches (9205 jobs, PASS 50/50); the model-level KV-10/NCF-9 claim is genuinely proved and honestly scoped; blocker accounting is honest; all named local declarations exist with the claimed signatures and hypotheses; all hashes match; no forbidden tokens; no smuggled conclusion. Only defects: a stale "§6.3" cross-reference, an unrelayed negative control, an unreproducible tree hash, and a source-comment name slip (not a card claim).

---

# 3. Card 3 — `D13-topping-ricci-adapter-plan`

## 3.A Headline claims (verbatim, with `.md` line numbers)

C3.1 (line 10, Verdict): "**TASK_DONE for the D13 milestone** — a precise, compile-checked adapter plan and a small Lean compatibility module (`Poincare.D13.ToppingAdapter`, 7 files, 50 audited declarations, 1723 lines) mapping the local D12 objectives to the upstream **Topping** package for the objective blockers **U6 / U7 / U8 / I2** are delivered, kernel-checked and axiom-audited. **No objective blocker is claimed closed** (see §8)".

C3.2 (lines 18–24, §1 table): `Core.lean` — "**verbatim transcription, locally re-verified** of the compact-space weak maximum principle, `Topping/Topping/MaximumPrinciple/Core.lean` (10 theorems, upstream file:line cited), plus the local expanded-hypothesis variant `nonpos_of_forall_isMax_time_deriv_le_of_pos'`"; `Slab.lean` — "the **I2 adapter** … the continuous heat weak maximum principle on `[a,b] × [0,T]` for classical solutions (`SlabRegularity` expanded hypotheses), proved via the transcribed Topping core"; `Scalar.lean` — "**verbatim transcription, locally re-verified** of `Topping/ParabolicPDE/Scalar.lean` … + the **U6/U8 symbol-level correspondence** with the local D9 `flowSymbol`/`laplacianSymbol`"; `ShortTime.lean` — "closed local theorems `shortTimeRicciFlow_of_splitInputs` … and `localDeTurckStrictParabolic`"; `Volume.lean` — "`hasVolumeDerivativeOn_of_weightedDensity_local`, the upstream volume-evolution theorem re-proved **through the local D12 theorem**".

C3.3 (line 35, §2): "No `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted`, fake proposition, weakened conclusion, or hypothesis equivalent to the conclusion occurs in the module set (fail-closed audit §6, token scan §6)."

C3.4 (line 39, §3): "The D12 objectives mapped: `D12-heat-domain-repair` (module `Poincare.D12.HeatDomain`), `D12-heat-semigroup-analysis` (`Poincare.D12.HeatSemigroup`), `D12-parabolic-local-existence` (`Poincare.D12.ParabolicLocal`), `D12-entropy-variation` (`Poincare.D12.EntropyVariation`), `D12-kappa-variational` (`Poincare.D12.KappaVariational`)."

C3.5 (line 46, §3.1): "**local proved theorem, expanded hypotheses** (`Slab.lean`) — the mathematical content of I2 for classical solutions, proved by the upstream Topping argument + `deriv_deriv_nonpos_of_isLocalMax`; the literal D2/D7 statement (without the regularity package) remains statement-only".

C3.6 (line 52, §3.2): upstream Scalar definitions "transcribed verbatim"; line 54: "transcribed + re-verified; **`heatPrincipalSymbol_eq_localLaplacianCoeff`**: the upstream heat principal symbol equals the local D9 Laplacian coefficient `|ξ|²_g` on the flat model — the same symbol object"; line 56: "recorded as upstream source claims (manifold level; needs upstream build)"; line 57: "remaining `ParabolicPDE/` (66 files: Hölder spaces, Schauder, Picard solvers) … recorded as upstream source claims".

C3.7 (line 63, §3.3): "**`Volume.hasVolumeDerivativeOn_of_weightedDensity_local`**: the upstream volume-evolution theorem re-proved **through the local D12 theorem** — downstream use of the D12 deliverable in the upstream statement's form"; line 65: "**the global divergence theorem, IBP and the Bochner formula are absent upstream too** (0 hits in the snapshot survey), so U7's IBP half stays open on both sides".

C3.8 (lines 71–73, §3.4): "**`ShortTime.shortTimeRicciFlow_of_splitInputs`** — the same closed assembly proved over the local D7 abstraction (conditional adapter; the antecedents are the split inputs, not the conclusion)"; "**`Scalar.flowSymbol_eq_neg_heatPrincipalSymbol`** and **`ShortTime.localDeTurckStrictParabolic`** — the upstream coercivity certificate in local terms (sign conventions matched)"; "**no upstream declaration produces a Picard model from an arbitrary metric**; U8 stays open on both sides".

C3.9 (line 82, §4): "Topping `Scalar.lean` exponential-conjugation jet block (`conjugatedScalarOperator_eq_quadratic_plus_lower`, Scalar.lean:265ff)"; line 84: "the Topping package (184 files) has **no** sorry/admit/axiom declarations (the 5 keyword hits are docstring text); it has **no** Perelman entropy/reduced-volume/κ content …; its short-time existence is **split** exactly like the local D7/D12 layer; and its maximum-principle core is fully proved."

C3.10 (lines 93–99, §5): "`lake build Poincare.D13.ToppingAdapter.Audit   # exit 0, \"Build completed successfully (8912 jobs)\"`"; "6/6 exit 0"; "Per-file logs: `tmp/lean-*.log`"; "The local D2/D7/D9/D12 dependency closure (8912 jobs) was rebuilt fresh from the accepted D12 scaffold sources (byte-identical copy, `diff -rq` clean against `D13-upstream-adapter-audit/release`)."

C3.11 (lines 105–109, §6): "**50 / 50** — all depend only on `[propext, Classical.choice, Quot.sound]`"; gate PASS string; negative control `/tmp/d13neg/NegativeAudit.lean`; "forbidden tokens … **0 hard / 0 soft** matches (7 files)".

C3.12 (lines 115–124, §7): "`Core.*` (10 transcribed Topping maximum-principle theorems) | upstream compiled theorem, locally re-verified"; "`Core.nonpos_of_forall_isMax_time_deriv_le_of_pos'` | local proved theorem, expanded hypotheses"; "`Scalar.*` (definitions + 13 transcribed theorems) | upstream compiled theorem / definition, locally re-verified"; "`ShortTime.SplitShortTimeInputs`, `shortTimeRicciFlow_of_splitInputs` | conditional adapter"; "`Volume.HasVolumeDerivativeOn`, `hasVolumeDerivativeOn_of_weightedDensity_local` | local proved theorem (adapter, downstream use of D12)".

C3.13 (lines 130–135, §8): I2 "**partially discharged — not closed.** The remaining gap is exact: the D2/D7 hypotheses record `deriv`/`iteratedDeriv 2` *values* (zero-fallback convention), which do not imply genuine differentiability"; U6 "**open** (mapped, not closed)"; U7 "**open** (analytic half mapped; the divergence theorem / IBP / Bochner formula are absent upstream too)"; U8 "**open** (mapped; split inputs remain antecedents)"; line 135: "`exact_blockers_closed`: **none** (empty list — none of U6/U7/U8/I2 is fully closed by this task; I2 is partially discharged, recorded above)".

## 3.B Declaration census (full signatures; paths under `audit/ophis/D13-topping-ricci-adapter-plan/release/Poincare/D13/ToppingAdapter/`)

All locally declared headline names exist. **One census exception:** the D12 counterpart modules/declarations credited in the mapping table are **not present in this task's relayed release** — see F3-a below.

`Core.lean` (10 audited declarations; upstream `Topping/Topping/MaximumPrinciple/Core.lean` has exactly 9 `theorem` declarations at lines 18/28/53/159/176/200/240/292/314 — see F3-b):
* `isLocalMaxOn_of_isMaxOn` — 57: `theorem … {X : Type*} [TopologicalSpace X] {f : X → ℝ} {s : Set X} {x : X} (h : IsMaxOn f s x) : IsLocalMaxOn f s x := by`
* `time_deriv_nonneg_of_isMaxOn_Icc` — 65: `theorem … {f : ℝ → ℝ} {f' t T : ℝ} (ht : t ∈ Icc 0 T) (htpos : 0 < t) (hmax : IsMaxOn f (Icc 0 T) t) (hderiv : HasDerivWithinAt f f' (Icc 0 T) t) : 0 ≤ f' := by`
* `nonpos_of_forall_isMax_time_deriv_le_of_pos` — 80: `theorem … {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] {w wt : X → ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T) (hcont : ContinuousOn (fun z : X × ℝ => w z.1 z.2) ((Set.univ : Set X) ×ˢ Icc 0 T)) (hderiv : ∀ x t, t ∈ Icc 0 T → HasDerivWithinAt (w x) (wt x t) (Icc 0 T) t) (hmax : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, 0 < w x t → (∀ y, w y t ≤ w x t) → wt x t ≤ K * w x t) (hzero : ∀ x, w x 0 ≤ 0) : ∀ x t, t ∈ Icc 0 T → w x t ≤ 0 := by`
* `nonpos_of_forall_isMax_time_deriv_le` — 185 (same shape, `hmax` for all `t`); `exists_nonneg_reaction_bound_on_rectangle` — 201; `exists_common_value_interval` — 223; `le_ode_solution_of_forall_isMax_time_deriv_le_of_pos` — 257; `…_le` — 308; `nonneg_of_forall_isMin_time_deriv_ge` — 329 (full statements quoted in the extraction; all are general theorems over an abstract compact space)
* `nonpos_of_forall_isMax_time_deriv_le_of_pos'` — 372: `theorem … {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X] {w wt : X → ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T) (hcont : …) (hderiv : ∀ x t, t ∈ Icc 0 T → 0 < t → HasDerivWithinAt (w x) (wt x t) (Icc 0 T) t) (hmax : ∀ t ∈ Icc 0 T, 0 < t → ∀ x, 0 < w x t → (∀ y, w y t ≤ w x t) → wt x t ≤ K * w x t) (hzero : ∀ x, w x 0 ≤ 0) : ∀ x t, t ∈ Icc 0 T → w x t ≤ 0 := by` — **this is the local variant, not an upstream transcription** (`Audit.lean:67`; §7 line 116 correctly classifies it as "local proved theorem, expanded hypotheses").

`Slab.lean`:
* `deriv_deriv_nonpos_of_isLocalMax` — 69: `lemma … {f : ℝ → ℝ} {x c : ℝ} (hmax : IsLocalMax f x) (hf : HasDerivAt f (deriv f x) x) (hdd : HasDerivAt (deriv f) c x) : c ≤ 0 := by`
* `iteratedDeriv_two_nonpos_of_isLocalMax` — 140: `lemma … {f : ℝ → ℝ} {x : ℝ} (hmax : IsLocalMax f x) (hf : HasDerivAt f (deriv f x) x) (hdd : HasDerivAt (deriv f) (iteratedDeriv 2 f x) x) : iteratedDeriv 2 f x ≤ 0 := by`
* `SlabRegularity` — 162: `def SlabRegularity (u : ℝ → ℝ → ℝ) (a b T : ℝ) : Prop := (∀ x t, x ∈ Icc a b → t ∈ Ioo 0 T → HasDerivAt (fun s => u x s) (deriv (fun s => u x s) t) t) ∧ (∀ x t, x ∈ Ioo a b → t ∈ Ioo 0 T → HasDerivAt (fun y => u y t) (deriv (fun y => u y t) x) x ∧ HasDerivAt (deriv (fun y => u y t)) (iteratedDeriv 2 (fun y => u y t) x) x)`
* `slab_nonpos_of_lt` — 179: `theorem … (u : ℝ → ℝ → ℝ) {a b T : ℝ} (hab : a ≤ b) (h : ContinuousHeatHypotheses u a b T) (hreg : SlabRegularity u a b T) {T' : ℝ} (hT' : 0 ≤ T') (hT'T : T' < T) : ∀ x, x ∈ Icc a b → ∀ t, t ∈ Icc 0 T' → u x t ≤ 0 := by`
* `continuousHeatMaximumPrinciple_of_topping` — 241: `theorem … (u : ℝ → ℝ → ℝ) {a b T : ℝ} (hab : a ≤ b) (h : ContinuousHeatHypotheses u a b T) (hreg : SlabRegularity u a b T) : ∀ x, x ∈ Icc a b → ∀ t, t ∈ Icc 0 T → u x t ≤ 0 := by`

`Scalar.lean`:
* `ScalarSecondOrderCoefficients` — 73 (structure `a : Ω → Matrix (Fin n) (Fin n) ℝ; b : Ω → Fin n → ℝ; c : Ω → ℝ`); `ScalarSecondOrderJet` — 79.
* `euclideanNormSq` — 85; `symbol` — 89; `ScalarSecondOrderCoefficients.principalSymbol` — 93: `def … {Ω : Type*} {n : ℕ} (A : ScalarSecondOrderCoefficients Ω n) (x : Ω) (ξ : Fin n → ℝ) : ℝ :=`; `IsPositiveDefinite` — 99; `PointwiseParabolic` — 104; `UniformlyParabolic` — 109.
* Transcribed theorems: `pointwiseParabolic_iff_symbol_positive` — 115; `symbol_zero` — 122; `symbol_add` — 127; `symbol_smul` — 140; `symbol_one` — 156; `euclideanNormSq_nonneg` — 162; `euclideanNormSq_pos` — 167; `uniformlyParabolic_pointwiseParabolic` — 179; `heatCoefficients_principalSymbol` — 196; `heatCoefficients_uniformlyParabolic` — 203; `heatCoefficients_pointwiseParabolic` — 211; `symbol_congruence` — 216; `IsPositiveDefinite.congruence` — 235 (13 transcribed theorems — the card's "13 transcribed theorems" count is correct).
* `heatCoefficients` — 189: `def heatCoefficients (Ω : Type*) (n : ℕ) : ScalarSecondOrderCoefficients Ω n where a := fun _ => 1; b := fun _ _ => 0; c := fun _ => 0`.
* Adapter definitions/theorems: `euclideanMetricData` — 257; `covectorOf` — 307; `covectorNormSq_euclidean_eq_euclideanNormSq` — 320: `theorem … {n : ℕ} (ξ : Fin n → ℝ) : covectorNormSq (euclideanMetricData n) (covectorOf ξ) = euclideanNormSq ξ := by`; `heatPrincipalSymbol_eq_localLaplacianCoeff` — 341: `theorem … {n : ℕ} (x ξ : Fin n → ℝ) : (heatCoefficients (Fin n → ℝ) n).principalSymbol x ξ = covectorNormSq (euclideanMetricData n) (covectorOf ξ) := by`; `flowSymbol_eq_neg_heatPrincipalSymbol` — 356: `theorem … {n : ℕ} (ξ : Fin n → ℝ) (h : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ) (X Y : Fin n → ℝ) : ((-2 : ℝ) • ricciSymbol (euclideanMetricData n) (covectorOf ξ) h + lieSymbol (euclideanMetricData n) (covectorOf ξ) h) X Y = - (heatCoefficients (Fin n → ℝ) n).principalSymbol (0 : Fin n → ℝ) ξ * h X Y := by` (the proof uses the local D9 `flowSymbol`/`laplacianSymbol` at lines 366).

`ShortTime.lean`:
* `SplitShortTimeInputs` — 78: `structure SplitShortTimeInputs (P : DeTurckParabolicProblem) : Prop where deTurckShortTime : DeTurckShortTimeExistence P; gaugeConversion : DeTurckToRicciConversion P`
* `shortTimeRicciFlow_of_splitInputs` — 88: `theorem … (P : DeTurckParabolicProblem) (h : SplitShortTimeInputs P) : ∃ T : ℝ, 0 < T ∧ ∃ u : ℝ → P.MetricState, u 0 = P.initial ∧ P.IsRicciFlowOn T u := by`
* `bilinPairing` — 102; `bilinPairing_pos_of_ne_zero` — 109; `localDeTurckStrictParabolic` — 164: `theorem … {n : ℕ} (ξ : Fin n → ℝ) (hξ : ξ ≠ 0) (h : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) →ₗ[ℝ] ℝ) (hh : h ≠ 0) : 0 < bilinPairing (euclideanMetricData n) h (laplacianSymbol (euclideanMetricData n) (covectorOf ξ) h) := by`; `deTurckLinearisationSymbol_strictParabolic_heatCoefficients` — 198.
* D7 interfaces consumed (verified): `Poincare/D7/ShortTime/Statements.lean:98` `def DeTurckShortTimeExistence (P : DeTurckParabolicProblem) : Prop := ∃ T, 0 < T ∧ ∃ u, u 0 = P.initial ∧ P.IsDeTurckSolutionOn T u`; `:110` `def DeTurckToRicciConversion (P) : Prop := ∀ T u, P.IsDeTurckSolutionOn T u → P.IsRicciFlowOn T (fun t => P.gaugeTransform u t)`.

`Volume.lean`:
* `HasVolumeDerivativeOn` — 74: `def HasVolumeDerivativeOn (R : ℝ → M → ℝ) (ρ : ℝ → M → NNReal) (ν : Measure M) (J : Set ℝ) : Prop := ∀ t ∈ J, HasDerivWithinAt (fun s => ∫ p, (ρ s p : ℝ) ∂ν) (-∫ p, R t p * (ρ t p : ℝ) ∂ν) J t`
* `hasVolumeDerivativeOn_of_weightedDensity_local` — 88: `theorem … {R : ℝ → M → ℝ} {ρ : ℝ → M → NNReal} {K U : Set ℝ} (hU : IsOpen U) (hKU : K ⊆ U) (hρmeas : ∀ t ∈ U, Measurable (ρ t)) (hρint : ∀ t ∈ U, Integrable (fun p => (ρ t p : ℝ)) ν) (hderiv : ∀ t ∈ U, ∀ p, HasDerivAt (fun s => (ρ s p : ℝ)) (-R t p * (ρ t p : ℝ)) t) (hderivMeas : ∀ t ∈ U, AEStronglyMeasurable (fun p => -R t p * (ρ t p : ℝ)) ν) (bound : M → ℝ) (hboundInt : Integrable bound ν) (hbound : ∀ᵐ p ∂ν, ∀ t ∈ U, ‖-R t p * (ρ t p : ℝ)‖ ≤ bound p) : HasVolumeDerivativeOn R ρ ν K := by` (body calls the D12 theorem at line 107).

Transcription faithfulness spot-check against `third_party/frenzymath/Poincare-Conjecture/formalized-sources/`: upstream `Topping/Topping/MaximumPrinciple/Core.lean:18–48` and the local `Core.lean:57–77` are byte-for-byte the same statement and proof body (only the namespace and the `private` modifier changed); upstream `ParabolicPDE/Scalar.lean:72–110, 195–217` and local `Scalar.lean:85–124, 189–213` likewise. Upstream `MaximumPrinciple/Volume.lean:59/76` and local `Volume.lean:74/88` correspond as claimed (the local def replaces `scalarCurvatureAt (g t)` by abstract `R` and bakes the volume integral into the predicate — the card describes this as an abstraction, lines 67–73).

## 3.C Semantic classification (exactly one class per headline declaration)

| declaration | class | justification from the type |
| --- | --- | --- |
| `Core.isLocalMaxOn_of_isMaxOn`, `Core.time_deriv_nonneg_of_isMaxOn_Icc`, `Core.nonpos_of_forall_isMax_time_deriv_le_of_pos`, `…_le`, `Core.exists_nonneg_reaction_bound_on_rectangle`, `Core.exists_common_value_interval`, `Core.le_ode_solution_of_forall_isMax_time_deriv_le_of_pos`, `…_le`, `Core.nonneg_of_forall_isMin_time_deriv_ge`, `Core.nonpos_of_forall_isMax_time_deriv_le_of_pos'` | **general theorem** | abstract `X` with `[TopologicalSpace X] [CompactSpace X] [Nonempty X]`, arbitrary `w wt T K`; no specific space |
| `Slab.deriv_deriv_nonpos_of_isLocalMax`, `Slab.iteratedDeriv_two_nonpos_of_isLocalMax` | **general theorem** | arbitrary `f : ℝ → ℝ`, local-max hypotheses |
| `SlabRegularity` | **statement-only** | a `def … : Prop` (regularity package), no proof obligation discharged by itself |
| `slab_nonpos_of_lt`, `continuousHeatMaximumPrinciple_of_topping` | **conditional** | explicit hypotheses `hab : a ≤ b`, `ContinuousHeatHypotheses u a b T`, `SlabRegularity u a b T` (and `T'`/`T'<T` for the first) |
| `Scalar.ScalarSecondOrderCoefficients`, `ScalarSecondOrderJet`, `euclideanNormSq`, `symbol`, `principalSymbol`, `IsPositiveDefinite`, `PointwiseParabolic`, `UniformlyParabolic`, `heatCoefficients`, `Scalar.euclideanMetricData`, `Scalar.covectorOf`, `ShortTime.bilinPairing`, `Volume.HasVolumeDerivativeOn` | **statement-only** | `def`/`structure`, no assertion |
| `Scalar.pointwiseParabolic_iff_symbol_positive`, `symbol_zero/add/smul/one`, `euclideanNormSq_nonneg/pos`, `uniformlyParabolic_pointwiseParabolic`, `heatCoefficients_principalSymbol`, `heatCoefficients_uniformlyParabolic`, `heatCoefficients_pointwiseParabolic`, `symbol_congruence`, `IsPositiveDefinite.congruence` | **general theorem** | arbitrary coefficient fields/matrices over arbitrary `Ω`, `n`, `m`; no flat-model restriction |
| `Scalar.covectorNormSq_euclidean_eq_euclideanNormSq`, `heatPrincipalSymbol_eq_localLaplacianCoeff`, `flowSymbol_eq_neg_heatPrincipalSymbol` | **model** | statements only about the explicit flat model `MetricData (Fin n → ℝ) (Fin n)` with Euclidean dot product |
| `ShortTime.SplitShortTimeInputs` | **statement-only** | a `structure … : Prop` of two antecedent Props |
| `shortTimeRicciFlow_of_splitInputs` | **conditional** | typed implication whose antecedent is the split-input structure; conclusion is the Ricci-flow existence statement |
| `ShortTime.bilinPairing_pos_of_ne_zero` | **general theorem** | arbitrary `MetricData V ι` and nonzero bilinear `h` |
| `ShortTime.localDeTurckStrictParabolic`, `deTurckLinearisationSymbol_strictParabolic_heatCoefficients` | **model** | flat `euclideanMetricData n` only |
| `Volume.hasVolumeDerivativeOn_of_weightedDensity_local` | **conditional** | explicit hypotheses (open `U`, measurability, integrability, pointwise derivative, domination) |

## 3.D Blocker claims and hypothesis-smuggling

* No closure claimed. `.json` `"exact_blockers_closed": []`; `.md` line 135: "`exact_blockers_closed`: **none** (empty list …)"; line 153: "**Remaining:** U6, U7, U8 (open), I2 (partially discharged; literal D2/D7 statement still statement-only)"; line 162: "does not claim U6/U7/U8/I2 is closed by this task".
* `(h : P) : P` shapes: none. `shortTimeRicciFlow_of_splitInputs` composes `DeTurckShortTimeExistence P` (∃ DeTurck solution) with `DeTurckToRicciConversion P` (∀ DeTurck solutions, the gauge transform is a Ricci flow). The conclusion `∃ T>0, ∃ u, u 0 = P.initial ∧ P.IsRicciFlowOn T u` is *not* one of the hypotheses; it is genuinely derived (ShortTime.lean:92–96). The card labels it "conditional adapter … the antecedents are the split inputs, not the conclusion" (line 71) and the upstream Topping theorem has the same shape (`ShortTimeExistence.lean:34`). Honest.
  **Nuance (disclosed):** `DeTurckToRicciConversion` is conclusion-shaped modulo the gauge transform `gaugeTransform`; the adapter therefore adds no mathematical content beyond the split architecture. The card says exactly this (U8 "open … the analytic antecedents are missing on both sides", lines 133, 158).
* The I2 partial-discharge claim is exactly what the source proves: `continuousHeatMaximumPrinciple_of_topping` (Slab.lean:241) concludes the D2 conclusion from `ContinuousHeatHypotheses` **plus** `SlabRegularity`, and the card states the literal D2/D7 interface remains statement-only (lines 130, 153); the D2 definition `Poincare/Longrun/PDE/ContinuousInterface.lean:82` `def ContinuousHeatMaximumPrincipleInterface … : Prop := ContinuousHeatHypotheses u a b T → ∀ x ∈ Icc a b, ∀ t ∈ Icc 0 T, u x t ≤ 0` is indeed only a `Prop`, and the D7 `ContinuousHeatMaximumPrincipleConjecture` (`D7/Limit/Blocked.lean:54`) remains statement-only.

## 3.E Over-claim / honesty findings

* **F3-a (mapping table credits D12 modules/declarations absent from the relayed release).** §3 line 39 claims `Poincare.D12.HeatSemigroup` and `Poincare.D12.ParabolicLocal` are mapped; §3.2 line 52 credits "D12 `ParabolicLocal` Duhamel/symbol layer"; line 54 credits "the D12 heat operator `heatOperator` (proved positivity/L∞-L¹ contraction/semigroup in `D12-heat-semigroup-analysis`)"; line 57 credits "D12 `mildToClassicalBridge` / `derivativeLossBarrier`"; line 73 credits "D12 `existsUnique_heatMildSolution`". In this task's relayed release there is **no `Poincare/D12/HeatSemigroup/`, no `Poincare/D12/ParabolicLocal/`** (only `D12/{EntropyVariation,HeatDomain,KappaVariational}`), and `grep -rn "existsUnique_heatMildSolution\|mildToClassicalBridge\|derivativeLossBarrier" <release>/Poincare --include=*.lean` finds only the card's own docstring text in `ShortTime.lean:39–42`; `heatOperator` exists only as the unrelated `Poincare.D7.HeatKernel.HeatSpacetime.heatOperator` (`D7/HeatKernel/Blocked.lean:76`). **Transport limitation rather than fabricated names:** the same declarations do exist in the sibling snapshot `audit/ophis/D13-integrated-kernel-audit/release/Poincare/D12/ParabolicLocal/{GaussianSetup.lean:58, Obligations.lean:208/222 derivativeLossBarrier/mildToClassicalBridge}` and `D12/HeatSemigroup/Basic.lean:53 heatOperator`. The module set still compiles without them, so no code depends on the missing modules — but the card's "D12 objectives mapped" claim is **not verifiable from this task's relayed release**.
* **F3-b (count overstatement, minor).** §1 line 18 and §7 line 115 say the transcription covers "**10** theorems" of upstream `Topping/MaximumPrinciple/Core.lean` (JSON `semantic_class` repeats: "Core.* (10 transcribed Topping maximum-principle theorems)"). Upstream Core.lean has **9** `theorem` declarations (lines 18, 28, 53, 159, 176, 200, 240, 292, 314; the first is `private`), while the local `Core.lean` has 10 audited declarations = those 9 + the **local** variant `nonpos_of_forall_isMax_time_deriv_le_of_pos'` (line 372), which §7 line 116 itself lists as a separate local theorem. The correct statement is "9 transcribed + 1 local variant".
* **F3-c (citation off-by-one, minor).** §4 line 82 cites `conjugatedScalarOperator_eq_quadratic_plus_lower` at "Scalar.lean:265ff"; the declaration is at upstream `ParabolicPDE/Scalar.lean:266`. All other 30+ Topping/MorganTian citations in card 3 are line-exact.
* **F3-d (compile evidence entirely unrelayed — highest-impact gap).** There is **no `longrun/ev-logs/` directory and no `tmp/` directory** in the topping task, so the `8909`/`8912`-job build, the 6/6 `lake env lean` exits, the per-file logs, and the negative control (`/tmp/d13neg/NegativeAudit.lean`) are all **undetermined from the relayed snapshot**. Unlike cards 1 and 2, no Audit-run log is relayed either. The only relayed corroboration of compilation is `checkpoint.json` ("Core.lean": "compiles (exit 0)", …, "Audit.lean": "compiles (exit 0); gate PASS 50/50"), which is the task's own status file, not a build transcript.
* **F3-e (supported).** Forbidden-token scan over `release/Poincare/D13/ToppingAdapter` (7 files) and over the whole `release/Poincare/D13` (13 files) → hard 0 / soft 0. Upstream `Topping` package: 184 files, raw keyword hits = 5, **all in docstrings** (`MaximumPrinciple/Volume.lean:69` "neighborhood", `ParabolicPDE/QuasilinearSectionNemytskii.lean:10`, `RicciFlow/Existence/DeTurckSlice.lean:9`, `…/GaugeFlowGlobalization.lean:55`, `…/Linearisation.lean:527`) — the scanner's comment-aware run gives hard 0. `Topping` contains **0** hits for `entropy`/`Entropy`/`noncollaps`/`reduced volume`/`reduced length`/`reducedVolume`. The `kappa` hits (47) are ordinary coefficient variables in `HigherDerivativeEstimate.lean`, not κ-noncollapsing. "ParabolicPDE/ 66 files" is defensible (68 `.lean` files minus the mapped `Scalar.lean` and `LaplaceBeltrami.lean`).
* **F3-f (byte-identity claim partially verifiable).** §5 line 99 / §9 line 149 claim `diff -rq` clean against `D13-upstream-adapter-audit/release` for "D2–D13 sources". There is no `Poincare/D2` directory in any release (the D2 interface is `Poincare/Longrun/PDE/ContinuousInterface.lean`), and as per F3-a the D12 modules `HeatSemigroup`/`ParabolicLocal` are absent from this release entirely. For the directories that do exist in both trees (`D7,D9,D10,D11,D12,D13`), `diff -rq` is clean — verified.

## 3.F Downstream use of headline constructors (task release sources)

* **Real cross-file consumer inside the module set:** `Slab.lean:224` uses `Core.nonpos_of_forall_isMax_time_deriv_le_of_pos'`; `Slab.lean:207` uses `iteratedDeriv_two_nonpos_of_isLocalMax`, which itself uses `deriv_deriv_nonpos_of_isLocalMax` (`Slab.lean:144–145`); `slab_nonpos_of_lt` is used by `continuousHeatMaximumPrinciple_of_topping` (`Slab.lean:261,299`). So the I2 chain `deriv_deriv_nonpos_of_isLocalMax → iteratedDeriv_two_nonpos_of_isLocalMax → Core.…_of_pos' → slab_nonpos_of_lt → continuousHeatMaximumPrinciple_of_topping` is code-connected.
* **Audit.lean has no kernel-checked `example` consumers** (unlike cards 1 and 2): its "Downstream-use notes" (lines 36–54) are prose, and its only code uses of the module declarations are the 50 `#print axioms` lines (58–107). It is honest about this: line 36 "Downstream-use notes (the uses are inside the module set itself)".
* **No consumers outside `release/Poincare/D13/ToppingAdapter/`**: `grep -rn "ToppingAdapter\." <release> --include=*.lean | grep -v /D13/` → empty; `ReleaseCheck.lean`/`ReleaseClaims.lean`/`lakefile.toml` contain no D13 reference.
* Headline declarations with **no consumer at all** beyond `#print axioms` include `shortTimeRicciFlow_of_splitInputs`, `deTurckLinearisationSymbol_strictParabolic_heatCoefficients`, `heatPrincipalSymbol_eq_localLaplacianCoeff`, `flowSymbol_eq_neg_heatPrincipalSymbol`, `covectorNormSq_euclidean_eq_euclideanNormSq`, `symbol_congruence`, `heatCoefficients_uniformlyParabolic`, `heatCoefficients_pointwiseParabolic`, `uniformlyParabolic_pointwiseParabolic`, `hasVolumeDerivativeOn_of_weightedDensity_local`. The card does not claim external consumers.

## 3.G Verdict (card 3)

**Partially supported.** The honesty of the blocker accounting is supported (no blocker closed; I2 explicitly partial); all *locally declared* names exist with the claimed signatures; transcription faithfulness is real for the sampled Core/Scalar statements; hashes and token scans check out. But: (i) the mapping table credits D12 modules/declarations that are absent from this task's relayed release (they exist only in a sibling snapshot) — F3-a; (ii) **all** compile/negative-control evidence is unrelayed, so "compile-checked" cannot be independently confirmed from the relayed sources — F3-d; (iii) the "10 transcribed theorems" count is wrong (9 transcribed + 1 local variant) — F3-b; (iv) one citation is off by one line — F3-c. No forbidden token, no smuggled conclusion, no invented declaration name.

---

# 4. Cross-cutting answers to the audit questions

**D. Do the cards implicitly claim blocker closure?** No. All three `.md` files and all three `.json` twins state non-closure, and the machine-readable `exact_blockers_closed` field is the empty list `[]` in every JSON:

* card 1 `.md`:10, §8 lines 130–134, §10 line 151; JSON `exact_blockers_closed: []`, `remaining_blockers: ["A1","A2","A3","P1","P5","U1-U12","I1-I8 (D7 inputs)","KV-1..KV-13 …"]`.
* card 2 `.md`:11, §8 line 173 ("**exact_blockers_closed:** none of U1–U9"), §10 line 192; JSON `[]`, `remaining_blockers` lists U1–U5, U9 as open.
* card 3 `.md`:10, §8 line 135 ("`exact_blockers_closed`: **none**"), §10 line 153; JSON `[]`.
* The one non-blocker closure card 2 claims (flat-model KV-10/NCF-9) is explicitly labelled "model-level input closure (not U-blockers)" (line 173) and "honestly labeled model-level, not a U-blocker closure" (line 222).

**Hypothesis-smuggling test.** No declaration in any of the three module sets has the shape `(h : P) : P` or a hypothesis that is literally the conclusion. The two adapters with conclusion-shaped antecedents (card 1's `hkl`, card 3's `gaugeConversion`) are disclosed as conditional adapters and carry independent bridge hypotheses (`hvol`, `hcurv` / `deTurckShortTime`). See §1.D and §3.D.

**E. `sorry`/`axiom`/`admit`/`unsafe`/`native_decide`/`proof_wanted`.** **Zero code-level occurrences** in the task-owned D13 files of all three tasks: scanner run over `release/Poincare/D13` → hard 0 / soft 0 (card 1: 6 files; cards 2/3: 13 files each, which also covers the copied UpstreamAdapter layer). There is therefore no `file:line` to report. All raw grep hits are docstring/`#print axioms` text, which the comment/string-aware scanner excludes. The upstream packages quoted by the cards are likewise clean (Evans 65, MorganTian 573, KleinerLott 11, Topping 184 files; 0 hard/0 soft each).

**F. Downstream use.** No headline constructor of any of the three cards has a consumer **outside its own D13 module set** in the relayed releases (`grep` for the three namespaces outside `D13/` → empty; no D13 reference in `ReleaseCheck.lean`, `ReleaseClaims.lean`, or `lakefile.toml`). Within each module set: card 1 has 4 `Audit.lean` examples (46/55/62/79) plus intra-file chains; card 2 has 4 `Audit.lean` examples (43/52/57/64) plus the `Curvature → Tensoriality` consumers at `Tensoriality.lean:125–126,139,142,153`; card 3 has the real `Core → Slab` chain (`Slab.lean:224,207,144–145,261,299`) but no `Audit.lean` examples. This matches all three cards' own framing (cards 1/2 claim "downstream-use examples"; card 3's Audit.lean explicitly says the uses are inside the module set).

---

# 5. Consolidated F-findings

| id | card | severity | finding | evidence |
| --- | --- | --- | --- | --- |
| F1-a | 1 | medium (unsupported mapping claim) | §3.3 "Gaussian reduced volume … identity via the Evans theorem (rfl-transport)" is not backed by any declaration; `gaussianReducedVolume` occurs 0 times in `release/Poincare/D13` | `.md`:68; `grep -rn gaussianReducedVolume release/Poincare/D13` → ∅; Audit list `.lean`:124–159 has no such theorem |
| F1-b | 1 | low (evidence gap) | `8909`/`8960`-job build counts not relayed; 5 of 6 per-file logs are 0 bytes | `.md`:91,95; `ls longrun/ev-logs` |
| F1-c | 1 | low (evidence gap) | `/tmp/d13neg/NegativeAudit.lean`, `d13AuditFakeAxiom` not relayed; relayed `negcontrol/NegativeControl.lean` is a different D5-era control | `.md`:108; `negcontrol/NegativeControl.lean`:25,27 |
| F1-d | 1 | low (evidence gap) | P5 byte-identity target `D6_weekly_release/release` not relayed | `.md`:134 |
| F2-a | 2 | info (doc) | cross-reference "§6.3" does not exist (§6 is compile evidence) | `.md`:11; `§6` at :131–148 |
| F2-c | 2 | low (evidence gap) | `/tmp/d13mtneg/NegativeAudit.lean`, `d13MtFakeAxiom` not relayed | `.md`:158,214 |
| F2-d | 2 | low (unverifiable) | upstream tree hash `e574480e…` not reproducible with standard sorted-file recipes | `.md`:186,215; my recomputations `26959b57…`, `b53fcbe5…`, `d28f7e49…` |
| F2-e | 2 | low (evidence gap) | "three D12 source worktrees" not relayed (cross-task copies are byte-identical) | `.md`:146,216 |
| F2-g | 2 | low (unverifiable) | pinned-mathlib docstring lines 22–23 not independently checkable (mathlib not relayed) | `.md`:76,219 |
| F2-h | 2 | info (source comment) | `Curvature.lean:45` header names a non-existent `shrinkerFpot_gradientShrinkerPotential_flatRicci` (actual `shrinkerFpot_gradientShrinkerPotentialFlat`, :290); card itself uses the correct name | source line + `.md`:19,60 |
| F3-a | 3 | medium (unverifiable mapping) | `Poincare.D12.HeatSemigroup`, `Poincare.D12.ParabolicLocal`, `existsUnique_heatMildSolution`, `mildToClassicalBridge`, `derivativeLossBarrier`, D12 `heatOperator` absent from this task's release (present in sibling D13-integrated-kernel-audit snapshot) | `.md`:39,52,54,57,73; `ls release/Poincare/D12`; greps |
| F3-b | 3 | medium (count overstatement) | "10 transcribed" upstream Core theorems; upstream has 9, the 10th audited Core declaration is the local variant `nonpos_…_of_pos'` (which §7 itself classifies as local) | `.md`:18,115; JSON `semantic_class`; upstream `Core.lean`:18,28,53,159,176,200,240,292,314; local `Core.lean`:372 |
| F3-c | 3 | low (citation) | `conjugatedScalarOperator_eq_quadratic_plus_lower` cited at "Scalar.lean:265ff", actual 266 | `.md`:82; upstream file:266 |
| F3-d | 3 | high (evidence gap) | **no** relayed build/audit logs or negative control; `8912 jobs`, 6/6 exits, `tmp/*.log`, gate PASS all undetermined from the relayed snapshot (only `checkpoint.json` self-report) | `.md`:93–99,106–107; `ls longrun/` (no ev-logs), `find … -name tmp` → ∅ |
| F3-f | 3 | low (evidence gap) | "diff -rq clean" for "D2–D13" — no `Poincare/D2` exists; D12 HeatSemigroup/ParabolicLocal absent from this release (see F3-a). Verifiable part (D7,D9,D10,D11,D12,D13) is clean | `.md`:99,149 |

**No F-finding of type "declaration does not exist" applies to any locally declared name** in any of the three cards: every Lean identifier the cards present as a local declaration was located in the task's release with the quoted signature. The only missing names are (i) card 3's D12 counterpart references (F3-a, names exist elsewhere in the program snapshot) and (ii) card 1's prose-only reduced-volume "identity" (F1-a, no declaration anywhere, upstream or local, asserting it).

# 6. Upstream citation verification (all cards, against the relayed snapshot)

I checked 126 (file, line, declaration) triples extracted from the three cards plus additional file references. **Every cited declaration exists at the cited file.** Line numbers are exact for 120/126; the six residue cases are matching artifacts, not errors except one:

* `MorganTianLib/Ch04/Tensoriality.lean:58/98` — namespaced `IsCovariantTensorField.congr_slot_apply` / `.vanishesOnZeroSlot`; names occur on the cited lines.
* `KleinerLott/…/SmoothRicciFlow.lean:236` — `induced_distance` is a structure field, occurring on the cited line.
* `Topping/…/ParabolicPDE/Scalar.lean:80` — `ScalarSecondOrderCoefficients.principalSymbol`, declared on the cited line (namespaced).
* `Topping/…/ParabolicPDE/Scalar.lean:252` — `IsPositiveDefinite.congruence`, namespaced, on the cited line.
* `Topping/…/ParabolicPDE/Scalar.lean:265ff` — actual 266 (F3-c).

Additional file-level references verified to exist: `Ch05/{PointedGH,PointedGHNetCharacterization,MarkedGHExtraction,Precompactness}.lean`, `Ch02/EpsilonNeck.lean`, `Ch01/{CurvatureTensor,PointwiseCurvature,CurvatureOperator,Geodesics,GlobalExp,ExpLocalDiffeo,ExpMinimizingLocalDiffeo,ParallelIsometry,ParallelTransfer,BishopGromovBall,BishopGromovManifold,ComparisonFunctions,ComparisonGeometric,ComparisonMinimizing,ExpJacobiDensity,MinimizingSegment,MinimalGeodesicNoConjugate,Einstein}.lean`, `Ch04/{TensorParallelTransport,LeviCivitaTensorTransport,Tensoriality,SecondCovLocality}.lean`, `Ch03/RicciFlow/{Basic,Soliton,PDE/LocalExistence,PDE/DeTurckPicard}.lean`, `KleinerLott/…/{FlowData,Noncollapsing,SmoothRicciFlow,MetricFamily,PointSelection}.lean`, `DoCarmo/…/{DoCarmoCh2,DoCarmoCh4Ricci}.lean`, `Topping/…/{MaximumPrinciple/Core,MaximumPrinciple/Volume,ParabolicPDE/Scalar,ParabolicPDE/LaplaceBeltrami,Riemannian/Variation,Riemannian/VariationScalar,RicciFlow/Evolution,RicciFlow/Existence/ShortTimeExistence}.lean`, `CaoZhu/blueprint/src/chapters/CZ04_ReducedVolume.tex`, plus the `shared` package referenced in card 1's next-dependency list. Exact-quote checks: card 1's KleinerLott predicates are verbatim; card 2's `IsGradientShrinkerPotential`/`solitonScale`/`riemannCurvature` citations resolve to the claimed lines; card 3's `LocalExistence.lean:9-12` quote "No existence claim is hidden in either structure" is verbatim at `LocalExistence.lean:10`.

# 7. Overall verdicts

| card | verdict | most important F-findings | undetermined from relayed snapshot |
| --- | --- | --- | --- |
| D13-upstream-adapter-audit | **claims supported** (one unbacked mapping row) | F1-a (reduced-volume "rfl-transport" has no declaration) | F1-b job counts, F1-c negative control, F1-d P5 target, D6 comparisons |
| D13-morgan-tian-adapter-plan | **claims supported** | F2-a broken §6.3 reference (minor) | F2-c negative control, F2-d tree hash, F2-e source worktrees, F2-g mathlib docstring |
| D13-topping-ricci-adapter-plan | **partially supported** | F3-a D12 counterpart modules absent from this release; F3-b "10 transcribed" overcount; F3-d all compile evidence unrelayed | F3-d compile/gate/negative control; F3-a D12 modules |
