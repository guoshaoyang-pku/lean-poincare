# D13-deturck-shorttime-producer — result card

- **Task id:** `D13-deturck-shorttime-producer`
- **Stage / lane:** D13 / builder
- **Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/D13-deturck-shorttime-producer`
- **Model:** `deepseek-v4-pro` (configured preset; never switched)
- **Generated (UTC):** 2026-09-11T06:00:00Z (elapsed ≈ 1.9 h of the 4 h invocation)
- **Toolchain:** `leanprover/lean4:v4.34.0-rc2` (binary `Lean 4.34.0-rc2, commit 6a10ac8c22be`); mathlib `7974e751bece493b6ff508039423ca9fa2452fa8`
- **Upstream snapshot:** `third_party/frenzymath/Poincare-Conjecture` = `frenzymath/Poincare-Conjecture` @ `bb91a091f0b968f8bbe8d861e025a88d82b161be` (reference-only, per `docs/UPSTREAM-INTEGRATION.md`)
- **Verdict:** **TASK_DONE for the D13 milestone** — the missing analytic antecedent of Hamilton/DeTurck short-time existence is produced: a compile-checked, axiom-audited **`RicciDeTurckPicardModel` producer from an arbitrary smooth metric** (`Poincare.D13.DeturckProducer`, 6 files, 1888 lines, 83 audited declarations), building on the D12 Banach-fixed-point semilinear mild solution, the D9 DeTurck symbol cancellation, and the D13 split architecture. **U8 is not claimed closed**: the producer supplies the analytic antecedent (model + strict-parabolicity certificate + D12 fixed-point assembly + truncation lemma + conditional end-to-end chain); the short-time existence theorem itself remains the named downstream obligation. This card requests independent acceptance of the producer module only and claims nothing about Perelman.

---

## 1. What was built

| file | lines | role |
| --- | --- | --- |
| `SmoothMetric.lean` | 177 | **the producer input**: `SmoothMetricData n` — an *arbitrary smooth metric* in global coordinates on `ℝⁿ`: symmetric `C²` matrix field with uniform quadratic bounds (`lower · ‖v‖² ≤ vᵀg(x)v ≤ upper · ‖v‖²`, `0 < lower ≤ upper`). Invertibility (`det_ne_zero`, `isUnit_det`, `inv_transpose`) proved from coercivity; `flatSmoothMetric n` non-vacuity witness (`lower = 1/2`, `upper = 2`) |
| `SymbolMatrix.lean` | 488 | **the D9 symbol layer at the matrix level + the strict-parabolicity certificate for an arbitrary metric**: index forms `ricciSymbolMat`/`deTurckFieldSymbolMat`/`lieSymbolMat`/`laplacianSymbolMat`; the D9 cancellation `flowSymbolMat : σ(-2Ric + L_W g) = -|ξ|²_g · Id` and `deTurckLinSymbolMat_eq_smul : σ(2Ric - L_W g) = |ξ|²_g · Id` for an *arbitrary* symmetric positive-definite matrix; elementary Cauchy–Schwarz `form_cauchySchwarz` (discriminant argument); `covectorNormSqMat_pos` (D9 `covectorNormSq_pos` for arbitrary metrics); **`symbolLowerBound : (1/upper)·‖ξ‖² ≤ |ξ|²_g`** (quantitative, uniform); **`producerStrictParabolic`** (0 < pairing for ξ ≠ 0, h ≠ 0) and **`producerStrictParabolic_lower`** (uniform lower bound with constant `1/upper`); `deTurckSymbolMat_injective` (ellipticity) |
| `Reaction.lean` | 465 | **the reaction in coordinates**: `christoffelMat`, `christoffelLowered`, `ricciTensorMat` (classical formula), `lieDerivativeCorrectionMat`, `deTurckReactionMat = -2Ric + L_W g`; `ricciTensorMat_zero_of_flatJets` (constant metrics are Ricci-flat); `deTurckReaction_at_initial` (reaction at the background = `-2 Ric(g₀)`, the actual Ricci-flow initial velocity); `deTurckReaction_flat_zero`; **explicit jet bounds** `abs_ricciEntry_le` (`|Ric_ij| ≤ 2n²KC₂ + (9/2)n⁴K²C₁²`), `abs_lieCorrectionEntry_le`, `deTurckReaction_entry_le` (entrywise jet-bound hypotheses `K, C₁, C₂, C_W, C_dW`) |
| `PicardModel.lean` | 324 | **the model + producer + assembly**: `RicciDeTurckPicardModel` (transcription of upstream `MorganTianLib.RicciDeTurckPicardModel` over the local layers: D12 `DuhamelSetup` + symbol field tied to `deTurckLinSymbolMat` + strict-parabolicity field); **`RicciDeTurckPicardModel.of_metric` — the producer** (the certificate proved from the metric alone); `existsUnique_mildSolution_of_model` / `mildSolution_of_model{,_duhamel_eq,_initial,_continuous}` (D12 Banach fixed point applied); `clampC` (+1-Lipschitz, retraction onto `[-C,C]`), `truncatedSetup`, `duhamelMap_congr_of_projection`, **`mildSolution_of_truncated`** (invariant-box truncation lemma); `MildClassicalOutput` (named mild-to-classical bridge), `deTurckShortTimeExistence_of_classicalOutput`, **`ricciFlow_of_model`** (conditional end-to-end: bridge + proved D7 conversion + D13 assembly ⇒ genuine short-time Ricci flow) |
| `FlatInstance.lean` | 168 | **the flat instance / downstream use of D12**: `flatPicardModel` (producer on `flatSmoothMetric` with the D12 Gaussian semigroup); `flatPicardModel_duhamel_eq_gaussianSetup` (rfl); **`flatMildSolution_eq_heatMildSolution`** (the produced mild solution IS the D12 `heatMildSolution` — constructed downstream checked use); `flatMildSolution_duhamel_eq`/`_initial`; `flatCertificate_positive`; `flatDeTurckLinSymbol_eq_euclideanNormSq_smul` (flat symbol = D13 `euclideanNormSq · Id`) |
| `Audit.lean` | 266 | 83 `#print axioms` transcripts + fail-closed `Lean.collectAxioms` gate |

Namespace `Poincare.D13.DeturckProducer.{SmoothMetricData, SymbolMatrix, Reaction, PicardModel, FlatInstance}`. Dependencies: the accepted D12 `ParabolicLocal` modules, D9 `DeTurck.SymbolModel`, D7 `ShortTime`, D13 `ToppingAdapter` (all byte-identical copies of the accepted scaffolds, `diff -rq` clean), + mathlib.

## 2. Compile evidence

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd release
for f in SmoothMetric SymbolMatrix Reaction PicardModel FlatInstance Audit; do
  lake build Poincare.D13.DeturckProducer.$f      # 6/6 exit 0
done
lake build Poincare.D13.DeturckProducer.Audit Poincare.D12.ParabolicLocal.AxiomAudit \
  Poincare.D13.ToppingAdapter.Audit               # exit 0 (full D2–D13 dependency closure, 8928 jobs)
```

* final build of the producer audit: `Build completed successfully (8928 jobs)`, exit 0;
* full joint build with the D12 ParabolicLocal axiom audit and the D13 ToppingAdapter audit: exit 0;
* the D2/D7/D9/D10/D11/D12/D13 sources were not modified: only the six files under `release/Poincare/D13/DeturckProducer/` are new (the dependency closure is byte-identical to the accepted D12/D13 scaffolds).

## 3. Axiom evidence (kernel trust, separate from compilation)

| item | value |
| --- | --- |
| audited declarations | **83 / 83** — all depend only on `[propext, Classical.choice, Quot.sound]` (or on none) |
| gate result | `DeturckProducerAxiomCheck: PASS — all 83 declarations of the D13 DeturckProducer module set depend only on [propext, Classical.choice, Quot.sound]` (build log, exit 0) |
| gate mechanism | the same fail-closed `run_cmd` + `Lean.collectAxioms` logic as the accepted D13 ToppingAdapter audit; any unapproved axiom aborts the build |
| forbidden tokens | `input/d5-tools/scan_forbidden.py` over `release/Poincare/D13/DeturckProducer`: **0 hard / 0 soft** matches |
| keyword scan | no `sorry`, `axiom`, `admit`, `unsafe`, `native_decide`, `proof_wanted` in any of the six new files |

## 4. Semantic classification

| declaration group | class | justification |
| --- | --- | --- |
| `SmoothMetricData` | **model** (def, all hypotheses explicit) | the local model of "an arbitrary smooth metric with bounded geometry"; fields are regularity/bounds hypotheses, none asserts existence of a flow |
| `SmoothMetricData.{form_pos, det_ne_zero, isUnit_det, inv_transpose}`, `flatSmoothMetric` | local proved theorem / definition | invertibility and positivity from coercivity; explicit flat witness |
| `SymbolMatrix.{metricSharpMat … laplacianSymbolMat}`, `{ricciSymbolMat_sub_half_lieSymbolMat*, flowSymbolMat, deTurckLinSymbolMat*}`, symmetry lemmas | **upstream D9 identity transcribed to the coordinate model, locally re-proved** | the D9 `SymbolModel` content (whose proof is the same index-algebra computation) for an arbitrary matrix metric; the D9 file:line correspondences are `Poincare.D9.DeTurck.SymbolModel` `ricciSymbol`/`lieSymbol`/`laplacianSymbol`/`flowSymbol` |
| `form_cauchySchwarz` | local proved theorem | elementary analytic ingredient (discriminant argument for symmetric coercive forms) |
| `SmoothMetricData.{covectorNormSqMat_pos, symbolLowerBound, producerStrictParabolic, producerStrictParabolic_lower, deTurckSymbolMat_injective}` | **local proved theorem — the strict-parabolicity certificate from the arbitrary metric** | uses only the metric's uniform bounds; the D9 `flowSymbol` + `covectorNormSq_pos` content at arbitrary-metric level |
| `Reaction.{christoffelMat, christoffelLowered, ricciTensorMat, lieDerivativeCorrectionMat, deTurckReactionMat}` | definitions (coordinate reaction) | classical formulas |
| `Reaction.{christoffelMat_zero_of_flat, christoffelLowered_zero_of_flat, ricciTensorMat_zero_of_flatJets, lieDerivativeCorrectionMat_zero_of_flat, deTurckReaction_at_initial, deTurckReaction_flat_zero}` | local proved theorem | coordinate sanity + the reaction's initial value is `-2 Ric(g₀)` |
| `Reaction.{abs_ricciEntry_le, abs_lieCorrectionEntry_le, deTurckReaction_entry_le}` | **local proved theorem, expanded hypotheses** (entrywise jet bounds `K, C₁, C₂, C_W, C_dW`, `[NeZero n]`) | the quantitative quasilinear-barrier content: the reaction is bounded on bounded jets with explicit polynomial constants |
| `RicciDeTurckPicardModel` | **conditional interface (structure)** | transcription of upstream `MorganTianLib.RicciDeTurckPicardModel` (`DeTurckPicard.lean:84`); fields are D12 analytic data + certificates, none asserts existence |
| `RicciDeTurckPicardModel.of_metric` | **the producer** (def; certificate field proved from the metric) | takes an arbitrary `SmoothMetricData` + the named analytic inputs (semigroup/reaction `DuhamelSetup`) and returns the model with the strict-parabolicity certificate **proved** from the metric |
| `existsUnique_mildSolution_of_model`, `mildSolution_of_model*` | **proved theorem, expanded hypotheses** (`M·L·T < 1` etc., the D12 hypotheses) | the D12 `existsUnique_mildSolution` applied to the produced model |
| `clampC*`, `truncatedSetup`, `duhamelMap_congr_of_projection`, `mildSolution_of_truncated` | local proved theorem | the classical truncation/invariant-box lemma (the box-invariance remains the named obligation) |
| `MildClassicalOutput` | **named obligation (structure)** | the remaining D12 mild-to-classical bridge, stated as explicit data, never assumed |
| `deTurckShortTimeExistence_of_classicalOutput`, `ricciFlow_of_model` | **conditional adapter** (typed implication; antecedents = the bridge + the *proved* D7 conversion, never the conclusion) | consumes D13 `shortTimeRicciFlow_of_splitInputs` and D7 `matrixProblem_deTurckToRicciConversion` |
| `FlatInstance.*` | local proved theorem / definition | the flat producer output IS the D12 Gaussian setup; `flatMildSolution_eq_heatMildSolution` is the constructed downstream checked use of D12 |

## 5. The produced chain (what this task delivers for U8)

1. **input**: an arbitrary smooth metric `G : SmoothMetricData n` (uniformly elliptic, `C²`, bounded geometry);
2. **certificate**: `producerStrictParabolic`/`producerStrictParabolic_lower` — the linearized DeTurck operator of `G` is **uniformly strictly parabolic**, with constants depending only on `G.lower`/`G.upper` (proved via the D9 symbol cancellation + coercivity + an elementary Cauchy–Schwarz);
3. **model**: `RicciDeTurckPicardModel.of_metric` assembles the D12 Duhamel data + the certificate;
4. **fixed point**: `existsUnique_mildSolution_of_model` (D12 Banach contraction) — short-time mild solution of the linearized-plus-reaction problem;
5. **quasilinear repair**: `mildSolution_of_truncated` — the clamped reaction is globally Lipschitz, and a box-valued mild solution of the truncated problem solves the true problem (the box-invariance is the named remaining obligation, matching the D12 `derivativeLossBarrier` quantification);
6. **end-to-end (conditional)**: `ricciFlow_of_model` — model + the named `MildClassicalOutput` bridge ⇒ D7 `DeTurckShortTimeExistence` ⇒ (proved D7 conversion + D13 assembly) ⇒ a genuine short-time Ricci flow;
7. **flat check**: `flatPicardModel` reproduces the D12 Gaussian setup exactly (`flatMildSolution_eq_heatMildSolution`).

## 6. Upstream correspondence (per `docs/UPSTREAM-INTEGRATION.md`)

* `RicciDeTurckPicardModel` mirrors `MorganTianLib.RicciDeTurckPicardModel` (`formalized-sources/MorganTian/MorganTianLib/Ch03/RicciFlow/PDE/DeTurckPicard.lean:84-118`): contraction/seed/lifespan upstream ↔ `DuhamelSetup` + `existsUnique_mildSolution_of_model` locally; the reconstruction/source fields upstream ↔ the D12 Duhamel identity locally.
* **Decisive**: upstream has **no** producer — "No upstream declaration constructs a `RicciDeTurckPicardModel` from an arbitrary initial metric" (recorded in the D13 adapter plan §3.4). The producer delivered here is the local construction of that missing antecedent; its upstream counterpart remains an upstream source claim requiring the Lean 4.32.1 build.
* The strict-parabolicity certificate corresponds to upstream `canonicalRicciDeTurckStrictParabolic` (`…/PDE/LocalExistence.lean:42-64`) and is proved locally for arbitrary metrics (the upstream one is the flat-model canonical certificate; the D13 plan's `localDeTurckStrictParabolic` is its local flat transcription — the flat correspondence is `FlatInstance.flatDeTurckLinSymbol_eq_euclideanNormSq_smul`).
* The split assembly corresponds to `Topping.exists_localRicciFlow_of_splitHamiltonGauge` (`Topping/RicciFlow/Existence/ShortTimeExistence.lean:34`), consumed via the D13 `shortTimeRicciFlow_of_splitInputs`.

## 7. Expanded hypotheses (every unproved input, explicit)

* `SmoothMetricData`: `g`, `symm`, `smooth : ContDiff ℝ 2 g`, `lower`, `lower_pos`, `coercive`, `upper`, `upper_pos`, `boundedAbove` — all about the metric, none about any flow;
* the model's analytic inputs: `S`/`F`/`u₀` with the D12 `DuhamelSetup` hypotheses (`smap_continuous`, `smap_norm_le ≤ M`, `F_lipschitz L`) and the contraction hypothesis `M · L · T < 1`;
* the reaction bound theorems: entrywise jet bounds `|g^{kl}| ≤ K`, `|∂g| ≤ C₁`, `|∂²g| ≤ C₂`, `|W| ≤ C_W`, `|∂W| ≤ C_dW`, `[NeZero n]`;
* the truncation lemma: `LipschitzWith L' (F ∘ r)` (the box-Lipschitz constant, the quantified quasilinear input) and the box-invariance of the mild solution;
* the end-to-end theorem: the named `MildClassicalOutput` bridge and the proved D7 matrix conversion.

## 8. Blockers — exact accounting

| blocker | D13-deturck-shorttime-producer action | status |
| --- | --- | --- |
| **U8** (Hamilton/DeTurck short-time existence) | the analytic antecedent is now **produced**: arbitrary-metric strict-parabolicity certificate (proved), the Picard model + producer, the D12 fixed-point assembly, the truncation lemma, and the conditional end-to-end chain; the flat instance is the D12 Gaussian setup | **open** — the antecedent is delivered, not the theorem. The remaining gap is exact: (i) the evolution family of the linearized DeTurck operator of an arbitrary metric (variable-coefficient heat semigroup — no such object in the pinned mathlib), (ii) the box-Lipschitz constant + box-invariance a priori estimate (quasilinear barrier, quantified by D12's `derivativeLossBarrier_holds` and by `deTurckReaction_entry_le` here), (iii) the mild-to-classical bridge (D12's remaining named obligation) |

`exact_blockers_closed`: **none** (empty list — U8 is not closed; its analytic antecedent is produced, which was this task's objective).

## 9. Source hashes (fresh, sha256)

| file | sha256 |
| --- | --- |
| `release/Poincare/D13/DeturckProducer/SmoothMetric.lean` | `32b4a538ba5719399c398700ce36a49dcd347ea5067962526cd8a7a2dcedd6ab` |
| `release/Poincare/D13/DeturckProducer/SymbolMatrix.lean` | `eb8c4e4d4061cee7b78164772c3f58a2d6bfedcea712c2cd76dbb42d802ed28d` |
| `release/Poincare/D13/DeturckProducer/Reaction.lean` | `22de561a22b9c7d1835181f8613561b97fcb4f58d107b91d26f79a0f5d1af754` |
| `release/Poincare/D13/DeturckProducer/PicardModel.lean` | `61a2b0316ce8447e022f5b0df3f97bcfaed04a1fc8f4b165a067855c3ec52349` |
| `release/Poincare/D13/DeturckProducer/FlatInstance.lean` | `721a87cf1f04709ef885a76a859997921aed35283bf21970a60e17e1f3a8da7e` |
| `release/Poincare/D13/DeturckProducer/Audit.lean` | `413d2a5340286a171125214def13c3118e68c9950d4b945d4d5cf275107f07f1` |

No D2/D7/D9/D10/D11/D12/D13 source was modified: only the six files under `release/Poincare/D13/DeturckProducer/` are new; the copied scaffolds are byte-identical to the accepted D12/D13 trees.

## 10. Remaining blockers and next dependency requests

**Remaining:** U8 (open; antecedent produced), plus the unchanged sibling blockers (U6, U7, I2 etc. are outside this task's scope).

**next_dependency_requests** (machine-readable in the JSON card):
1. A variable-coefficient heat semigroup for the linearized DeTurck operator of an arbitrary bounded-geometry metric on `ℝⁿ` (symbol `|ξ|²_{g(x)} · Id`, now certified uniformly strictly parabolic) — the one missing analytic field of the produced model for non-flat metrics.
2. The quasilinear box-Lipschitz constant and the box-invariance a priori estimate (the inputs named by `deTurckReaction_entry_le` and `mildSolution_of_truncated`), or a weighted-space/parabolic-Hölder scheme producing them.
3. The mild-to-classical bridge (`MildClassicalOutput`) from the produced mild solution — the last step to discharge the D7 `DeTurckShortTimeExistence` statement through `ricciFlow_of_model`.
4. Upstream build of MorganTian/Topping at Lean 4.32.1 to upgrade the upstream source claims (§6) to upstream compiled theorems.

TASK_DONE — card: `longrun/results/D13-deturck-shorttime-producer.md` (this file); machine-readable twin: `longrun/results/D13-deturck-shorttime-producer.json`. This card requests independent acceptance of the producer module set only; it does not claim U8 is closed, does not claim Hamilton/DeTurck short-time existence is proved, and does not count upstream sources as local proof evidence.
