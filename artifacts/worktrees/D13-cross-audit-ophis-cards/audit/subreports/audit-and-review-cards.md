# Adversarial audit of two fetched ophis-gpu D13 result cards

Auditor: independent adversarial audit (this worktree is read-only except for this one file).
Date of audit: evidence frozen at the fetched artifact state (ophis-gpu cards dated 2026-09-11/12).

Cards audited (abbreviations used throughout):

- **C1** = `audit/ophis/D13-cross-audit-360-cards/longrun/results/D13-cross-audit-360-cards.md`
  (+ `.json`, same stem) — "adversarial cross-audit result card", task `D13-cross-audit-360-cards`.
- **C2** = `audit/ophis/D13-critical-path-review/longrun/results/D13-critical-path-review.md`
  (+ `.json`, same stem) — "critical-path review", task `D13-critical-path-review`.

Line numbers are 1-based and refer to the `.md` of each card unless a different file is named.

## 0. What is checkable in this worktree (evidence availability)

Local 360-1 sibling sources present as full worktrees (producer `release/` trees and result cards):

| worktree | card JSON | producer D12 sources |
|---|---|---|
| `../D12-connection-curvature` | `longrun/results/D12-connection-curvature.json` (119 entries) | `release/Poincare/D12/ConnectionCurvature/*` |
| `../D12-volume-ibp` | `longrun/results/D12-volume-ibp.json` | `release/Poincare/D12/VolumeIBP/*` |
| `../D12-spectral-sobolev` | `longrun/results/D12-spectral-sobolev.json` | present |
| `../D12-semantic-ledger` | `longrun/results/D12-semantic-ledger.json` | `release/Poincare/Longrun/*`, `audit_probes/` |
| `../D12-tensor-maximum-bochner` | `longrun/results/D12-tensor-maximum-bochner.json` | `release/Poincare/D12/TensorMaximumBochner/*` |

Not present as worktrees locally: `D12-comparison-geodesics`, `D12-geometric-compactness`,
`D12-surgery-recognition`, `D12-triangulation-topology`. However, the **relayed snapshot** inside
`audit/ophis/D13-critical-path-review/release/Poincare/D12/` contains the source trees of
`ComparisonGeodesics`, `GeometricCompactness`, `SurgeryRecognition`, `TriangulationTopology`,
`TensorMaximumBochner`, `VolumeIBP`, `SpectralSobolev`, `SemanticLedger`, `ConnectionCurvature`,
`HeatDomain` (etc.). Source-level claims about those cards can therefore be checked here at the
source level, but **not** their producer result-card JSON, their hash inventories, or any
`audit360/` staging artifact.

Not present anywhere in the fetched ophis trees: `audit360/` (all `A3Probe.lean`,
`A3FullAudit.lean`, `A3KindAudit.lean`, `A3Extra*/`, `a3d2d3/A3D2D3*.lean`, `pkgs/`, `logs*/`,
`*.json` evidence artifacts referenced by C1). Consequently every C1 claim whose only evidence is
one of those kernel probes is **UNDETERMINED here** (absent artifact), and I say so explicitly.
Also absent: the `D12-tensor-maximum-bochner` / `D12-triangulation-topology` producer worktrees *on
the ophis host* (the card's rounds 1–10 claim), which is not observable from here.

Card 2's own evidence bundle **is** present: `audit/ophis/D13-critical-path-review/audit-evidence/`
(logs, gate replay, hashes, summary) and `.../release/Poincare/D13/CriticalPathReview/` (8 modules).

---

# Card 1 — `D13-cross-audit-360-cards`

## 1. Identity and self-declared state

- C1:10–12 `**Status:** `TASK_DONE` … — **9/9 cards independently re-verified.**`
- C1:32–34 `The audit does **not** close the producer-side blocker **B1** … and does **not** claim Perelman.**`
- C1:66–68 the stale round-10 `TASK_BLOCKED` sentence is declared `**superseded and stale**`.
- C1:2369 end of file. JSON agrees: `status: TASK_DONE`, `scope.cards_available_and_audited: 9`,
  `final_state.cards_not_auditable: []`.

## 2. A. Findings census (every numbered finding / claim about other cards)

Legend: **CONF** = confirmed against a local source; **REF** = refuted; **UND** = undetermined
(artifact absent); **CONF(src)** = confirmed at source level but the card's kernel probe artifact is
absent, so the card's own instrumented proof cannot be re-run here.

### 2.1 Findings F1–F15 (C1 §7, lines 255–342)

| id | verbatim claim (C1 line) | checkable here? | verdict + local evidence |
|---|---|---|---|
| **F1** | "73/119 `proved_declarations` entries carry file-derived namespace segments that do not exist in the compiled sources (e.g. `…ConnectionCurvature.ChartLeviCivita.ChartMetricCoefficients.christoffel_symm` vs the real `…ConnectionCurvature.ChartMetricCoefficients.christoffel_symm`). Every declaration exists (unique short-name match) and compiles; the card inventory is wrong, the mathematics is not." (C1:255–259) | yes | **CONF.** Independent parse of `../D12-connection-curvature/longrun/results/D12-connection-curvature.json` (119 entries) against `release/Poincare/**/*.lean`: 45 exact, **73** unique-short-name ("over-qualified") matches, 1 needing a namespace rule. Real declaration: `../D12-connection-curvature/release/Poincare/D12/ConnectionCurvature/ChartLeviCivita.lean:86` (`namespace ChartMetricCoefficients`), `:102` (`theorem christoffel_symm (k i j : ι) : christoffel c k i j = christoffel c k j i`). The card entry's extra `ChartLeviCivita.` segment is not a source namespace. |
| **F2** | "2/9 declared names live in `audit_probes/D12RealModuleProbe.lean` outside the release package. Replayed and audited here; both are genuine and within the allowed cone." (C1:260–262) | yes | **CONF.** `../D12-semantic-ledger/longrun/results/D12-semantic-ledger.json` `proved_declarations` has 9 entries; exactly 2 carry `"file": "audit_probes/D12RealModuleProbe.lean"` (`real_initialCondition_specializes`, `realField_unsatisfiable_by_gaussian`). Those theorems are at `../D12-semantic-ledger/audit_probes/D12RealModuleProbe.lean:79` and `:92`. |
| **F3** | "`D12-tensor-maximum-bochner` and `D12-triangulation-topology` have no worktree, no release package, no card and no Lean module anywhere on this host (exhaustive filename search, `.lake` pruned). They are `remote_owned` queue entries only. They are **not refuted** — they are **not auditable here**." (C1:263–266) | ophis-side only | **UND** (the ophis filesystem is not in the artifact). Note: this is a rounds-1–10 statement; C1 itself supersedes it (C1:1917–1928, 1567–1577, 2098–2109). Locally the sibling `../D12-tensor-maximum-bochner` worktree **does** exist with a card (`status: partial_blocked`, `terminal_marker: TASK_BLOCKED`), exactly as C1's round-11 arrival report describes (C1:1865–1870). |
| **F4** | "The model non-vacuity witnesses `euclidModel_singular_comparison_ge` and `euclidModel_bishopGromov` are reflexive instances (`m ≤ m`; `V R/V R ≤ V r/V r`). They establish hypothesis satisfiability but do not exercise a strict comparison." (C1:267–271) | yes (relayed source) | **CONF.** `audit/ophis/D13-critical-path-review/release/Poincare/D12/ComparisonGeodesics/ModelEuclidean.lean:177–179` concludes `euclidModelM d t ≤ euclidModelM d t`; `:206–210` concludes `radialVolume (euclidModelA d) R / radialVolume (euclidModelA d) R ≤ radialVolume (euclidModelA d) r / radialVolume (euclidModelA d) r`. Both sides are the same term. |
| **F5** | "`axiom negativeControl : False` is declared in the task's own audit module, documented in-file, unused in every cone. Recorded, not a violation." (C1:272–274) | yes | **CONF.** `../D12-volume-ibp/release/Poincare/D12/VolumeIBP/Audit.lean:40` `axiom negativeControl : False`; the file's sha256 is `584b2e69…f968`, exactly the card's recorded `source_hashes["Audit.lean"]`. Sub-note: C1:1196 cites this at line **36** while C1:903 cites line **40**; the on-disk line is **40** — the §14.5 citation is wrong (see §3, defect D5). |
| **F6** | "Queue/checkpoint state disagrees with card verdicts: connection-curvature and volume-ibp checkpoints are `in_progress` while their cards say TASK_DONE; geometric-compactness is `in_progress`; semantic-ledger is `gate_failed` in the queue with A1/A2/A3/P1/P5." (C1:275–278) | partly | **CONF (partly).** `../D12-connection-curvature/checkpoint.json` → `"status": "in_progress"`; `../D12-volume-ibp/checkpoint.json` → `"status": "in_progress"`; both cards say `TASK_DONE*`. `../D12-semantic-ledger/checkpoint.json` has `phase: "complete — result card written; independent acceptance pending"` and no `gate_failed` token is findable in the local producer tree (`grep -r gate_failed` empty) → the `gate_failed` clause is **UND** (dispatcher-side state, absent). |
| **F7** | "`chartMetricCompatible_form` / `chartTorsionFree_form` are algebraic identities whose right-hand sides are supplied coefficient data (`dFormOf`, zero coordinate bracket); the genuine Fréchet-derivative statements are `nabla_metricCompatible` / `nabla_torsionFree`, both present and audited." (C1:279–283) | yes | **CONF.** Form level: `../D12-connection-curvature/release/Poincare/D12/ConnectionCurvature/ChartLeviCivitaForm.lean:294` `theorem chartMetricCompatible_form (X Y Z : ι → ℝ) : …` and `:325` `theorem chartTorsionFree_form (X Y : ι → ℝ) : …`. Smooth level: `ChartLeviCivitaSmooth.lean:393` `theorem nabla_torsionFree …` and `:476` `theorem nabla_metricCompatible …`. |
| **F8** | "The ledger note `L-D2-LEVI-CIVITA` calls `LeviCivitaExistenceStatement` **and** `CovariantDerivativeCurvatureStatement` 'BLOCKED Props'. The second is unconditionally inhabited by the zero tensor (`A3D2D3.covariantCurvatureStatement_trivial`), so the label is wrong; the first is stale, since `Poincare.D12.ConnectionCurvature.leviCivitaExists` is a compiled proof … The entry is nonetheless classified `genuine-general`." (C1:284–291) | partly | **CONF (src).** Note verbatim in `../D12-semantic-ledger/manifest/d12-semantic-ledger.json` `main_chain_theorems[23].note`: "LeviCivitaExistenceStatement and CovariantDerivativeCurvatureStatement are BLOCKED Props (blocker I1)."; `semantic_class: "genuine-general"`. `CovariantDerivativeCurvatureStatement` is `def … (_cov : CovariantDerivative …) : Prop := ∃ κ : PointwiseCurvature I M, (∀ …, κ x X Y Z = - κ x Y X Z) ∧ (∀ …, κ x X Y Z + κ x Y Z X + κ x Z X Y = 0)` (`../D12-semantic-ledger/release/Poincare/Longrun/Geometry/LeviCivitaBlocked.lean:230–238`) with `_cov` unused and `PointwiseCurvature` an `abbrev` to a function type (`Stage1/RiemannAdapter.lean:87`), so `κ := 0` inhabits it unconditionally — trivial, as claimed. `leviCivitaExists` is `../D12-connection-curvature/release/Poincare/D12/ConnectionCurvature/MilnorLeviCivita.lean:142`. The named probe `A3D2D3.covariantCurvatureStatement_trivial` is **UND** (absent). |
| **F9** | "The ledger note `L-D2-ODE-SCALAR-MONO` says `scalarCurvature_monotone_of_bridge` is 'conditional on the **uninhabited** `TensorRicciFlowODEBridge`'. The bridge is inhabited (`A3D2D3.bridgeWitness`) and every inhabitant with `0 < T` has `ricci = 0` hence `traj = 0` on `[0,T]` …: the correct defect is **degeneracy**, not uninhabitedness. Separately, `L-D3-ENTROPY-CERTIFICATES` lists the projections `LinearDecayCertificate.decay` / `.rate_pos` among checked decay certificates, but the structure is provably empty (F-A3-1)." (C1:292–299) | partly | **CONF for the note text and the listing; UND for the degeneracy theorem.** Note verbatim: `main_chain_theorems[26].note` = "scalarCurvature_monotone_of_bridge is conditional on the uninhabited TensorRicciFlowODEBridge (blocker I3).", `semantic_class: "genuine-general"`. `L-D3-ENTROPY-CERTIFICATES` (`main_chain_theorems[27]`) lists `…LinearDecayCertificate.decay` and `…LinearDecayCertificate.rate_pos`. `LinearDecayCertificate` (`../D12-semantic-ledger/release/Poincare/Longrun/Entropy/Certificate.lean:261–270`) has fields `rate_pos : 0 < rate` and `decay : ∀ t, 0 ≤ t → (E t).F ≤ (E 0).F - rate * t` with `EntropyData.F : ℝ` (`Functional.lean:~66`), so it is unsatisfiable by the Archimedean property — the emptiness claim is sound at statement level. The bridge (`CurvatureODE/Bridge.lean:135–157`) has an explicit field `realization : TensorRicciFlowODERealization …` that bundles the trivially-inhabited `CovariantDerivativeCurvatureStatement` plus `MetricFamilySolvesRicciFlow`, `MetricCurvatureShadow`, `DiffusionVanishes`; the module docstring itself says "No inhabitant of the bridge is constructed" (Bridge.lean:34). A degenerate inhabitant (zero curvature/metric, zero trajectory, `F` with zero reaction) is constructible from the definitions, but the card's stronger theorem "**every** inhabitant with `0 < T` has `ricci = 0`" does **not** follow from the interface as I read it, and `A3D2D3.bridgeWitness` / `bridge_forces_zero_traj` are absent → the degeneracy half is **UND**. |
| **F10** | "`missingSphereRecognitionAlgorithm` is trivially true via classical decidability and captures no algorithm; `SurgeryCertificate` has no field mentioning the surgery datum, so certificates exist for an empty-relation datum; `missingConjugateHeatKernel` and `missingKappaNoncollapsing` are false for the zero measure; `NeckAnalysis` is inhabited with all `Prop` fields `False`; `ExtinctionTheorem` has its conclusions as free fields; and the discrete maximum principle's `hM` is redundant. All kernel-checked." (C1:300–306) | partly | **CONF (src) for the structural facts; UND for the kernel witnesses.** `missingSphereRecognitionAlgorithm : Prop := ∀ (M) […], Nonempty (Decidable (Nonempty (M ≃ₜ SphereThree)))` (`../D12-connection-curvature/release/Poincare/Longrun/Topology/MissingTheorems.lean:204–206`) — classically inhabited. `SurgeryCertificate` fields are only `compact_preserved`, `orientable_preserved`, `simplyConnected_preserved`; `D` is a parameter never mentioned in a field (`Surgery/Basic.lean:171–178`). `missingConjugateHeatKernel μ FlowHypotheses := FlowHypotheses → ∃ u, (∀τ>0, Measurable (u τ)) ∧ (∀τ>0, ∫ x, u τ x ∂μ = 1)` (`MissingTheorems.lean:88–92`) — for `μ = 0` and `FlowHypotheses := True` the integral is 0, so false. `NeckAnalysis` has only `Prop` fields and implications between them (`Surgery/Missing.lean:54–70`), so all-`False` inhabits it. `ExtinctionTheorem` has four free `Prop` fields with implications (`Missing.lean:127–141`), so all-`True` inhabits it. `HeatGridEvolution.le_of_initial_le` takes `(hM : 0 ≤ M)` explicitly (`PDE/DiscreteMaximumPrinciple.lean:96–98`); the structure has `boundary_left : ∀ t, u t 0 = 0` (`PDE/HeatGrid.lean:80`) and `hinit` at `i = 0` then gives `ev.u 0 0 = 0 ≤ M`, so `hM` is indeed redundant at source level (kernel restatement `heatGrid_le_of_initial_le_no_hM` absent → probe half UND). |
| **F11** | "`VERIFIER-D7-adversarial-audit-d2d3` finding F2 ('entropy bridge has the wrong sign') is **refuted**: Perelman's eq. (1.4) gives `F_t = +2∫\|Ric + ∇²f\|²e^{-f} ≥ 0`, matching the release. Its F11 (conjugate heat equation missing `Rρ`) is confirmed." (C1:307–310) | yes | **CONF.** The prior card is local: `audit/ophis/D13-critical-path-review/longrun/results/VERIFIER-D7-adversarial-audit-d2d3.md:82` and `:300` do claim the wrong sign ("it asserts `dF/dt = +FDissipation ≥ 0`, whereas Perelman's F satisfies `dF/dt = -2∫\|Ric+Hess f\|²e^{-f} ≤ 0`"). The release statement is `def FDerivativeStatement … : Prop := ∀ t, 0 < t → HasDerivAt (fun s => (E s).F) (EntropyData.FDissipation (E t)) t` with `FDissipation = ∫ x, 2 * (D.riccHess x)^2 * D.ρ x` (`../D12-connection-curvature/release/Poincare/Longrun/Entropy/Bridge.lean:96–98`, `Entropy/Functional.lean` `FDissipation`), i.e. `+2∫\|Ric+∇²f\|²ρ`, which is the standard Perelman (1.4) sign (F monotone nondecreasing). The conjugate equation is stated as `∂_t ρ = -Δρ` with no `+Rρ` (`Bridge.lean:88–91`), consistent with the card's confirmed F11. |
| **F12** | "A compiled proof-term binder screen over 830 declarations finds: **F12a** three D12-geometric-compactness statement-only frontier `Prop`s whose dimension/Hölder-exponent parameters are phantom (kernel-checked `rfl` independence); **F12b** six D12-comparison-geodesics theorems with explicit hypotheses the proofs never use (six sharp restatements kernel-checked); and **F12c** minor redundancies …" (C1:311–318; detail C1:724–745) | partly | **F12a CONF (src).** `harmonicCoordinatesExistence (_n : ℕ) (_α : ℝ) …` (`…/GeometricCompactness/Frontier.lean:127`), `cheegerGromovCompactness (_n : ℕ) (_α : ℝ) …` (`:164`), `bishopGromovVolumeComparison (_n : ℕ) …` (`:140`); the definition bodies contain **0** occurrences of `_n` and **0** of `_α` (scripted token count over the bodies), i.e. the propositions are parameter-independent. **F12b CONF (src, binder naming) / UND (proof-term unusedness).** The six are underscore-declared exactly as named: `areaRatio_antitone_of_logDeriv_le (_hT : 0 < T)` (`VolumeRatio.lean:77–78`), `radialVolume_pos_of_pos (_hT …)` (`:124`), `radialVolume_hasDerivAt (_hT …)` (`:192`), `radialVolume_numerator_le_zero (_hT …)` (`:208–209`), `wronskian_antitoneOn_of_le (_hab : a ≤ b)` (`SturmComparison.lean:81–82`), `euclidModelM_riccati … (_hdne : (d:ℝ) ≠ 0)` (`ModelEuclidean.lean:70`). Textual occurrence counts in the bodies are 0/1, so "never used" is plausible but the kernel restatements (`HypRemoval.lean`) are absent → **UND**. **F12c UND** (probe absent). |
| **F13** | "the round-1/2 recorded `audited_copy_sha256` for `D12-semantic-ledger`'s `A3Extra/D12RealModuleProbe.lean` (`9968a2ce…`) matches neither current copy — the file was edited after hashing … (card copy `7ee714a3…`, snapshot copy `c6c3502d…`)." (C1:319–322, 813–819) | partly | **CONF (partly).** The producer copy `../D12-semantic-ledger/audit_probes/D12RealModuleProbe.lean` hashes to `9968a2ce3e201b331dbb2392272dd6523a8b23c733c7f7b2fd0f079281fbe75d`, i.e. exactly the stale recorded value, so the producer-side file is the pre-edit version. The two staged copies (`7ee714a3…`, `c6c3502d…`) are absent → their corrected hashes **UND**. |
| **F14** | "A kernel `ConstantInfo` screen of the 342 probe entries shows 266 are proofs … 76 are non-proofs … the seventh, `D12.ConnectionCurvature.bracketInvariant`, is a hypothesis predicate sitting in that card's flat `proved_declarations` list (its proved instance is the separately listed `SoThreeModel.so3_bracketInvariant`)." (C1:323–333) | yes | **CONF.** `D12-connection-curvature.json` `proved_declarations` contains both `Poincare.D12.ConnectionCurvature.bracketInvariant` and `Poincare.D12.ConnectionCurvature.SoThreeModel.so3_bracketInvariant`. Source: `bracketInvariant … : Prop :=` is a `def` (`MilnorLeviCivita.lean:164`); `theorem so3_bracketInvariant : bracketInvariant so3Metric so3Lie` (`SoThreeModel.lean:115`). |
| **F15** | "**D12-volume-ibp records 9 of its 10** D12 files — the umbrella module `Poincare/D12/VolumeIBP.lean` (`546cd9d470e7fc07d1b16f6062790e294781566cef6f4a8b41ec858c3c8026b4`) is missing from `source_hashes`." (C1:334–342) | yes | **CONF.** `../D12-volume-ibp/longrun/results/D12-volume-ibp.json` `source_hashes` has 9 `Poincare/D12/VolumeIBP/*.lean` keys (plus `audit.py`, `ProbeScratch.lean`) and no umbrella key; `sha256sum ../D12-volume-ibp/release/Poincare/D12/VolumeIBP.lean` = `546cd9d470e7fc07d1b16f6062790e294781566cef6f4a8b41ec858c3c8026b4`, matching the card. |

### 2.2 Findings A3-D2D3-1 … A3-D2D3-9 (C1 §8, §11.10, §17.3)

| id | verbatim claim | checkable? | verdict + local evidence |
|---|---|---|---|
| **A3-D2D3-1** | "`Poincare.Longrun.Entropy.LinearDecayCertificate` … **VACUOUS**: the global lower bound and the global linear decay with `rate > 0` are jointly unsatisfiable in ℝ; `time_le` is a theorem about an empty type" (C1:408) | yes (statement) | **CONF (src); kernel probe absent.** See F9 above: `Certificate.lean:261–270` + `EntropyData.F : ℝ`. |
| **A3-D2D3-2** | "`CovariantDerivativeCurvatureStatement I M cov` … **TRIVIAL** despite the `BLOCKED` label: `cov` is unused and `κ := 0` inhabits it unconditionally" (C1:409) | yes (statement) | **CONF (src).** `LeviCivitaBlocked.lean:230–238`; `_cov` unused; `PointwiseCurvature` is a function type (`RiemannAdapter.lean:87`). |
| **A3-D2D3-3** | "`TensorRicciFlowODEBridge I M cov F T traj D` … **INHABITED BUT DEGENERATE**: witness for zero data; and every inhabitant with `0 < T` has `ricci(curvature t) = 0` on `[0,T]`, hence `traj ≡ 0` (via `basis_fixed` + orthonormality)" (C1:410) | no (probe absent) | **UND.** The interface is plausibly inhabited by degenerate data (its `realization` field reduces to the trivially-inhabited `CovariantDerivativeCurvatureStatement` plus equations that zero data satisfy — `Bridge.lean:68–99,135–157`), but the universal "every inhabitant … forces zero" claim is not derivable from the definitions I can inspect and the kernel witness (`A3D2D3.bridgeWitness`, `bridge_forces_zero_traj`) is absent. Note the producer docstring "No inhabitant of the bridge is constructed" (`Bridge.lean:34`) speaks about `release/`, not about the audit's extra `a3d2d3` module, so it neither confirms nor refutes the audit claim. |
| **A3-D2D3-4** | "`FDerivativeStatement` / `ConjugateMeasureEvolutionStatement` — sign verified against Perelman (1.4); conjugate equation missing `Rρ`" (C1:411) | yes (statement) | **CONF (src).** See F11 above. |
| **A3-D2D3-5** | "`missingSphereRecognitionAlgorithm`, `SurgeryCertificate`, `missingConjugateHeatKernel`, `missingKappaNoncollapsing`, `NeckAnalysis` — **TRIVIAL / FALSE-INSTANCE statement defects** …" (C1:412) | partly | **CONF (src) for the four inspected** (`missingSphereRecognitionAlgorithm`, `SurgeryCertificate`, `missingConjugateHeatKernel`, `NeckAnalysis`; see F10). `missingKappaNoncollapsing` was not opened (its conclusion `KappaNoncollapsingCertificate` is in `Noncollapsing.lean`, not read here) → that clause **UND**. Named probes absent. |
| **A3-D2D3-6** | "`ExtinctionTheorem` / `MissingInputs`; `HeatGridEvolution.le_of_initial_le` — **TRIVIAL / OVERSTRONG**: the four extinction conclusions are free `Prop` fields … the discrete maximum principle's hypothesis `hM : 0 ≤ M` is redundant …" (C1:413) | partly | **CONF (src).** `Missing.lean:127–141`; `DiscreteMaximumPrinciple.lean:96–98`. `MissingInputs` itself not inspected → that clause **UND**. Sharp-restatement probe absent. |
| **A3-D2D3-7** | "`kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound` — **OVERSTRONG**: the hypotheses `0 < κ`, `0 < r₀` are fields of either side and hence redundant; sharp restatement without them proved" (C1:414) | partly | **CONF (src) for redundancy; UND for the sharp restatement.** `NormalizedVolume.lean:138–143` takes `(hκ : 0 < κ) (hr₀ : 0 < r₀)`; `NormalizedBallVolumeLowerBound` has fields `kappa_pos : 0 < κ`, `r0_pos : 0 < r₀` (`:124–132`). The probe `kappa_iff_normalized_no_hyp` is absent. |
| **A3-D2D3-8** | "`stage6Target_of_compactThreeManifold._h` — `#print` shows the proof term is literally `fun _h hrec => hrec` … the theorem is 'if `M ≃ₜ 𝕊³` then `M ≃ₜ 𝕊³`', with `CompactThreeManifold` and `SimplyConnectedSpace` unused" (C1:789–793) | yes | **CONF.** `../D12-connection-curvature/release/Poincare/Longrun/Topology/Stage6Bridge.lean:102–106`: `theorem stage6Target_of_compactThreeManifold … (_h : CompactThreeManifold M) [SimplyConnectedSpace M] (hrec : Nonempty (M ≃ₜ SphereThree)) : poincareConjectureTopologicalThree M := hrec`; and `poincareConjectureTopologicalThree … : Prop := Nonempty (M ≃ₜ 𝕊³)` (`Stage6/TopologyBridge.lean:83–85`). |
| **A3-D2D3-9** | "`Poincare.Longrun.Topology.stage6Target_of_sphereRecognition` … `(h : Nonempty (M ≃ₜ SphereThree)) : poincareConjectureTopologicalThree M := h`; the hypothesis type is definitionally the conclusion, so it is a restatement of the missing Poincaré statement" (C1:1467–1468) | yes | **CONF.** `Stage6Bridge.lean:84–88` exactly as quoted. |

### 2.3 Findings F18–F28 and D-1 (later rounds)

| id | verbatim claim (C1 lines) | verdict |
|---|---|---|
| **F18** | "The round-3 screen split only on top-level `→`/`,`; … the injected tautology control was **not** flagged by the old screen (`old_screen_flags_on_control = []`), which the fixed signature-aware splitter now flags …" (1289–1298) | **UND** (audit-tool artifacts `vacuity_screen7*.json`, `selfcontrol_round7.json` absent). Directionally corroborated: the later kernel screen (§17) exists and its claims are consistent, but the specific old/new screen outputs are not present. |
| **F19** | "`diam_rep_of_toGHSpace`, printed as `diam univ = diam univ` — the pretty-printer hides the two `Set` type ascriptions; a kernel probe shows `rfl` *fails*" (C1:762–766, 1375, 1382–1387) | **UND** (`A3ExtraR8/PpArtifactCheck.lean`, `A3ExtraR3/TrivialCheck.lean` absent); the claim is plausible but unverifiable here. |
| **F20** | "the closure's only checked consumers are the ones this audit constructed in rounds 3/6/7. Verdict: **closure CONFIRMED …, the cited downstream chain REFUTED as a dependency on the closure**" (1740–1785) | **CONF.** Local source shows `so3MeanLeviCivita` is built from `meanLeviCivitaData so3Metric so3Lie so3_bracketInvariant` (`../D12-connection-curvature/release/Poincare/D12/ConnectionCurvature/SoThreeModel.lean:127–128`), not from `leviCivitaExists`/`milnorLeviCivitaData`; `so3_ricci_e00` uses `ricci_contraction_eq_sum_basis` (`:196–199`), while `so3_ricci_symm` is the user of `ricci_symm` (`:234–237`). The `leviCivitaExists` declaration has no producer-side consumer (grep over release sources: only `MilnorLeviCivita.lean:142` definition and `RicciSymmetry.lean:202–204` uses `milnorLeviCivitaData`, not `leviCivitaExists`). **However C1 §6 item 1 (C1:223–224) still asserts the refuted chain as "Downstream checked use: `milnorLeviCivitaData` → `so3MeanLeviCivita` → `ricci_symm`/`so3_ricci_e00`" — a stale, self-contradictory sentence (see §3, defect D1).** |
| **F20b** | "`closure_consumption_round8.json` labels occurrences in this lane's own `A3Extra*` files as `producer_uses` … The round-8 'all closures WIRED' statement therefore counted audit consumers, not producer consumers." (1780–1785) | **UND** (audit artifact absent). |
| **F21** | "the flagged binder is the `[T2Space X]` *instance* of `sphereOfTwoDisks` (**F21**, informational). No explicit (non-instance) hypothesis of any card-8 declaration is unused" (1684–1687) | **UND** (card-8 probe absent; card-8 producer card not local). |
| **F22** | "the remaining entry is the prose line *"plus all remaining supporting lemmas (95 declarations total audited; see AxiomAudit.lean)"*, not a declaration — a card-precision note, **F22**" (1648–1653) | **UND** (D12-triangulation-topology card absent locally). |
| **F23** | "Three card-8 use queries from round 11 had the dependency direction reversed … `uses_queries_card8.json` fixes the direction and all 15 queries now pass" (2068–2071) | **UND** (audit artifacts + card-8 absent). |
| **F24** | "`antipodalQuotientCovering` … and `simplexHomeoDisk` … have **no persistent declaration consumer**: their only uses are `example` commands …" (2072–2079) | **UND for the card-8 use-probe; source check partly possible but not decisive.** In the relayed `TriangulationTopology` tree, `antipodalQuotientCovering` appears in `CoveringLemma.lean`/`AntipodalQuotient.lean` (definition + examples) — I did not find a consumer theorem for it in the greps performed for this audit, consistent with the claim. |
| **F25** | "All three reversed pairs involved a *component/derived* lemma listed as consumer of the *main* theorem it is derived from; the corrected pairs are …" (2092–2096) | **UND** (same reason as F23). |
| **F26** | "The card's blocker *"covering-space recognition"* names `RemainingRecognitionHypothesesV2.toRemaining` and `stage6Target_of_v2hypotheses` as its downstream use. Kernel reachability … shows **neither** declaration reaches `finiteFreeOrbit_isQuotientCoveringMap`, `SphericalSpaceFormModel.covering` or `antipodalModel`: the V2 bridge is built by `sphericalPieceRecognition_of` from the *assumed* `coveringTrivial` field …" (2080–2091) | **CONF at source level (the surgery-recognition result card itself is not local → the "card's `downstream_use` field" attribution is UND, but the mathematical content is confirmed).** Relayed source: `sphericalPieceRecognition_of` takes `coveringTrivial` as an explicit hypothesis and builds `SphericalPieceRecognition` from it (`…/SurgeryRecognition/CoveringRecognition.lean:436–448`); `finiteFreeOrbit_isQuotientCoveringMap` is used only at `CoveringRecognition.lean:288` (antipodal) and `:367` (`coveringQuotient`); `RemainingRecognitionHypothesesV2.toRemaining` calls `sphericalPieceRecognition_of H.spaceForm H.coveringTrivial` (`ExpandedInterfaces.lean:176–179`), and `stage6Target_of_v2hypotheses` uses `H.vanKampen` + `H.coveringTrivial` (`:200–210`), never the constructed covering recognition; the V3 route does consume the proved deck triviality (`DeckTrivial.lean:130–162`, `ExpandedInterfaces.lean:216–225`). |
| **F27 (md §21.4)** | "The manifest's `olean_sha256` values are **not reproducible**: all 37 differ from a fresh build. … Two independent fresh builds … are **byte-identical to each other**, so the build is deterministic" (2250–2258) | **UND (build part); adjacent provenance CONFIRMED.** The `olean_sha256` field of `../D12-semantic-ledger/manifest/d12-rebuild-manifest.json` cannot be re-checked without building (read-only audit). Separately, the card's **source**-side claim for the same snapshot is confirmed: the 37 `snapshot_rebuilt_modules` hashes in the card JSON verify **37/37** against `../D11-bochner-manifold/release`. The claimed `attempts: 1, seconds: 0.0` metadata was not contradicted. |
| **F27/F28 (JSON `findings[23]`,`[24]`)** | JSON-only entries: F27 = "diskGlueRel … listed among its 195 proved_declarations"; F28 = scoped-cone "scope limitation (non-blocking)" for triangulation/surgery | **Finding-id collision.** The JSON reuses `F27`/`F28` for *different* findings than the md's `F27` (olean hashes) and `F28` (`Expr.BEq`). See §3, defect D3. |
| **F28 (md §21.6)** | "`Expr`'s `BEq` instance in `leanprover/lean4:v4.34.0-rc2` is **hash-based, not structural**: `a == b` returned `true` for the two structurally different sides of `sum_three_cycle` …" (2300–2304) | **UND** (Lean-level instrument test not re-runnable read-only; the card's claim is a tooling note, not a claim about a 360-1 card). |
| **D-1** | "The JSON still carried the round-10 `scope` (7/9 audited, 2 source-absent) and `final_state` (`TASK_BLOCKED`), contradicting `status: TASK_DONE` … Round 13 corrected `scope`, moved the stale block to `final_state_round10_superseded`, and installed a round-13 `final_state`." (2348–2351) | **CONF (fix applied).** JSON: `status: TASK_DONE`, `scope.cards_available_and_audited: 9`, `scope.cards_source_absent: []`, `final_state.cards_not_auditable: []`, `final_state_round10_superseded` retained. |

### 2.4 Claims about other cards in C1 §2 (verdict table) and §6 (closure confirmations)

- C1:115 `D12-connection-curvature … 1 claimed → **CONFIRMED** | **PASS** (card inventory defect F1)` — closure is independently confirmed here (F1 and F20 above); the "CONFIRMED" of the *closure* is supported by the local proof `leviCivitaExists` and the §21.8 type evidence. **CONF** (closure), with the §6 downstream sentence stale (see D1).
- C1:116–120 volume-ibp / spectral-sobolev / semantic-ledger / comparison-geodesics / geometric-compactness `**PASS**` — producer-side hashes for the five cards with local worktrees were independently recomputed here by content address and **all verify**: connection-curvature **12/12**; volume-ibp **11/11** (flat basename schema, content-resolved); spectral-sobolev **8/8** (`source_hashes.sha256`, 7 release files + `tools/d12_axiom_audit.sh`); semantic-ledger **66/66** `package_lean_files` + **3/3** `d12_authored` + **37/37** `snapshot_rebuilt_modules` against `../D11-bochner-manifold/release` (the D7/D10 snapshot sources the card says they match); tensor-maximum-bochner **9/9**. This confirms C1 §3's provenance claim for the five locally available cards. The other four cards (`comparison-geodesics`, `geometric-compactness`, `surgery-recognition`, `triangulation-topology`) are **UND** at card level (cards absent locally).
- C1:121 `D12-surgery-recognition … 3 claimed → **CONFIRMED** | **PASS**` — superseded by C1's own F26 for the covering-recognition claim; the other two closure claims are consistent with the relayed sources (SR-5 `mkV2` → `sphere_of_spheres` via `iteratedSphereSum_homeo_sphere`; `deckTrivial_of_simplyConnected_quotient` -> V3). **CONF for two, REFUTED-attribution for one (per C1's own F26).**
- C1:122–123 `D12-tensor-maximum-bochner | remote_owned (no artifacts) | … | **NOT AUDITABLE**`, `D12-triangulation-topology | … | **NOT AUDITABLE**` — round-1 state; **superseded** by rounds 11–13 (C1:1567, 1865–1930, 2098–2111). Locally the tensor card exists and matches the round-11+ description.
- C1 §6 items 1–4 (219–241): closure 1 `LeviCivitaExistenceStatement: CONFIRMED` — **CONF** (proof exists); its quoted downstream chain is **stale/refuted** (F20). Closure 2 SR-5 `sphere_of_spheres: CONFIRMED (with decomposition data as an explicit V2 input)` — **CONF (src)**; `mkV2` fills `sphere_of_spheres` from the proved chain while `ConnectedSumDecompositionV2.sumHomeo` remains input data. Closures 3 and 4 (covering recognition; `coveringTrivial`) — see F26: closure 3's *downstream attribution* is refuted by the same card; closure 4 (`deckTrivial_of_simplyConnected_quotient`) is **CONF (src)** (`DeckTrivial.lean:137–152`).
- C1 §19.9/§20.4/§21.8 claims about `D12-tensor-maximum-bochner` (status `TASK_BLOCKED` partial; 20 declarations; C1/C2/C3 confirmed; B1 genuine and unassumed) — **CONF locally**: the sibling card JSON has `status: partial_blocked`, `terminal_marker: TASK_BLOCKED`, 21 prose `proved_declarations` entries, `exact_blockers_closed` C1/C2/C3, and `remaining_blockers` B1/B2/B3. All **9/9** recorded source hashes verify (`sha256` recomputed here). Source check: both invariance theorems require the strengthened condition (`PositivityPreservation.lean:277–285`, `:417–425`), `hamiltonField_not_strengthened` refutes the strengthened hypothesis for the Hamilton field (`TangentCone.lean:336–338`), so "no declaration concludes PSD-invariance from `KernelTangent`" is **CONF** at source level. B1 genuinely open. The exact count "20 declarations"/"6 remaining tokens" could not be reproduced because the audited card version may differ from the local JSON (21 entries; prose lines) → numeric details **UND**.

### 3. Additional defects found in C1 itself (not numbered by the card)

- **D1 (stale self-contradiction).** C1 §6 item 1 (C1:219–224) still asserts the downstream chain
  "`milnorLeviCivitaData` → `so3MeanLeviCivita` → `ricci_symm`/`so3_ricci_e00`" as a checked use,
  while C1:1764–1775 (F20) says exactly that sentence "is not a use of the closure". The final
  round-13 table (C1:2327) no longer mentions the chain, but §6 was never corrected.
- **D2 (duplicated, mutually contradictory headline blocks).** The paragraph beginning
  `**Round-11 headline.**` occurs **10** times consecutively (C1:1559, 1561, 1563, 1565, 1567,
  1569, 1571, 1573, 1575, 1577). Four copies (1559–1565) end `One producer card, … is still
  source-absent: the milestone is 8/9 and the task remains `TASK_BLOCKED`` and report the
  intermediate count **304**; six copies (1567–1577) end `**All nine cards are audited; the
  cross-audit milestone is TASK_DONE**` and report **324**. The delivered card therefore contains
  stale contradictory status text in its body; the header (C1:66–68) notes only one other stale
  sentence.
- **D3 (duplicate finding ids).** The JSON `findings` array uses `F27` and `F28` twice with
  different content (md §21.4/§21.6 vs JSON-only "diskGlueRel"/"scope limitation" entries); the
  JSON-only pair is not documented in the md. Finding numbers F16/F17 are skipped entirely.
- **D4 (missing finding in md).** The JSON records F27 "diskGlueRel … listed among proved
  declarations" (card-8 precision) and F28 "scoped-cone scope limitation"; neither appears in the
  md (the md documents §20.8 as prose, and the diskGlueRel note only at C1:1667 as a list of
  internal relations). Reporting is therefore JSON/md divergent.
- **D5 (wrong line citation).** C1:1196 cites `Poincare/D12/VolumeIBP/Audit.lean:36`; the axiom is
  at line **40** on disk (and C1:903 correctly says 40).
- **D6 (volume-ibp card body still not updated).** C1 §10 item 4 (C1:509–512) attributes "F1/F2"
  to "D12-connection-curvature … and D12-comparison-geodesics grouped-name strings", but F2 is the
  semantic-ledger provenance finding (C1:260); the comparison-geodesics grouped-name issue is not
  given its own finding id in §7.
- **D7 (hash self-audit baseline).** C1's self-audit claims (e.g. C1:1514 `775 hashes, 0
  mismatches`) are not re-runnable here (`audit360/verify_own_hashes.py` absent). The delivered md
  hash *does* match the recorded round-13 deliverable hash `095d6083991e…` in the JSON
  (`deliverables_sha256_round13`), which is a positive provenance check.

### 4. B. Lean evidence of C1 itself

C1's own D13-authored Lean sources are **not present** in the fetched artifact: there is no
`audit360/` directory and no `a3d2d3/` directory anywhere under
`audit/ophis/D13-cross-audit-360-cards/` (verified by filename search). The Lean files that *are*
in the tree belong to the task's base D6 release (`release/…`, 60+ modules) and the workspace
negative control (`negcontrol/NegativeControl.lean`, a D6-release artifact), not to the audit
lane. Therefore C1's headline declarations (`A3D2D3.covariantCurvatureStatement_trivial`,
`linearDecay_uninhabited`, `bridgeWitness`, `a3_leviCivitaData_nonempty`, `a3_twoFoldV2`, …) can
only be reported as **UNDETERMINED — artifact absent**; no declaration names are invented here.

### 5. D. Honesty check (C1)

- Does not claim Perelman: C1:34 `The audit does **not** … claim Perelman`; C1:2347
  `No Perelman claim is made anywhere in this card.` **PASS.**
- Labels the A3 gate as *not closed* ("stale-as-stated / partially addressed", C1:69–74, 474–483,
  2345–2346) and B1 as open producer-side (C1:1926–1928, 2339–2344). **PASS.**
- Distinguishes refuted vs not-auditable (F3, F26) and records its own tool defects (F13, F18,
  F20b, F23, F28, D-1). **PASS.**
- Over-claims found: the stale §6 downstream sentence (D1) and the 10 conflicting headline blocks
  (D2) are over-claims/stale text in an otherwise honest card; the header status (`TASK_DONE`, 9/9)
  is the final state and matches the JSON. No claim that a *false theorem* was found; F10/F8/F9
  defects are interface/ledger defects. **PASS with the two text defects.** The "9/9 audited"
  claim is supported for the five locally present cards by hash/statement checks and for the four
  others by the card's own (absent) staging evidence — i.e. audited-by-report here.

### 6. E. Forbidden tokens in C1's own D13 source files

No C1-authored Lean source is present in the fetched artifact, so a scan of "the card's own D13
sources" cannot be reproduced. For completeness, the fetched tree's only task-local Lean file with
escape tokens is the D6-release negative control `negcontrol/NegativeControl.lean`:
`:25` `theorem negControl_sorry : True := by sorry` and `:27`
`theorem negControl_nativeDecide : (2 + 2 = 4) := by native_decide` — both inside the documented
negative control, not part of C1's audit. C1's own reported scans (rounds 1–7) claim clean results
with only the documented volume-ibp control; I could not re-run them. **UNDETERMINED (artifact
absent); no violation attributable to C1 on the available evidence.**

### 7. Card 1 verdict

**PASS with defects.** The hash-provenance core of the card is strongly confirmed: every recorded
`source_hashes` entry of the five locally available cards was recomputed by content address
(connection-curvature 12/12, volume-ibp 11/11, spectral-sobolev 8/8, semantic-ledger 66/66 + 3/3 +
37/37 snapshot modules, tensor-maximum-bochner 9/9), and the tensor card's status/B1/C1–C3 text
matches the local producer card. The substantive findings that are checkable against the local
360-1 sources
(F1, F2, F4, F5, F7, F8-note, F11, F12a, F13-producer-side, F14, F15, A3-D2D3-1/2/4/5/6/7/8/9,
F26-source) are **confirmed**; F9's degeneracy theorem, F3, F6's `gate_failed` clause, F10's
kernel witnesses, F12b/c, F13's corrected copies, F18–F25, F27(olean), F28 and the missing-card
claims are **undetermined** because the `audit360/` and `a3d2d3/` artifacts are absent from the
fetched bundle. Two real editorial defects remain in the delivered card: the stale
already-refuted downstream sentence in §6 (D1) and ten duplicated, mutually contradictory
"Round-11 headline" paragraphs (D2), plus finding-id collisions (D3/D4) and a wrong line citation
(D5). The final status/JSON are internally consistent (D-1 fixed); the honesty posture (no
Perelman, B1 open, 9/9 with a partial refutation) is accurate.

---

# Card 2 — `D13-critical-path-review`

## 1. Identity and self-declared state

- C2:8 `**Verdict:** `TASK_DONE` … **No Perelman/Poincaré claim; full completion is explicitly
  UNESTIMATED.**`
- C2:11–51 repair attempt 1: dispatcher gate `ok:false` due to the deliberately failing negative
  control; the root was relocated (not edited) outside `release/`; all 8 authored Lean files
  byte-identical to invocation 1.
- C2:80–85 **Not claimed:** "no theorem of Riemannian geometry, Ricci flow, surgery, extinction or
  sphere recognition is proved; `stage6Target_of_v3hypotheses` is an implication, not the Poincaré
  conjecture".

## 2. A. Findings census — claims C2 makes about other cards

### 2.1 C2 §2 table: eliminated inputs E1–E5 (C2:120–126), with producer evidence

| id | verbatim claim (C2 line) | checkable here? | verdict + evidence |
|---|---|---|---|
| **E1** | "D7 `ConnectedSumDecomposition.sphere_of_spheres` (SR-5) \| constructed from V2 connected-sum data \| `ConnectedSumDecomposition.mkV2` \| in proof of `stage6Target_of_v2decomposition`; `mkV2` 3, `iteratedSphereSum` 38, `sphereConnectSum_homeo_sphere` 42 retained consumers \| removes the field from the hypothesis list; re-verified" (C2:122) | yes (relayed source + evidence log) | **CONF.** `audit/ophis/D13-critical-path-review/audit-evidence/logs/02-usage-probe.log` lines 3–6: `mkV2 3`, `iteratedSphereSum 38`, `sphereConnectSum_homeo_sphere 42`; `01-statement-audit.log` has `D13CP_PAIR ConnectedSumDecomposition.mkV2 … stage6Target_of_v2decomposition … in_proof=true` and `D13CP_ELIMINATED_OK` for `SphericalPieceRecognition`. Source: `…/SurgeryRecognition/SphereOfSpheres.lean:225` `def mkV2 (D : ConnectedSumDecompositionV2 X pieces)`. |
| **E2** | "D7 `SphericalPieceRecognition` (opaque bridge) \| covering recognition + deck triviality constructed \| `sphericalPieceRecognition_of`, `sphericalPieceRecognition_of_spaceForm`, `deckTrivial_of_simplyConnected_quotient` \| in proofs of `...V2.toRemaining`, `...V3.toRemainingV2`, `...V3.toRemaining`; consumers 5 / 1 / 4" (C2:123) | yes | **CONF.** Log lines: `sphericalPieceRecognition_of 5`, `sphericalPieceRecognition_of_spaceForm 1`, `deckTrivial_of_simplyConnected_quotient 4`; the three `D13CP_PAIR` rows are `in_proof=true`. |
| **E3** | "`RemainingRecognitionHypothesesV2.coveringTrivial` \| proved (monodromy of `𝕊³ → 𝕊³/Γ`) \| `deckTrivial_of_simplyConnected_quotient` \| type-level absence of `RemainingRecognitionHypothesesV2` from the V3 assembly type" (C2:124) | yes | **CONF.** `01-statement-audit.log`: `D13CP_ELIMINATED_OK stage6Target_of_v3hypotheses RemainingRecognitionHypothesesV2`; source `DeckTrivial.lean:130–152`. |
| **E4** | "D7 heat-kernel `FullInitialCondition` as literally stated \| **refuted**, not repaired: false in every positive dimension \| `not_fullInitialCondition_flat_of_pos` \| D13 re-elaborated at `n = 1`; D12 repair provides the admissible-test-function interface \| eliminates a *false* hypothesis; does **not** give manifold heat-kernel existence" (C2:125) | yes (relayed source) | **CONF.** `…/release/Poincare/D12/HeatDomain/Counterexample.lean:276–277` `theorem not_fullInitialCondition_flat_of_pos (n : ℕ) (hn : 0 < n) : ¬ (flatHeatKernelCore n).FullInitialCondition`. |
| **E5** | "model/conditional inputs (Milnor Levi-Civita, semilinear parabolic mild solutions, flat-Gaussian entropy derivative, chart IBP/Bochner, 1-torus Poincaré, GH criterion) \| constructed **at model level** \| see D12 cards \| `D13CP_USE` consumers non-zero \| these are **not** the manifold-level inputs on the critical path" (C2:126) | partly | **CONF (structure) / UND (per-item).** The distinction "model-level, not manifold-level" matches the producer cards locally (e.g. `D12-tensor-maximum-bochner` remaining blocker B2; `D12-connection-curvature` chart-level F7; `D12-spectral-sobolev` scope dimension 1 per C1:1166–1170). Item-by-item confirmation would need each card's semantic_class; not re-derived here. |

**New partial closure (B1 dimension 1)** (C2:135–163): the claim is about the D12-tensor-maximum-bochner
card's blocker. Locally the tensor card indeed lists B1 as remaining
(`remaining_blockers[0]`), and C2's `n ≥ 2` statement matches the card's text almost verbatim.
**CONF** that B1 is the recorded blocker; C2's dimension-1 closure is its own new theorem (below).

### 2.2 C2 §6 "Findings beyond the D12/D13 cards" (C2:260–275)

| # | verbatim claim | verdict |
|---|---|---|
| 1 | "`iteratedSphereSum_homeo_sphere` has 0 retained consumers on the fresh build (`D13CP_USE 0`); the consumed object is the definition `iteratedSphereSum` (38 consumers) whose structure field carries the homeomorphism. The SR-5 mathematical content is constructed, but the named theorem is only an anonymous-`example`-level restatement — same class of finding as the D13-integrated audit §6.3." (C2:262–266) | **CONF.** `logs/02-usage-probe.log`: `D13CP_USE … iteratedSphereSum_homeo_sphere 0`, `iteratedSphereSum 38`. Source grep over the relayed release: the only non-docstring reference to `iteratedSphereSum_homeo_sphere` is `#print axioms` in `SurgeryRecognition/Audit.lean:134`; no proof-term consumer. |
| 2 | "**Relay gap confirmed and repaired locally:** the relayed terminal input contained only the D12 and D13/IntegratedAudit deltas; D11 (6 packages) and VKPort (10 files) had to be copied byte-identically from the verified D13-integrated worktree (per-file sha256 in `audit-evidence/copied-snapshot-hashes.txt`) before the package would compile." (C2:267–270) | **CONF.** `input/terminal/D13-integrated-kernel-audit/` contains only `release/Poincare/D12` and `release/Poincare/D13` (no `D11`, no `VKPort`). `audit-evidence/copied-snapshot-hashes.txt` lists 166 files (37 lines mention `D11`, 11 mention `VKPort`); I recomputed **166/166 sha256 OK** against the current release tree. |
| 3 | "Two negative-control modules remain inside the `Poincare.+` library glob (`axiom … : False`), so the built package contains a `False` reachable by importing those two leaf modules. Pre-existing, reported, not edited, excluded from this task's clean root." (C2:271–273) | **CONF, with an omission.** `release/lakefile.toml` globs `Poincare.+`. Exactly two **pre-existing** `axiom … : False` declarations exist in the relayed release: `release/Poincare/D12/TriangulationTopology/NegControl/NegControl.lean` and `release/Poincare/D12/VolumeIBP/Audit.lean`. A **third** one is C2's own `release/Poincare/D13/CriticalPathReview/NegControl.lean:17` (`axiom negControlBadAxiom : False`), also inside the same glob; it is never imported by a proof module, but the sentence "Two negative-control modules remain inside the `Poincare.+` library glob" under-reports the package's `False`-declaring modules. (See §5 defect D-1.) |
| 4 | "The D13-integrated audit's heat-semigroup over-claim is a card/consumer mismatch (recorded); this review did not re-audit it and does not count it as mathematics." (C2:274–275) | **UND by design** (the card explicitly declines to re-audit; the D13-integrated card is a different ophis artifact not in scope of this pair audit). |

### 2.3 C2 §3 semantic classification of others' results (C2:169–182)

Claims classify D12 results as general / conditional / model / statement-only. Spot-checks that are
locally checkable:

- "D12 Milnor Levi-Civita (left-invariant model, not the manifold-chart theorem)" (C2:171) —
  **CONF (src)**: `IsMetricCompatible` is the algebraic left-invariant condition; the chart layer is
  a separate module and the producer card itself records the scope note.
- "D12 Sturm/Riccati ODE core" as general (C2:170) — consistent with
  `ComparisonGeodesics/RiccatiComparison.lean`, `SturmComparison.lean`.
- "the heat-domain counterexample" as general (C2:173) — **CONF (src)**: `not_fullInitialCondition_flat_of_pos`
  is an unconditional theorem for every `n > 0`.
- "all four end-game assemblies … conditional" (C2:174–176) — **CONF**: the four are implications
  with explicit hypothesis structures (`stage6Target_of_certificates/v2decomposition/v2hypotheses/v3hypotheses`).
- "statement-only: the root target, `ExtinctionCertificate`, `CanonicalNeighborhoodInput`,
  `SphericalPieceRecognition`, Moise/PL-smoothing, `spaceForm`, and the U1–U12 / I1–I8 interfaces"
  (C2:179–182) — **CONF (src)** for the named D12 interfaces inspected (`ExtinctionCertificate` is a
  structure with `Prop` fields; `CanonicalNeighborhoodInput` appear as hypotheses; `SphericalPieceRecognition`
  is a structure of recognition fields; `spaceForm` is a hypothesis field in the V2/V3 structures).

### 2.4 C2 §4 critical-path ledger (claims about what remains missing)

- The five residual inputs listed for the V3 assembly (C2:196–200) are exactly the constants C2's
  own `requiredInType`/`forbiddenInType` audit checks (and the log confirms each
  `D13CP_REQ_OK`/`D13CP_ELIMINATED_OK`, `logs/01-statement-audit.log`). **CONF** as an inventory of
  the V3 type; whether each is *genuinely* an open mathematical input is a judgement, and the
  card's own §4 marks `ExtinctionCertificate`, `CanonicalNeighborhoodInput`, `spaceForm` as
  "hypothesis, no constructor".
- The `n ≥ 2` missing statement (C2:212–219) is **CONF** as identical in content to the local tensor
  card's `remaining_blockers[0]` (B1).
- "U8 quasilinear Ricci–DeTurck short-time existence … only a semilinear BUC model; derivative-loss
  barrier proved" and the rest of the analytic-core list (C2:202–210): these are cross-card
  summaries; not re-derived here → **UND** for the details, but consistent with the D12 card set
  present locally.

## 3. B. Lean evidence of C2 itself

Authored sources: `audit/ophis/D13-critical-path-review/release/Poincare/D13/CriticalPathReview/`
— **8 Lean modules** (the card's "8 authored Lean files", C2:31–32). Their recorded sha256s in
`audit-evidence/authored-hashes.txt` verify **8/8 byte-identical** here (I recomputed them), which
confirms the card's "all 8 authored Lean files … byte-identical to invocation 1".

### 3.1 `ScalarViability.lean` — mathematical content, classification **general**

- `exists_last_zero` (lines 60–62):
  `lemma exists_last_zero {g : ℝ → ℝ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (hg : ContinuousOn g (Icc 0 t₀)) (h0 : 0 ≤ g 0) (ht : g t₀ < 0) : ∃ s ∈ Icc 0 t₀, g s = 0 ∧ ∀ u ∈ Ioc s t₀, g u < 0`
- `scalar_forward_invariance` (lines 132–140):
  `theorem scalar_forward_invariance {f x : ℝ → ℝ} {T M L : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L) (hlip : ∀ a ∈ Icc (-M) M, ∀ b ∈ Icc (-M) M, |f a - f b| ≤ L * |a - b|) (hker : 0 ≤ f 0) (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t) (hcont : ContinuousOn x (Icc 0 T)) (hx0 : 0 ≤ x 0) (hxM : ∀ t ∈ Icc 0 T, |x t| ≤ M) : ∀ t ∈ Icc 0 T, 0 ≤ x t`
- `scalar_forward_invariance_of_locallyLipschitz` (lines 236–244):
  `theorem … {f x : ℝ → ℝ} {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hlip : LocallyLipschitzOn (Icc (-M) M) f) (hker : 0 ≤ f 0) (hx : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t) (hcont : ContinuousOn x (Icc 0 T)) (hx0 : 0 ≤ x 0) (hxM : ∀ t ∈ Icc 0 T, |x t| ≤ M) : ∀ t ∈ Icc 0 T, 0 ≤ x t`
- `scalar_forward_invariance_witness` (lines 261–262):
  `theorem scalar_forward_invariance_witness (c T : ℝ) (hc : 0 ≤ c) (hT : 0 ≤ T) : ∀ t ∈ Icc 0 T, 0 ≤ c * Real.exp t`

Classification: `scalar_forward_invariance` = **general** (all hypotheses expanded; the file's own
§Classification, lines 29–35, says so); `scalar_forward_invariance_of_locallyLipschitz` =
**general/derived** (unconditional consequence of the mathlib definition on a compact interval);
`exists_last_zero` = **general** (order-topology lemma); `scalar_forward_invariance_witness` =
**general non-vacuity witness**.

### 3.2 `B1DimensionOne.lean` — mathematical content, classification **general (partial closure of B1 in dim 1)**

- `scalarMat` (46): `def scalarMat (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := Matrix.diagonal (fun _ => a)`
- `scalarField` (49–50): `def scalarField (f : ℝ → ℝ) (A : Matrix (Fin 1) (Fin 1) ℝ) : Matrix (Fin 1) (Fin 1) ℝ := scalarMat (f (A 0 0))`
- `scalarMat_posSemidef_iff` (66): `theorem scalarMat_posSemidef_iff (a : ℝ) : (scalarMat a).PosSemidef ↔ 0 ≤ a`
- `kernelTangent_scalarField_iff` (73–75):
  `theorem kernelTangent_scalarField_iff (f : ℝ → ℝ) : (∀ A : Matrix (Fin 1) (Fin 1) ℝ, A.PosSemidef → KernelTangent A (scalarField f A)) ↔ 0 ≤ f 0`
- `b1_dimension_one` (122–132):
  `theorem b1_dimension_one {f : ℝ → ℝ} {T M L : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M) (hL : 0 ≤ L) (hlip : ∀ a ∈ Icc (-M) M, ∀ b ∈ Icc (-M) M, |f a - f b| ≤ L * |a - b|) (hker : 0 ≤ f 0) : (∀ A : Matrix (Fin 1) (Fin 1) ℝ, A.PosSemidef → KernelTangent A (scalarField f A)) ∧ ∀ (Mpath : ℝ → Matrix (Fin 1) (Fin 1) ℝ), (∀ t ∈ Ioo 0 T, HasDerivAt (fun u => Mpath u 0 0) (f (Mpath t 0 0)) t) → ContinuousOn (fun t => Mpath t 0 0) (Icc 0 T) → 0 ≤ Mpath 0 0 0 → (∀ t ∈ Icc 0 T, |Mpath t 0 0| ≤ M) → ∀ t ∈ Icc 0 T, (Mpath t).PosSemidef`
- `kernelTangent_scalarField_id` (142–144):
  `theorem kernelTangent_scalarField_id : ∀ A : Matrix (Fin 1) (Fin 1) ℝ, A.PosSemidef → KernelTangent A (scalarField (fun x => x) A)`

Classification: all **general** (unconditional theorems in dimension 1); `b1_dimension_one` is the
**conditional-form** statement of a partial closure (hypotheses explicit). The file's own header
(lines 24–27) labels it "a **partial closure of `B1` (the scalar/diagonal-component case only)**".
`KernelTangent` (the imported D12 condition) is `def KernelTangent {n} [Fintype n] (A N : Matrix n n ℝ) : Prop := ∀ v : n → ℝ, A *ᵥ v = 0 → 0 ≤ star v ⬝ᵥ (N *ᵥ v)`
(`…/release/Poincare/D12/TensorMaximumBochner/TangentCone.lean:77–78`).

### 3.3 Audit modules (classification **bookkeeping / evidence instruments**)

`StatementAudit.lean`:

- `mainChainDecls` (49–70): `def mainChainDecls : List Name := [ ``Poincare.D7.Recognition.stage6Target_of_certificates, … , ``Poincare.D13.CriticalPathReview.b1_dimension_one ]` (20 names)
- `requiredInType` (73–89), `forbiddenInType` (92–99), `closurePairs` (103–124):
  `def closurePairs : List (Name × Name)` containing, among others,
  `(``Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff, ``Poincare.D13.CriticalPathReview.b1_dimension_one)` (120–121)
  and `(``Poincare.D13.CriticalPathReview.scalar_forward_invariance, ``Poincare.D13.CriticalPathReview.scalar_forward_invariance_witness)` (118–119).
- `statementConstants` (131–142): `def statementConstants (env : Environment) (n : Name) : Array Name` — type constants, with the inductive-constructor special case.
- `transitiveProofConstants` (146–167): `def transitiveProofConstants (env : Environment) (root : Name) : Array Name` — fuel-bounded transitive proof-term closure.
- `runCriticalPathAudit` (171–211): `def runCriticalPathAudit : CommandElabM Unit` — fail-closed checks 1–5; `elab "#d13_cp_audit" : command => runCriticalPathAudit` (214), invoked at 220.

`UsageProbe.lean`:

- `usageTargets` (37–48): `def usageTargets : List (Name × Bool)` — includes `scalar_forward_invariance, true` (46), `exists_last_zero, true` (47), `iteratedSphereSum_homeo_sphere, false` (40).
- `directDependencies` (52–60), `projectDeclarations` (63–67), `buildReverseGraph` (70–76), `consumerCount` (80–92), `runUsageProbe` (95–114); `elab "#d13_usage_probe"` (117), invoked at 123.

`AxiomAudit.lean`:

- `approvedAxioms` (36): `def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]`
- `sorryAxiom` (39), `nativeAxioms` (42), `auditNamespace` (45)
- `loadBearingDeclarations` (49–58): `def loadBearingDeclarations : List Name := [ ``Poincare.D7.Recognition.stage6Target_of_certificates, … , ``Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2 ]` (8 names)
- `kindLabel` (61–72), `auditedDeclarations` (75–82), `runAxiomAudit` (86–133); `elab "#d13_axiom_audit"` (136), invoked at 142.

`PrintAxioms.lean` (20 `#print axioms`, lines 15–34) and `PrintAxiomsAll.lean` (63 `#print axioms`,
lines 10–72) = **bookkeeping/evidence**. `NegControl.lean` = **negative control** (see §3.4; the count omission is defect D-1 in §5).

### 3.4 Negative control: present and effective

- Yes: `release/Poincare/D13/CriticalPathReview/NegControl.lean:17`
  `axiom negControlBadAxiom : False`, `:20` `theorem negControlBadTheorem : False := negControlBadAxiom`.
  No module imports it (`grep -rn 'import.*NegControl' release` finds nothing).
- Failing root outside the package: `audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean`
  (sha256 `ef3f7ecec38bf58ff47989aed477e95e8ae00129250bb891077f667d97a042eb`, exactly the card's
  `ef3f7ece…42eb`, C2:27–28); it imports `AxiomAudit` + `NegControl` and runs `#d13_axiom_audit`.
- Log `logs/04-negcontrol-included.log` ends `D13CPAUDIT_VERDICT FAIL` and names
  `Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom`; the driver records
  `exit: 1, expected_exit: [1], ok: true` (`transcript.txt`). **CONF.**
- The card also reports (C2:271–273) two pre-existing negative controls in the relayed snapshot —
  verified above in §2.2 item 3 — but does not count its own as a third in the glob (defect D-1 in §5).

## 4. C. Self-consistency: does C2 claim closure of a named blocker, with constructor + downstream use + rebuild evidence?

Yes, exactly one: "**A new partial closure of the recorded blocker `B1`** (PSD-cone invariance under
Hamilton's *kernel* condition) in **dimension 1**" (C2:68–71; details C2:135–163), and it is
explicitly partial ("`n ≥ 2` remains open", C2:71, 163). The evidence supplied:

1. **Constructor (kernel-checked):** `kernelTangent_scalarField_iff` + `b1_dimension_one` +
   the general engine `scalar_forward_invariance` (quoted in §3.1–3.2), plus a non-vacuity witness
   `scalar_forward_invariance_witness` / `kernelTangent_scalarField_id`.
2. **Downstream use:** the card's own `StatementAudit` closure pair is a *kernel* use check —
   `logs/01-statement-audit.log` line `D13CP_PAIR Poincare.D13.CriticalPathReview.kernelTangent_scalarField_iff Poincare.D13.CriticalPathReview.b1_dimension_one in_type=false in_proof=true`
   (C2:40 reports "10 `D13CP_PAIR in_proof=true`"; the log has exactly 10 and `D13CP_VERDICT PASS`).
   The usage probe reports `D13CP_USE scalar_forward_invariance 3` and `exists_last_zero 4`
   (`logs/02-usage-probe.log`). Caveat: `b1_dimension_one` itself has **no consumer** other than
   `#print axioms`/`StatementAudit` references (grep over `release/Poincare/` — only
   `PrintAxioms.lean:24`, `PrintAxiomsAll.lean:17`, `StatementAudit.lean:69,121`), so the closure is
   not wired into any producer code; the card does not claim that it is.
3. **Rebuild evidence:** `audit-evidence/build-first.log` tail `Build completed successfully (9329
   jobs)`, `exit=0` (inv-1 fresh build, matching C2:78/300); `audit-evidence/logs/00-lake-build.log`
   (repair invocation) `Build completed successfully (9337 jobs)`; the dispatcher-gate replay
   `audit-evidence/gate-replay.json` `ok: true`, `lean_files: 454`, `build_exit: 0`,
   `nonzero_exits: 0`, fingerprint `13c945de1a1bf3e2cdf1adc1ddfbc8af2ee36509d3f7bec2c88682f936b94ef1`
   — byte-equal to the card's quoted `13c945de…4ef1` (C2:45). (The card additionally claims this
   equals `dispatch_loop.source_hash`; `longrun/bin/dispatch_loop.py` is not present in the fetched
   bundle, so that equality itself is **UND** here.)
4. **Axiom evidence:** `logs/03-axiom-audit.log` tail: `D13CPAUDIT audited_declarations 71`,
   `project_axioms 0`, `unsafe 0`, `sorryAx 0`, `native_decide 0`, `unapproved_axioms 0`,
   `collect_failures 0`, `D13CPAUDIT_VERDICT PASS`; `logs/06-print-axioms-all.log` has **63**
   declaration lines with **28** "does not depend on any axioms" — both matching C2:72–77 and
   `audit-summary.json` steps 07/08 (`declarations 20`, `declarations 63`, no unapproved cones).

So the closure is backed by constructor + kernel downstream-use + rebuild + axiom evidence, not
prose. **PASS.** The only gap is that the new closure has no external consumer (not claimed) and the
evidence-tool hash file is stale for `tools/assemble_result.py` (see D-3).

## 5. D. Honesty check (C2)

- Avoids Perelman/Poincaré: C2:8, C2:80–85, and the §7 trust table's last row (C2:287–290:
  "No layer claims more than its evidence. 'Kernel-clean' is not 'mathematically correct'; a
  constructor plus a consumer is not the general theorem."). `stage6Target_of_v3hypotheses` is
  explicitly "an implication, not the Poincaré conjecture" (C2:81–82). **PASS.**
- Labels the B1 result as a **partial** closure (dimension 1) with the exact `n ≥ 2` open statement
  (C2:68–71, 135–163, 212–219). **PASS.**
- Classification labels in §3 match the modules: `scalar_forward_invariance` = general (module
  §Classification lines 29–35), the new interface witness = non-vacuity
  (`scalar_forward_invariance_witness`, `kernelTangent_scalarField_id`), `LinearDecayCertificate`
  etc. are described as model/statement-only of the *other* cards. **PASS.**
- Over-claims / minor defects:
  - **D-1 (negative-control count).** "Two negative-control modules remain inside the `Poincare.+`
    library glob" (C2:271–273) is under-inclusive: its own `Poincare/D13/CriticalPathReview/NegControl.lean`
    (in the same glob) is a third `axiom … : False`. The card is otherwise explicit that its own
    control is never imported and that the failing root was relocated; the omission is a wording /
    completeness issue, not a hidden proof dependency.
  - **D-2 (job-count provenance).** C2:78/284 quote **9329 jobs** for the fresh build; that number
    is in `audit-evidence/build-first.log`, while the repair-invocation log `logs/00-lake-build.log`
    (the one referenced by the repair table, C2:37–39) reports **9337 jobs**. Both are exit-0 builds;
    the card's citation is to the invocation-1 log, so it is accurate but potentially confusing.
  - **D-3 (stale evidence-tool hash).** `audit-evidence/authored-hashes.txt` records
    `4b84a102…` for `tools/assemble_result.py`; the file on disk hashes to
    `85f1f64b35049d5f16fc0f87a292a8c19af72d6a2132b2924573aa7899ec8a3b` and its mtime
    (2026-09-11 19:02:47) is **after** the hash file (18:55:58). The 8 authored Lean files verify
    8/8; the other two tools verify. This is the same class as C1's F13 (self-audit drift), and the
    card does not claim the tool hashes were re-verified, but the artifact is presented as the
    provenance record (C2:316–317).
  - No claim of Perelman/Poincaré, no claim that B1 is fully closed, no claim that the model-level
    inputs are manifold-level.

## 6. E. Forbidden tokens in C2's own D13 source files (outside comments/strings)

Method: comment/string-aware scan (nested `/- -/`, `--`, string and char literals stripped,
original line numbers preserved) over the 8 authored modules
`release/Poincare/D13/CriticalPathReview/*.lean` plus the negative-control root
`audit-evidence/negcontrol/CriticalPathNegControlIncluded.lean`, for `sorry`, `axiom`, `admit`,
`unsafe`, `native_decide`, `proof_wanted`.

| file:line | token | text | assessment |
|---|---|---|---|
| `release/Poincare/D13/CriticalPathReview/NegControl.lean:17` | `axiom` | `axiom negControlBadAxiom : False` | Intentional negative control, documented in-file (lines 6–11), never imported by a proof module, and its only effect is to make the fail-closed detector fire. This is the **only real `axiom`** in C2's own sources. |
| `release/Poincare/D13/CriticalPathReview/AxiomAudit.lean:64` | `unsafe` | `\| .«unsafe» =>` | Lean constant name in the `kindLabel` match; not an `unsafe` declaration. |
| `release/Poincare/D13/CriticalPathReview/AxiomAudit.lean:101` | `unsafe` | `\| .defnInfo v => if v.safety == .«unsafe» then unsafeDecls := unsafeDecls.push n` | Same — the audit *checks for* `unsafe`; no unsafe declaration exists. |

No `sorry`, `admit`, `native_decide` or `proof_wanted` occurs outside comments/strings in any of the
8 authored modules or in the negative-control root. **Result: 1 intentional `axiom` (NegControl),
2 identifier-only `unsafe` matches, 0 other forbidden tokens.** The card's blanket claim "No
`sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted`" appears in module docstrings (e.g.
`ScalarViability.lean:37`) and is true of the proof modules; `NegControl.lean` is the disclosed
exception.

## 7. Card 2 verdict

**PASS (strong).** Its findings about other cards that are checkable here are confirmed (E1–E5,
§6.1–6.3, the negative-control count apart), its own Lean content is exactly what the card states
with full signatures, the single claimed closure (B1 dim 1) has constructor + kernel downstream-use
+ fresh rebuild + fail-closed axiom evidence, the negative control is real and fires, and the
honesty posture is correct (no Perelman/Poincaré; partial closure labelled as such; model-level vs
manifold-level distinguished). Defects are minor: the own-negative-control count omission (D-1), a
naming ambiguity in the cited lake job count (D-2), and one stale evidence-tool hash (D-3). The
card's evidence bundle verifies here at 8/8 authored Lean hashes, 166/166 copied-snapshot hashes,
454/454 gate-replay files, 71/71 audited declarations and 63/63 literal `#print axioms`
declarations.

---

## Summary verdicts

| card | verdict | most important findings |
|---|---|---|
| C1 `D13-cross-audit-360-cards` | **PASS with defects** | Hash provenance independently re-verified for every locally available card (CC 12/12, volume-ibp 11/11, spectral-sobolev 8/8, semantic-ledger 66/66 + 3/3 + 37/37 D11 snapshot modules, tensor 9/9). F1 `73/119` over-qualified names independently reproduced (45 exact / 73 over-qualified / 1 namespace-resolvable); F2, F4, F5, F7, F11, F12a, F14, F15, A3-D2D3-1/2/4/5/6/7/8/9, and F26's source-level content **CONFIRMED**; F9's "inhabited and forces zero" bridge theorem, F3, F6 `gate_failed`, F10 kernel witnesses, F12b/c, F13 corrected copies, F18–F25, F27(olean), F28 **UNDETERMINED** (all `audit360/`/`a3d2d3/` artifacts absent from the fetched bundle). Card-internal defects: §6 still asserts the downstream chain its own F20 refutes; ten duplicated, mutually contradictory "Round-11 headline" paragraphs (304/8/9/TASK_BLOCKED vs 324/9/9/TASK_DONE); duplicate `F27`/`F28` ids (JSON vs md); stale line citation `Audit.lean:36` vs 40. Honesty: no Perelman claim, B1 correctly left open. |
| C2 `D13-critical-path-review` | **PASS (strong)** | E1–E5, `iteratedSphereSum_homeo_sphere` 0 consumers, the D11/VKPort relay gap (166/166 copied hashes recomputed OK) and the two pre-existing negative controls all **CONFIRMED**; own Lean content matches full signatures in `ScalarViability.lean` and `B1DimensionOne.lean`; the B1-dim-1 partial closure carries constructor + `in_proof=true` kernel use + cold/fresh rebuild + fail-closed axiom audit (71 decls, 0 unapproved; 63 literal `#print axioms`, 28 empty); negative control `NegControl.lean:17` present and rejected (exit 1). Minor defects: it under-counts its own in-glob negative control (a third `False` axiom); cites the inv-1 job count 9329 while the repair log says 9337; `tools/assemble_result.py` hash in `authored-hashes.txt` is stale (mtime after hashing). No forbidden tokens outside comments/strings except the disclosed `axiom negControlBadAxiom : False`. |

### Audit limitations (stated, not speculated)

- No ophis-side `audit360/` artifacts were available, so all kernel-probe-based findings of C1 are
  reported UNDETERMINED rather than assumed true or false.
- The four producer cards without local worktrees (`comparison-geodesics`, `geometric-compactness`,
  `surgery-recognition`, `triangulation-topology`) were checked only at source level through the
  relayed snapshot in `audit/ophis/D13-critical-path-review/release/`; their card-level hash
  inventories, `proved_declarations` completeness and closure-attribution fields could not be
  verified.
- This audit was read-only (no `lake build`, no producer tool re-execution), so all "CONF(src)"
  verdicts are source/statement-level confirmations unless a compiled artifact (log, replay JSON,
  hash file) was already present in the fetched bundle and was re-read/recomputed here.
