# VERIFIER-D7 — adversarial audit of the promoted D2/D3 clusters

**Task id:** `VERIFIER-D7-adversarial-audit-d2d3`
**Worktree:** `/data3/guoshaoyang/workdir/lean_poincare/longrun/worktrees/VERIFIER-D7-adversarial-audit-d2d3`
**Release audited:** `D6_weekly_release` (`week-1-2026-09-09`), package `release/` (`PoincareRelease`,
Lean `v4.34.0-rc2`, mathlib `7974e751…`).
**Verdict:** the promoted D2/D3 algebraic/measure/order content is **sound** (no false theorem
found), but the audit found **one provably empty certificate structure**, **one wrong-sign
entropy bridge**, **three vacuous transfer/interface theorems**, **two "BLOCKED" statements that
are in fact trivialities**, and **one "uninhabited" bridge that is inhabited but forces the zero
trajectory**. Conventions of the curvature/Ricci/κ layers match the standard references; the
Perelman entropy bridge does not.

## 0. Scaffold and reproduction

The requested `cp -al ../D6_weekly_release/. .` failed in this sandbox with
`Invalid cross-device link` on every hard link (the file sandbox emulates cross-device links for
`link(2)`; verified with a minimal `ln` test). The scaffold was therefore created with
`cp -a ../D6_weekly_release/. .` (full copy, 687 files, 300 MB). **No copied release file was
modified**; all verifier files are new files under `AuditD2D3/`.

**Repair attempt 1 (compile gate).** The first gate run failed with no per-file math errors:
the harness gate runs `lake env lean <file>` with the **worktree root** as cwd, while the D6
scaffold puts the Lake package in `release/`. With no root `lean-toolchain`/`lakefile.toml`,
elan aborted every file with `error: no default toolchain configured`, so all 75 `.lean` files
failed. The repair adds a root Lake scaffold that re-exposes the prebuilt pinned package tree
without re-fetching anything:

| root file | content |
|---|---|
| `lakefile.toml` | root package `VerifierD7AdversarialAuditRoot`, `packagesDir = ".lake/packages"`, `require mathlib` |
| `lean-toolchain` | copy of `release/lean-toolchain` (`leanprover/lean4:v4.34.0-rc2`) |
| `lake-manifest.json` | copy of `release/lake-manifest.json` (mathlib `7974e751…`) |
| `.lake` | symlink to `release/.lake` (prebuilt mathlib + release oleans) |

No mathematical content and no copied release file changed. Re-run of the exact harness gate
command over **all 75 `.lean` files** in the worktree: **75/75 exit 0** (`GATE_OK`; per-file
log `logs/gate_repair_attempt1.txt`, JSON `logs/gate_repair_attempt1.json`). The harness command is:

```bash
export ELAN_HOME=/data3/guoshaoyang/workdir/lean_poincare/elan
export PATH="$ELAN_HOME/bin:$PATH"
cd <worktree>
lake env lean <file>          # exit 0 for all 75 files
```

The 11 verifier files can equivalently be compiled from `release/` with
`lake env lean ../AuditD2D3/<File>.lean` (exit 0), which is how they were first checked.

Forbidden-token scan (`input/d5-tools/scan_forbidden.py`, comment/string aware):
`11 files scanned, hard_match_count = 0, soft_match_count = 0`.

The only file in the worktree that contains `sorry`/`native_decide` is the **copied** D6
negative control `negcontrol/NegativeControl.lean`; it is deliberately non-release content whose
whole purpose is to prove the audit machinery detects `sorryAx` and `native_decide` (it is not
imported by anything, it is unchanged from D6, and it still compiles with exit 0). No verifier
file and no release-cluster file contains a forbidden token.

| verifier file | lines | decls | `lake env lean` |
|---|---|---|---|
| `AuditD2D3/GeometryAudit.lean` | 644 | 54 | EXIT 0 |
| `AuditD2D3/PdeAudit.lean` | 298 | 23 | EXIT 0 |
| `AuditD2D3/OdeAudit.lean` | 339 | 27 | EXIT 0 |
| `AuditD2D3/OdeAuditB.lean` | 325 | 17 | EXIT 0 |
| `AuditD2D3/OdeAuditC.lean` | 261 | 30 | EXIT 0 |
| `AuditD2D3/EntropyAudit.lean` | 877 | 76 | EXIT 0 |
| `AuditD2D3/EntropyAuditB.lean` | 213 | 20 | EXIT 0 |
| `AuditD2D3/EntropyAuditC.lean` | 132 | 10 | EXIT 0 |
| `AuditD2D3/SurgeryKappaAudit.lean` | 557 | 60 | EXIT 0 |
| `AuditD2D3/SurgeryKappaAuditB.lean` | 474 | 76 | EXIT 0 |
| `AuditD2D3/SurgeryKappaAuditC.lean` | 221 | 29 | EXIT 0 |

All `#print axioms` checks inside the verifier files return only
`{propext, Classical.choice, Quot.sound}`; no `sorryAx`, no project axiom, no `unsafe`,
no `native_decide`, no `proof_wanted`.

## 1. Headline findings

| # | finding | verdict class | evidence |
|---|---|---|---|
| F1 | `LinearDecayCertificate` is **provably empty**: its global linear-decay field contradicts its own global lower bound, so `decay`, `rate_pos` and `time_le` are vacuous. | VACUOUS | `EntropyAudit.linearDecayCertificate_uninhabited`, `.linearDecayCertificate_isEmpty`, `.linearDecayCertificate_time_le_absurd` |
| F2 | The entropy bridge's `FDerivativeStatement` has the **wrong sign**: it asserts `dF/dt = +FDissipation ≥ 0`, whereas Perelman's F satisfies `dF/dt = -2∫|Ric+Hess f|²e^{-f} ≤ 0`; the derived certificate is nondecreasing where it should be nonincreasing. | CONVENTION_MISMATCH | `EntropyAudit.fDerivativeStatement_positive_dissipation_implies_positive_deriv`, `.bridgeFamily_strictly_increasing`, `.bridgeFamily_certificate_increasing` |
| F3 | `CovariantDerivativeCurvatureStatement` / `ManifoldCurvatureRealization`, documented as **BLOCKED**, are **unconditionally provable** (`κ := 0`; the `cov` argument is ignored). | VACUOUS | `OdeAuditB.curvatureStatement_unconditional`, `.manifoldCurvatureRealization_unconditional` |
| F4 | `TensorRicciFlowODEBridge`, documented as **uninhabited**, is **inhabited**; but every inhabitant forces `traj ≡ 0` (`basis_fixed` + orthonormality pin the metric form), so both tensor-level transfer theorems are vacuous. | VACUOUS | `OdeAuditB.bridge_nonempty`, `.bridge_forces_zero_traj`, `.bridge_scalarCurvature_transfer_trivial`, `.ricciDiagonal_nonneg_of_bridge_trivial` |
| F5 | The abstract Levi-Civita **existence** statement, documented as "false without extra hypotheses", is **a theorem**: the Koszul connection is well defined and is the unique Levi-Civita connection. | OVERSTRONG (label) | `GeometryAudit.koszulNabla_eq_of_isLeviCivita`, `.leviCivitaExistence_unconditional`, `.leviCivita_nabla_unique_reproved` |
| F6 | The continuous parabolic maximum principle's `hM : 0 ≤ M` is **redundant**: it is implied by the initial bound and the Dirichlet boundary. | OVERSTRONG | `PdeAudit.le_of_initial_le_no_hM`, `.zero_le_of_initial_le` |
| F7 | The κ equivalence `kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound`'s hypotheses `0 < κ`, `0 < r₀` are **redundant** (both are fields of either side). | OVERSTRONG | `SurgeryKappaAudit.kappa_iff_normalized_strengthened` |
| F8 | `SurgeryCertificate`'s fields **do not mention the surgery datum** `D`; certificates exist for data with an empty relation. | VACUOUS (structural) | `SurgeryKappaAuditB.cert_ignores_relation`, `.toyRel_five_five_false` |
| F9 | `NeckAnalysis`, `ExtinctionTheorem`, `MissingInputs` are **inhabited for every ledger/datum**; the promoted content is conditional only. | VACUOUS | `SurgeryKappaAuditB.neckAnalysis_inhabited`, `SurgeryKappaAuditC.extinctionTheorem_inhabited`, `.missingInputs_inhabited` |
| F10 | `missingSphereRecognitionAlgorithm` is a **tautology** (`Nonempty (Decidable p)` via `Classical.propDecidable`); `missingKappaNoncollapsing` and `missingConjugateHeatKernel` are **false for the zero measure**. | VACUOUS / OVERSTRONG | `SurgeryKappaAuditC.missingSphereRecognitionAlgorithm_holds`, `.missingKappaNoncollapsing_false_zero`, `.missingConjugateHeatKernel_false_zero` |
| F11 | `ConjugateMeasureEvolutionStatement` is `∂_t ρ = -Δρ` (the heat equation); the conjugate heat equation is `∂_t ρ = -Δρ + Rρ`; the statement is insensitive to `R`. | CONVENTION_MISMATCH | `EntropyAudit.conjugateEvolutionStatement_allows_nonzero_curvature` |
| F12 | 10 of the 24 promoted entropy "declarations" are structure-field projections (`τ_pos`, `ρ_nonneg`, `integrable_F`, `integrable_W`, `MonotoneCertificate.mono`, `AntitoneCertificate.mono`, `ContinuousAntitoneCertificate.hasDerivAt_F`, `.dissipation_nonpos`, …). | OVERSTRONG | `EntropyAudit.audit_*_projection` |

## 2. Per-declaration verdicts

Legend: **CONFIRMED** = statement true and independently re-derived (or a genuine non-vacuity
witness produced); **OVERSTRONG** = true but a hypothesis/label is stronger than necessary;
**VACUOUS** = hypotheses unsatisfiable, or the conclusion is trivial for every inhabitant;
**CONVENTION_MISMATCH** = differs from the standard reference convention;
**COUNTEREXAMPLE** = a compiling witness refutes the (weakened/claimed) statement.

### 2.1 `L-D2-CURVATURE-IDENTITIES` — D2-geometry-foundation

| declaration | verdict | evidence (file: theorem) |
|---|---|---|
| `AbstractConnection.curvature_skew` | CONFIRMED | `GeometryAudit.RawConn.curv_skew` (independent re-derivation) |
| `AbstractConnection.curvature_bianchi` | CONFIRMED | `GeometryAudit.RawConn.curv_bianchi` |
| `AbstractConnection.curvature_cyclic_decomp` | CONFIRMED | `GeometryAudit.RawConn.curv_cyclic_decomp` |
| `CurvatureOperator.ricci_add` | CONFIRMED | `GeometryAudit.ricci_add_reproved` |
| `CurvatureOperator.ricci_smul` | CONFIRMED | `GeometryAudit.ricci_smul_reproved` |
| `CurvatureOperator.scalarCurvature_add` | CONFIRMED | `GeometryAudit.scalarCurvature_add_reproved` |
| `CurvatureOperator.scalarCurvature_smul` | CONFIRMED | `GeometryAudit.scalarCurvature_smul_reproved` |
| `MetricData.scalarCurvature_eq_sum_basis` | OVERSTRONG | `GeometryAudit.scalarCurvature_eq_sum_basis_reproved`; `GeometryAudit.weak_scalarContraction_eq_sum_basis` shows orthonormality is not used by the algebraic identity |
| `MetricData.form_raiseIndex` | CONFIRMED | `GeometryAudit.form_raiseIndex_reproved`; orthonormality is necessary (`GeometryAudit.form_raiseIndex_needs_orthonormal`) |
| `curvatureForm_first_pair_skew` | CONFIRMED (hypothesis-level) | `GeometryAudit.curvatureForm_first_pair_skew_reproved` |
| `curvatureForm_first_bianchi` | CONFIRMED (hypothesis-level) | `GeometryAudit.curvatureForm_first_bianchi_reproved` |

Cluster note: the two `curvatureForm_*` identities are immediate projections of the Stage1
structure fields; the algebraic content is a hypothesis, as the release's own `NOTE`
("Algebraic identities over abstract data") states. The interface is non-vacuous:
`GeometryAudit.crossCurvature_ne_zero` exhibits a nonzero `CurvatureOperator` (mean connection of
the cross-product bracket on `ℝ³`).

### 2.2 `L-D2-LEVI-CIVITA` — D2-geometry-foundation

| declaration | verdict | evidence |
|---|---|---|
| `leviCivita_nabla_unique` | CONFIRMED | `GeometryAudit.leviCivita_nabla_unique_reproved` (independent proof via the Koszul pairing) |
| `meanConnection_isMetricCompatible_iff` | CONFIRMED | `GeometryAudit.meanConnection_isMetricCompatible_iff_reproved` |
| `leviCivitaExistence_iff_nonempty` | CONFIRMED | `GeometryAudit.leviCivitaData_nonempty` |
| `mean_curvature_apply` | CONFIRMED | `GeometryAudit.mean_endoRicci_reproved`, `GeometryAudit.crossCurvature_eq_sphere_form` (round-sphere cross-check) |
| `mean_endoRicci` | CONFIRMED | `GeometryAudit.mean_endoRicci_reproved` |
| `mean_ricci_comm` | CONFIRMED | `GeometryAudit.mean_ricci_comm_reproved` |
| `LeviCivitaExistenceStatement` ("BLOCKED, false without extra hypotheses") | OVERSTRONG | `GeometryAudit.leviCivitaExistence_unconditional`, `GeometryAudit.koszulNabla_eq_of_isLeviCivita` — provable for every `MetricData`/`LieBracketData`; only bracket skew is used |

### 2.3 `L-D2-DISCRETE-MAX-PRINCIPLE` — D2-pde-foundation

| declaration | verdict | evidence |
|---|---|---|
| `HeatGridEvolution.le_of_initial_le` | OVERSTRONG | independent re-proof `PdeAudit.my_le_of_initial_le`; `hM` redundant (`PdeAudit.le_of_initial_le_no_hM`) |
| `HeatGridEvolution.le_sup'_initial` | CONFIRMED | `PdeAudit.release_max_principle_on_explicit` |
| `HeatGridEvolution.succ_le` | OVERSTRONG | `PdeAudit.my_succ_le`; `hM` redundant as above |
| `HeatGridEvolution.energy_nonincreasing` | CONFIRMED | `EntropyAuditB.audit_HeatGridEvolution_energy_antitone` (independent induction); hypotheses delimiting: `PdeAudit.counterexample_alpha_gt_half`, `.counterexample_alpha_negative`, `.counterexample_energy_alpha_gt_half` |
| `continuousHeatHypotheses_affine` | CONFIRMED | `PdeAudit.my_continuousHeatHypotheses_zero` (independent inhabitant); heat-equation hypothesis necessary: `PdeAudit.continuous_interface_needs_heat_equation` |

Non-vacuity: `PdeAudit.heatGridEvolution_inhabited` constructs an explicit `HeatGridEvolution`
for every `N`, `α`; the maximum principle is re-derived end-to-end on it.

### 2.4 `L-D2-ODE-INVARIANT` — D2-ricci-ode-cluster

| declaration | verdict | evidence |
|---|---|---|
| `component_monotone` | CONFIRMED | `OdeAudit.audit_component_monotone` (independent MVT proof) |
| `nonneg_orthant_invariant` | CONFIRMED | `OdeAudit.audit_nonneg_orthant_invariant`; non-vacuity on a **nonzero** solution: `OdeAudit.nonzero_hamilton_solution` (`λ(t)=1/(1-2t)`) |
| `nonneg_orthant_invariant_discrete` | CONFIRMED | `OdeAudit.audit_nonneg_orthant_invariant_discrete`; `h ≥ 0` necessary: `OdeAuditC.counterexample_h_nonneg` |
| `zero_orthant_invariant` | VACUOUS | `OdeAudit.zero_orthant_invariant_trivial` (conclusion is `0 ≤ 0`) |

### 2.5 `L-D2-ODE-SCALAR-MONO` — D2-ricci-ode-cluster

| declaration | verdict | evidence |
|---|---|---|
| `scalarFunctional_monotone` | CONFIRMED | `OdeAudit.audit_scalarFunctional_monotone`; `w ≥ 0` necessary: `OdeAuditC.counterexample_w_nonneg` |
| `scalarOfState_monotone` | CONFIRMED | `OdeAudit.audit_scalarOfState_monotone`; strict `1 → 2` on the nonzero solution: `OdeAudit.release_scalar_monotone_strict_on_nonzero` |
| `scalarFunctional_monotone_discrete` | CONFIRMED | `OdeAudit.audit_scalarFunctional_monotone_discrete` |
| `scalarOfState_monotone_discrete` | CONFIRMED | `OdeAudit.audit_scalarOfState_monotone_discrete` |
| `zero_scalar_monotone` | VACUOUS | `OdeAudit.zero_scalar_monotone_trivial` |
| `scalarCurvature_monotone_of_bridge` | VACUOUS | `OdeAuditB.bridge_forces_zero_traj` + `.bridge_scalarCurvature_transfer_trivial`; the bridge is inhabited (`OdeAuditB.bridge_nonempty`), so this is "inhabited but content-free", not "hypothesis never satisfiable" |
| `CovariantDerivativeCurvatureStatement` / `ManifoldCurvatureRealization` | VACUOUS | `OdeAuditB.curvatureStatement_unconditional`, `.manifoldCurvatureRealization_unconditional` |
| `TensorRicciFlowODEBridge` ("uninhabited") | VACUOUS | `OdeAuditB.bridge_nonempty` (inhabited), `.bridge_forces_zero_traj` (only zero trajectories) |
| `MetricFamilySolvesRicciFlow` | CONFIRMED (sign) | `OdeAudit.audit_ricci_flow_sign` (`-2 * ricci`, i.e. `∂_t g = -2 Ric`) |

### 2.6 `L-D3-ENTROPY-CERTIFICATES` — D3-entropy-interface

| declaration | verdict | evidence |
|---|---|---|
| `EntropyData.F` | CONFIRMED | `EntropyAudit.audit_datum_F` (`∫(R+\|∇f\|²)ρ dμ = 3e^{-3}`) |
| `EntropyData.W` | CONVENTION_MISMATCH | `EntropyAudit.W_with_conjugate_weight`: the `(4πτ)^{-n/2}` factor is absent; the release documents this as absorbed, so the interface is deliberately abstract |
| `EntropyData.FDissipation_nonneg` | CONFIRMED | `EntropyAudit.audit_FDissipation_nonneg` |
| `EntropyData.F_mono_integrand` | CONFIRMED | `EntropyAudit.audit_F_mono_integrand` |
| `EntropyData.conjugateWeight_pos` | CONFIRMED | `EntropyAudit.audit_conjugateWeight_pos` |
| `EntropyData.τ_pos` | OVERSTRONG | field projection: `EntropyAudit.lean:152` |
| `EntropyData.ρ_nonneg` | OVERSTRONG | field projection: `EntropyAudit.lean:155`; `EntropyAudit.counterexample_negative_weight_dissipation` |
| `EntropyData.integrable_F` | OVERSTRONG | field projection: `EntropyAudit.lean:158`; `EntropyAudit.counterexample_integral_mono_without_integrability` |
| `EntropyData.integrable_W` | OVERSTRONG | field projection: `EntropyAudit.lean:162` |
| `AntitoneCertificate.mono` | OVERSTRONG | `EntropyAudit.audit_antitone_mono_projection` |
| `AntitoneCertificate.F_le_of_le` | CONFIRMED | `EntropyAudit.audit_antitoneCertificate_F_le_of_le` |
| `ContinuousAntitoneCertificate.antitoneOn` | CONFIRMED | `EntropyAudit.audit_antitoneOn_direct`, `.audit_continuousAntitoneCertificate_antitoneOn` |
| `ContinuousAntitoneCertificate.dissipation_nonpos` | OVERSTRONG | `EntropyAudit.audit_dissipation_nonpos_projection`; `EntropyAudit.counterexample_flipped_sign` |
| `ContinuousAntitoneCertificate.hasDerivAt_F` | OVERSTRONG | `EntropyAudit.audit_hasDerivAt_F_projection` |
| `MonotoneCertificate.mono` | OVERSTRONG | `EntropyAudit.audit_monotone_mono_projection` |
| `LinearDecayCertificate.decay` | VACUOUS | `EntropyAudit.linearDecayCertificate_uninhabited` |
| `LinearDecayCertificate.rate_pos` | VACUOUS | `EntropyAudit.linearDecayCertificate_isEmpty`; `EntropyAudit.counterexample_rate_pos_dropped` |
| `heatEnergy_le_initial` | CONFIRMED | `EntropyAuditB.audit_heatEnergy_le_initial`; CFL hypotheses necessary (`EntropyAuditB.counterexample_alpha_negative`, `.counterexample_alpha_gt_half`) |
| `heatEnergy_nonneg` | CONFIRMED | `EntropyAuditB.audit_heatEnergy_nonneg_no_hyp` (no hypotheses needed) |
| `heatEnergyCertificate_zero` | CONFIRMED (content `0 ≤ 0`) | `EntropyAuditB.audit_heatEnergyCertificate_zero` |
| `finiteCurvatureDatum_F` | CONFIRMED | `EntropyAuditC.audit_finiteCurvatureDatum_F`, `.audit_finiteDatum_F_value` |
| `finiteCurvatureDatum_W` | CONFIRMED | `EntropyAuditC.audit_finiteCurvatureDatum_W`, `.audit_finiteDatum_W_value` (`e^{-2} ≠ 0`) |
| `continuousMonotoneCertificateOfBridge` | CONVENTION_MISMATCH | `EntropyAudit.fDerivativeStatement_positive_dissipation_implies_positive_deriv`, `.bridgeFamily_certificate_increasing` |
| `entropyRegularityBridge_zero` | CONFIRMED | `EntropyAudit.audit_entropyRegularityBridge_zero`; nontrivial instance: `EntropyAudit.bridge_bridgeFamily` |

Adjacent non-headline: `LinearDecayCertificate.time_le` — **VACUOUS**
(`EntropyAudit.linearDecayCertificate_time_le_absurd`); `FDerivativeStatement` — **CONVENTION_MISMATCH**;
`ConjugateMeasureEvolutionStatement` — **CONVENTION_MISMATCH** (missing `+Rρ`).
Vacuity map: every hypothesis structure except `LinearDecayCertificate` has an explicit
nontrivial inhabitant (`EntropyAudit.audit_datum`, `.bridge_bridgeFamily`,
`.continuousMonotoneCertificate_inc`, `.continuousAntitoneCertificate_exp`, …).

### 2.7 `L-D3-KAPPA-MANIFOLD` — D3-kappa-ledger

All seven declarations **CONFIRMED**, independently re-proved in `SurgeryKappaAuditC`:
`toSigmaCompactSpace` (`sigmaCompact_re`), `toParacompactSpace` (`paracompact_re`),
`toLocallyCompactSpace` (`locallyCompact_re`), `toSecondCountableTopology` (`secondCountable_re`),
`toTopologicalManifold` (`topologicalManifold_re`), `exists_finite_chart_cover`
(`exists_finite_chart_cover_re`, genuine compactness subcover),
`exists_mem_chart_source` (`exists_mem_chart_source_re`). Non-vacuity: `CompactThreeManifold`
is inhabited by `𝕊³` (`instCompactThreeManifoldSphereThree`) and **not** by `ℝ³` or `Empty`
(`not_compactThreeManifold_euclideanThree`, `not_compactThreeManifold_empty`).

### 2.8 `L-D3-KAPPA-ALGEBRA` — D3-kappa-ledger

All 21 declarations **CONFIRMED** except:

| declaration | verdict | evidence |
|---|---|---|
| `kappaNoncollapsingCertificate_iff_normalizedBallVolumeLowerBound` | OVERSTRONG | `SurgeryKappaAudit.kappa_iff_normalized_strengthened` — `hκ`, `hr₀` redundant |
| `KappaNoncollapsingCertificate` (structure) | VACUOUS when the curvature predicate is unsatisfiable | `SurgeryKappaAudit.vacuous_cert` (`K := False`, zero measure) |
| `NormalizedVolumeLowerBound.const_iff` | CONFIRMED | `[Nonempty M]` necessary: `SurgeryKappaAudit.const_iff_needs_nonempty` |
| κ-certificate with zero measure / `κ ≤ 0` / `r₀ ≤ 0` | COUNTEREXAMPLE (provably empty) | `SurgeryKappaAudit.zero_measure_no_cert`, `SurgeryKappaAuditC.zero_measure_no_cert_any`, `.no_cert_kappa_zero`, `.no_cert_r0_zero` |

Convention notes (recorded, not defects of the proofs): the exponent `3` is hard-coded
(dim 3 only), `normalizedBallVolume = μ(B)/r³` carries no `(4π)^{3/2}` factor, the ball is
mathlib's **open** `Metric.eball`, and the `|Rm| ≤ r⁻²` curvature normalization is only in prose
because `CurvatureBoundedOn` is an opaque abbrev. All are documented by the release; the
normalized ↔ absolute equivalence is a genuine `ENNReal` division/multiplication bookkeeping,
not a renaming (`SurgeryKappaAudit.pointwise_iff`).

### 2.9 `L-D3-SURGERY-INTERFACE` — D3-surgery-ledger

All eight declarations **CONFIRMED** (`SurgeryKappaAuditB`):
`SurgeryCertificate.trivial` (`surgeryCertificate_trivial_re`), `.ofHomeomorph` (`ofHomeomorph_re`;
orientability is exactly the supplied hypothesis), `.ofHomotopyEquiv` (`ofHomotopyEquiv_re`;
`hcompact` and `horientable` are genuinely necessary — `ofHomotopyEquiv_needs_compact`,
`.ofHomotopyEquiv_needs_orientable`), `ChainCertificate.append` (`chainCertificate_append_re`),
`.preservation` (`chainCertificate_preservation_re`), `.compact_preserved`,
`.orientable_preserved`, `.simplyConnected_preserved`.

Structural vacuity finding: `SurgeryCertificate`'s fields do not depend on the datum `D`
(`SurgeryKappaAuditB.cert_ignores_relation`: a certificate exists for `toyDatum 5 5` although
`¬ ToyRel 5 5`).

### 2.10 `L-D3-SURGERY-TOY` — D3-surgery-ledger

All 14 declarations **CONFIRMED** (`SurgeryKappaAuditB`), e.g. `toyRel_functional_re`,
`toyRel_lt_re`, `toyRel_succ_re`, `toyRel_not_refl_re`, `toyRel_nonempty_re`,
`toyRel_odd_iff_re`, `toyChain_value_re` (explicit `ToyChain 3 1 2`), `toyChain_le_re`,
`toyChain_no_infinite_re`, `toyChain_reflTransGen_re`, `toyCertificate_re`,
`toyChain321_preserves_re`, `toyChain321_compact_re`, `toy_extinction_skeleton_re`
(alias of `ToyChain.no_infinite`). `ToyRel` is empty at `m ≤ 1`
(`toyRel_zero_eq_false`, `toyRel_one_eq_false`); `toySpace 0` is compact and orientable but not
toy-simply-connected. `NeckAnalysis` / `ExtinctionTheorem` / `MissingInputs` are always
inhabited (`neckAnalysis_inhabited`, `extinctionTheorem_inhabited`, `missingInputs_inhabited`).

## 3. Counterexamples to weakened hypotheses (all compiling)

| weakened hypothesis | counterexample | evidence |
|---|---|---|
| `MetricData.orthonormal` dropped | adjoint property fails (`V=ℝ`, basis vector `2`, `⟨2,2⟩=4≠1`) | `GeometryAudit.form_raiseIndex_needs_orthonormal` |
| PDE stability `α ≤ 1/2` dropped | max principle fails (`M=1` but value `2`); energy grows `1 → 5` | `PdeAudit.counterexample_alpha_gt_half`, `.counterexample_energy_alpha_gt_half` |
| PDE sign `0 ≤ α` dropped | max principle fails (`M=1` but value `3`) | `PdeAudit.counterexample_alpha_negative` |
| strict subharmonicity weakened | constant positive `u` violates the conclusion | `PdeAudit.strict_static_needs_strict` |
| continuous heat equation dropped | `t·x·(1−x)` has correct boundary data but positive interior value | `PdeAudit.continuous_interface_needs_heat_equation` |
| `g_nonneg` dropped (ODE) | `λ' = −1` sends `1 → −1`; orthant and monotonicity fail | `OdeAuditC.counterexample_g_nonneg_continuous`, `.counterexample_g_nonneg_discrete` |
| `w ≥ 0` dropped (ODE) | weighted functional `−1 → −3` | `OdeAuditC.counterexample_w_nonneg` |
| `h ≥ 0` dropped (ODE) | negative Euler step leaves the orthant | `OdeAuditC.counterexample_h_nonneg` |
| `a_nonneg` dropped (ODE) | `λ' = −λ²` decreases a component (orthant itself still holds) | `OdeAuditC.counterexample_a_nonneg_monotone` |
| `ρ ≥ 0` dropped (entropy) | `FDissipation = −2 < 0` | `EntropyAudit.counterexample_negative_weight_dissipation` |
| integrability dropped (entropy) | pointwise `f ≤ g` but `∫f = 0 > ∫g = −1` | `EntropyAudit.counterexample_integral_mono_without_integrability` |
| `rate_pos` dropped (entropy) | `time_le`'s bound becomes false | `EntropyAudit.counterexample_rate_pos_dropped` |
| dissipation sign flipped (entropy) | the identity family is not antitone | `EntropyAudit.counterexample_flipped_sign` |
| continuity dropped (entropy) | jump family with derivative `≤ 0` is not antitone | `EntropyAudit.counterexample_continuity_dropped` |
| `[Nonempty M]` dropped (kappa) | empty type: `v₀ ≤ c` is vacuously true for `v₀ > c` | `SurgeryKappaAudit.const_iff_needs_nonempty` |
| `1 ≤ r₀` dropped (kappa) | `r₀ = 1/2`, `κ = 2` breaks the unit-ball bound | `SurgeryKappaAudit.unit_ball_lower_needs_scale` |
| `hcompact`/`horientable` dropped (surgery) | `PUnit` vs `ℝ` homotopy equivalence; `orientLedger` | `SurgeryKappaAuditB.ofHomotopyEquiv_needs_compact`, `.ofHomotopyEquiv_needs_orientable` |
| zero measure (kappa) | no certificate with `κ > 0` exists | `SurgeryKappaAuditC.zero_measure_no_cert_any` |
| zero measure (missing theorems) | `missingKappaNoncollapsing` and `missingConjugateHeatKernel` are false | `SurgeryKappaAuditC.missingKappaNoncollapsing_false_zero`, `.missingConjugateHeatKernel_false_zero` |
| impossible toy chains | `ToyChain 3 0 2`, `ToyChain 3 1 3`, `ToyChain 1 0 1`, `ToyChain 0 0 1` are empty | `SurgeryKappaAuditB` examples + `toyRel_zero_eq_false` |

## 4. Sign / index / normalization convention audit

| layer | release convention | standard reference | verdict |
|---|---|---|---|
| curvature | `R(X,Y)Z = -R(Y,X)Z`; `R(X,Y)Z+R(Y,Z)X+R(Z,X)Y=0` | do Carmo, *Riemannian Geometry* Ch. 4 | matches |
| Ricci | `endoRicci K X Y = trace (Z ↦ R(Z,X)Y)` | do Carmo: `Ric(X,Y)=Σᵢ⟨R(eᵢ,X)Y,eᵢ⟩` | matches |
| scalar curvature | `trace (raiseIndex (ricci)) = Σᵢ ricci(eᵢ,eᵢ)` | standard orthonormal-frame trace | matches |
| mean connection | `∇_X Y = ½[X,Y]`, `R(X,Y)Z = -¼[[X,Y],Z]` | bi-invariant Lie-group formula; reproduces round `S³` | matches (`GeometryAudit.crossCurvature_eq_sphere_form`) |
| Ricci-flow equation | `MetricFamilySolvesRicciFlow`: `d/dt⟨X,X⟩ = -2 Ric(X,X)` | `∂_t g = -2 Ric` | matches (`OdeAudit.audit_ricci_flow_sign`) |
| ODE reaction | `λᵢ' = aᵢλᵢ² + gᵢ`, `aᵢ,gᵢ ≥ 0` | reaction part of `∂_t R = ΔR + 2|Ric|²` | matches (model documented) |
| entropy F | `∫(R+\|∇f\|²)ρ dμ` | Perelman `∫(R+\|∇f\|²)e^{-f}dμ` | matches with `ρ=e^{-f}` |
| entropy W | `∫(τ(\|∇f\|²+R)+f−n)ρ dμ` | Perelman `∫[τ(R+\|∇f\|²)+f−n](4πτ)^{-n/2}e^{-f}dμ` | CONVENTION_MISMATCH: `(4πτ)^{-n/2}` absent (documented as absorbed) |
| F dissipation | `FDissipation = +2∫\|Ric+∇²f\|²ρ dμ` | `dF/dt = −2∫\|Ric+Hess f\|²e^{-f}dμ` | CONVENTION_MISMATCH: `FDerivativeStatement` uses `dF/dt = +FDissipation`, the wrong sign |
| conjugate heat | `∂_t ρ = −Δρ` | `∂_t ρ = −Δρ + Rρ` | CONVENTION_MISMATCH: `Rρ` term missing |
| κ-noncollapsing | `κ r³ ≤ μ(B(x,r))`, `normalizedBallVolume = μ(B)/r³` | `vol B(x,r) ≥ κ r³` (dim 3) | matches up to the κ rescaling; no `(4π)^{3/2}`, open `eball`, opaque `|Rm| ≤ r⁻²` |
| surgery | orientability a predicate parameter | standard | documented parameter |

## 5. Soundness

**No soundness bug found.** Every promoted theorem of the audited clusters type-checks and was
independently re-derived where feasible; no false proved statement exists in the release. The
defects found are specification defects: vacuity (F1, F4, F8, F9, F10), a wrong-sign interface
(F2, F11), trivially-provable "blocked" interfaces (F3, F5), redundant hypotheses (F6, F7) and
projection-as-theorem inflation (F12). No `sorry`, `axiom`, `unsafe`, `native_decide` or
`proof_wanted` occurs in the release clusters or in the verifier files.

## 6. Recommendations

1. `LinearDecayCertificate`: replace the global decay inequality by a horizon-bounded one
   (`t ≤ T` with `T ≤ (F(E0)−lowerBound)/rate`) or the structure stays empty.
2. `FDerivativeStatement`: flip to `dF/dt = −FDissipation` and derive a
   `ContinuousAntitoneCertificate` (Perelman's F is nonincreasing).
3. `ConjugateMeasureEvolutionStatement`: add the `+Rρ` term.
4. Relabel `CovariantDerivativeCurvatureStatement`/`ManifoldCurvatureRealization`: either add the
   derivation content (curvature from `cov`) or mark them as satisfiable-by-zero, not BLOCKED.
5. `TensorRicciFlowODEBridge`: the `basis_fixed` field plus orthonormality forces `traj ≡ 0`;
   the transfer theorems should either drop `basis_fixed` or be restated without the forcing.
6. Separate structure-field accessors from theorems in the promoted declaration lists.
7. Document that `KappaNoncollapsingCertificate` is vacuous when the curvature predicate is
   unsatisfiable, and that `missingKappaNoncollapsing`/`missingConjugateHeatKernel` need a
   positive-volume-measure hypothesis.

## 7. Evidence index

- Geometry: `AuditD2D3/GeometryAudit.lean`
- PDE: `AuditD2D3/PdeAudit.lean`
- ODE: `AuditD2D3/OdeAudit.lean`, `AuditD2D3/OdeAuditB.lean`, `AuditD2D3/OdeAuditC.lean`
- Entropy: `AuditD2D3/EntropyAudit.lean`, `AuditD2D3/EntropyAuditB.lean`, `AuditD2D3/EntropyAuditC.lean`
- Kappa/surgery: `AuditD2D3/SurgeryKappaAudit.lean`, `AuditD2D3/SurgeryKappaAuditB.lean`,
  `AuditD2D3/SurgeryKappaAuditC.lean`
- Machine-readable verdicts: `longrun/results/VERIFIER-D7-adversarial-audit-d2d3.json`

TASK_DONE — card: `longrun/results/VERIFIER-D7-adversarial-audit-d2d3.md`
