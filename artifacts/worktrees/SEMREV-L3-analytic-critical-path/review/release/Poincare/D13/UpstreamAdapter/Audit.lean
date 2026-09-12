/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-upstream-adapter-audit)

# Axiom audit for the D13 upstream-adapter module set

Every declaration authored by `Poincare.D13.UpstreamAdapter` is printed with
`#print axioms` and re-checked programmatically with `Lean.collectAxioms`.  The expected
(and enforced) outcome is that every declaration depends only on the three standard Lean
axioms `propext`, `Classical.choice`, `Quot.sound` (or on none); in particular no
`sorryAx`, no user axiom, no `unsafe`, no `Lean.ofReduceBool` from `native_decide`, and no
`proof_wanted` may appear.  The `#print axioms` lines are informational transcripts; the
enforceable fail-closed gate is the programmatic `run_cmd` re-check at the end, which
aborts the build on any axiom outside the approved cone.

The upstream transcriptions (`heatKernelSpatial`, `heatSolution`, `solitonScale`,
`RicciFlowData`, `IsKappaNoncollapsedOnScale`, …) are plain definitions/structures:
no upstream axiom is imported; the upstream sources carry no `axiom` declarations
(verified by the snapshot survey, `tmp/upstream-survey.md`).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

import Poincare.D13.UpstreamAdapter.All

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command
open Poincare.D13.UpstreamAdapter

/-! ## Downstream use checks (kernel-checked consumers of the adapter theorems) -/

open MeasureTheory Filter
open scoped Topology

/-- The transcribed upstream Evans bounded initial-condition theorem, consumed on the
flat model: for the bounded Gaussian datum `g = heatKernelSpatial n 1` (integrable in the
bounded class), the convolution attains its value at `0`. -/
example (n : ℕ) :
    Tendsto (fun t : ℝ => Evans.heatSolution n (Evans.heatKernelSpatial n 1) 0 t)
      (𝓝[>] (0 : ℝ)) (𝓝 ((Evans.heatKernelSpatial n 1) 0)) := by
  rcases Evans.heatKernelSpatial_bound_compat n with ⟨M, hM⟩
  exact Evans.heatSolution_tendsto_initial_of_bounded n
    (Evans.heatKernelSpatial_contDiff_compat n).continuous hM (0 : EuclideanSpace ℝ (Fin n))

/-- The upstream compact-support differentiation lemma, consumed at the D12 level: the
transcribed Evans statement is proved by the local D12 weighted-integral theorem. -/
example {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ => ∫ y : EuclideanSpace ℝ (Fin n),
        Evans.heatKernelSpatial n t (x₀ - y) * g y) (𝓝[>] (0 : ℝ)) (𝓝 (g x₀)) :=
  Evans.heatSolution_tendsto_initial_of_integrable n x₀ hg
    (hg.integrable_of_hasCompactSupport hgc)

/-- The upstream MorganTian soliton scale, consumed at the local D12 F-flow level. -/
example (τ₀ t : ℝ) :
    MorganTian.solitonScale (1 / (2 * τ₀)) t =
      Poincare.D12.EntropyVariation.fflowMetricScale τ₀ t :=
  MorganTian.solitonScale_eq_fflowMetricScale τ₀ t

/-- The upstream KleinerLott κ-predicate, consumed through the conditional adapter:
the exact typed reduction of the upstream predicate (with the translation hypotheses) to
the local D3/D7 κ-certificate. -/
example {M : Type*} [PseudoEMetricSpace M] [MeasurableSpace M]
    (flow : KleinerLott.RicciFlowData M) (μ : Measure M)
    (K : Poincare.Longrun.Topology.CurvatureBoundedOn M) {T t₀ κ ρ r₀ : ℝ}
    (ht₀T : t₀ < T) (hr₀ : 0 < r₀) (hr₀ρ : r₀ < ρ) (hscale : ρ ^ (2 : ℕ) ≤ t₀)
    (hκ : 0 < κ)
    (hvol : ∀ x r, 0 < r → ENNReal.ofReal
        (flow.volume t₀ (KleinerLott.RicciFlowData.ball flow t₀ x r)) ≤
      μ (Metric.eball x (ENNReal.ofReal r)))
    (hcurv : ∀ x r, 0 < r → K x r →
      flow.HasCurvatureBoundOnParabolicBall x t₀ r ((r⁻¹) ^ 2))
    (hkl : KleinerLott.IsKappaNoncollapsedOnScale flow 3 T κ ρ) :
    Poincare.Longrun.Topology.KappaNoncollapsingCertificate M μ K κ r₀ :=
  KleinerLott.isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate
    flow μ K ht₀T hr₀ hr₀ρ hscale hκ hvol hcurv hkl

/-! ## Transcribed upstream definitions and adapter theorems -/

#print axioms Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatSolution
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial_eq_gaussianKernel
#print axioms Poincare.D13.UpstreamAdapter.Evans.integrable_heatKernelSpatial
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial_integral
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatSolution_eq_convolution
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatSolution_eq_flatKernelConv
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatSolution_approx_bound_at_of_bounded
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatSolution_tendsto_initial_of_bounded
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatSolution_tendsto_initial_joint_of_bounded
#print axioms Poincare.D13.UpstreamAdapter.Evans.boundedContinuousClass
#print axioms Poincare.D13.UpstreamAdapter.Evans.boundedClass_cls_iff_integrableClass_cls_of_compactSpace_finiteMeasure
#print axioms Poincare.D13.UpstreamAdapter.Evans.weakInitialConditionFor_boundedClass_iff_full_of_compact_finiteMeasure
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial_contDiff_compat
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial_bound_compat
#print axioms Poincare.D13.UpstreamAdapter.Evans.heatSolution_tendsto_initial_of_integrable
#print axioms Poincare.D13.UpstreamAdapter.Evans.hasDerivAt_integral_mul_hasCompactSupport
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.solitonScale
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.metricLieDerivativeFlat
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.shrinkerGradientField
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.IsSolitonGeneratorEuclidean
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.IsGradientShrinkerPotentialEuclidean
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.solitonScale_eq_fflowMetricScale
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.shrinkerGradientField_isGradient
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.fderiv_shrinkerGrad
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.metricLieDerivativeFlat_shrinkerGrad
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.shrinkerFpot_isGradientShrinkerPotentialEuclidean
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.shrinkerGrad_isSolitonGeneratorEuclidean
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean
#print axioms Poincare.D13.UpstreamAdapter.MorganTian.shrinkerFpot_GSS_and_solitonGenerator
#print axioms Poincare.D13.UpstreamAdapter.KleinerLott.RicciFlowData
#print axioms Poincare.D13.UpstreamAdapter.KleinerLott.RicciFlowData.ball
#print axioms Poincare.D13.UpstreamAdapter.KleinerLott.RicciFlowData.HasCurvatureBoundOnParabolicBall
#print axioms Poincare.D13.UpstreamAdapter.KleinerLott.IsKappaNoncollapsedOnScale
#print axioms Poincare.D13.UpstreamAdapter.KleinerLott.IsKappaCollapsedAt
#print axioms Poincare.D13.UpstreamAdapter.KleinerLott.isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate

/-! ## The fail-closed programmatic gate -/

private def d13UpstreamAdapterAuditedDeclarations : List Name :=
  [ ``Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial,
    ``Poincare.D13.UpstreamAdapter.Evans.heatSolution,
    ``Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial_eq_gaussianKernel,
    ``Poincare.D13.UpstreamAdapter.Evans.integrable_heatKernelSpatial,
    ``Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial_integral,
    ``Poincare.D13.UpstreamAdapter.Evans.heatSolution_eq_convolution,
    ``Poincare.D13.UpstreamAdapter.Evans.heatSolution_eq_flatKernelConv,
    ``Poincare.D13.UpstreamAdapter.Evans.heatSolution_approx_bound_at_of_bounded,
    ``Poincare.D13.UpstreamAdapter.Evans.heatSolution_tendsto_initial_of_bounded,
    ``Poincare.D13.UpstreamAdapter.Evans.heatSolution_tendsto_initial_joint_of_bounded,
    ``Poincare.D13.UpstreamAdapter.Evans.boundedContinuousClass,
    ``Poincare.D13.UpstreamAdapter.Evans.boundedClass_cls_iff_integrableClass_cls_of_compactSpace_finiteMeasure,
    ``Poincare.D13.UpstreamAdapter.Evans.weakInitialConditionFor_boundedClass_iff_full_of_compact_finiteMeasure,
    ``Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial_contDiff_compat,
    ``Poincare.D13.UpstreamAdapter.Evans.heatKernelSpatial_bound_compat,
    ``Poincare.D13.UpstreamAdapter.Evans.heatSolution_tendsto_initial_of_integrable,
    ``Poincare.D13.UpstreamAdapter.Evans.hasDerivAt_integral_mul_hasCompactSupport,
    ``Poincare.D13.UpstreamAdapter.MorganTian.solitonScale,
    ``Poincare.D13.UpstreamAdapter.MorganTian.metricLieDerivativeFlat,
    ``Poincare.D13.UpstreamAdapter.MorganTian.shrinkerGradientField,
    ``Poincare.D13.UpstreamAdapter.MorganTian.IsSolitonGeneratorEuclidean,
    ``Poincare.D13.UpstreamAdapter.MorganTian.IsGradientShrinkerPotentialEuclidean,
    ``Poincare.D13.UpstreamAdapter.MorganTian.solitonScale_eq_fflowMetricScale,
    ``Poincare.D13.UpstreamAdapter.MorganTian.shrinkerGradientField_isGradient,
    ``Poincare.D13.UpstreamAdapter.MorganTian.fderiv_shrinkerGrad,
    ``Poincare.D13.UpstreamAdapter.MorganTian.metricLieDerivativeFlat_shrinkerGrad,
    ``Poincare.D13.UpstreamAdapter.MorganTian.shrinkerFpot_isGradientShrinkerPotentialEuclidean,
    ``Poincare.D13.UpstreamAdapter.MorganTian.shrinkerGrad_isSolitonGeneratorEuclidean,
    ``Poincare.D13.UpstreamAdapter.MorganTian.isGradientShrinkerPotentialEuclidean_isSolitonGeneratorEuclidean,
    ``Poincare.D13.UpstreamAdapter.MorganTian.shrinkerFpot_GSS_and_solitonGenerator,
    ``Poincare.D13.UpstreamAdapter.KleinerLott.RicciFlowData,
    ``Poincare.D13.UpstreamAdapter.KleinerLott.RicciFlowData.ball,
    ``Poincare.D13.UpstreamAdapter.KleinerLott.RicciFlowData.HasCurvatureBoundOnParabolicBall,
    ``Poincare.D13.UpstreamAdapter.KleinerLott.IsKappaNoncollapsedOnScale,
    ``Poincare.D13.UpstreamAdapter.KleinerLott.IsKappaCollapsedAt,
    ``Poincare.D13.UpstreamAdapter.KleinerLott.isKappaNoncollapsedOnScale_to_kappaNoncollapsingCertificate ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def d13UpstreamAdapterApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in d13UpstreamAdapterAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !d13UpstreamAdapterApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D13UpstreamAdapterAxiomCheck: PASS — all {d13UpstreamAdapterAuditedDeclarations.length} declarations \
      of the D13 upstream-adapter module set depend only on [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D13UpstreamAdapterAxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D13UpstreamAdapterAxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
