/-
Copyright (c) 2026 Poincaré project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D13-morgan-tian-adapter-plan)

# Axiom audit for the D13 MorganTian-adapter module set

Every declaration authored by `Poincare.D13.MorganTianAdapter` is printed with
`#print axioms` and re-checked programmatically with `Lean.collectAxioms`.  The expected
(and enforced) outcome is that every declaration depends only on the three standard Lean
axioms `propext`, `Classical.choice`, `Quot.sound` (or on none); in particular no
`sorryAx`, no user axiom, no `unsafe`, no `Lean.ofReduceBool` from `native_decide`, and no
`proof_wanted` may appear.  The `#print axioms` lines are informational transcripts; the
enforceable fail-closed gate is the programmatic `run_cmd` re-check at the end, which
aborts the build on any axiom outside the approved cone.

The upstream transcriptions (`flatRiemannCurvature`, `flatRicciAt`, `expMapEuclidean`,
`flatParallelTransport`, …) are plain definitions: no upstream axiom is imported; the
upstream sources carry no `axiom` declarations (verified by the snapshot survey).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/

import Poincare.D13.MorganTianAdapter.All

import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command
open Poincare.D13.MorganTianAdapter

/-! ## Downstream use checks (kernel-checked consumers of the adapter theorems) -/

open MeasureTheory Filter
open scoped Topology ENNReal

/-- The upstream (GSS) gradient-shrinker predicate, satisfied by the local D12 Gaussian
shrinker through the computed flat Ricci tensor (`Curvature` → `UpstreamAdapter`). -/
example (n : ℕ) {τ : ℝ} (hτ : 0 < τ) :
    Poincare.D13.UpstreamAdapter.MorganTian.IsGradientShrinkerPotentialEuclidean n
      (Poincare.D12.EntropyVariation.shrinkerFpot τ) (1 / (2 * τ)) :=
  Curvature.shrinkerFpot_isGradientShrinkerPotentialEuclidean n hτ

/-- The flat-model κ-noncollapsing certificate: the D12 conditional transfer
`gaussianKappaNoncollapsing_of_ballVolumeComparison` fires with the proved flat-model
ball-volume comparison, producing the D3 `KappaNoncollapsingCertificate` with
`κ = 4π/3`. -/
example :
    Poincare.Longrun.Topology.KappaNoncollapsingCertificate
      (EuclideanSpace ℝ (Fin 3)) volume (fun _ _ => True) (4 * Real.pi / 3) 1 :=
  BishopGromov.flatModel_kappaNoncollapsingCertificate

/-- The upstream geodesic predicate, satisfied by the affine lines of the flat model. -/
example (x v : EuclideanSpace ℝ (Fin 2)) :
    ExpGeodesic.IsGeodesicEuclidean (ExpGeodesic.globalGeodesicEuclidean x v) :=
  ExpGeodesic.isGeodesicEuclidean_globalGeodesic x v

/-- The U1 flat-curvature vanishing, consumed in the upstream curvature-form shape:
the four first-order symmetries and the first Bianchi identity hold on the flat model. -/
example (p v w z t : EuclideanSpace ℝ (Fin 3)) :
    Curvature.flatCurvatureFormAt p v w z t + Curvature.flatCurvatureFormAt p w z v t
      + Curvature.flatCurvatureFormAt p z v w t = 0 :=
  Curvature.flatCurvatureFormAt_firstBianchi p v w z t

/-! ## The MorganTian-adapter declaration inventory -/

#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatMetric
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatCovariantDeriv
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatLieBracket
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatRiemannCurvature
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormField
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatRicciAt
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatScalarCurvatureAt
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatSectionalCurvatureAt
#print axioms Poincare.D13.MorganTianAdapter.Curvature.IsGradientShrinkerPotentialFlat
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatRiemannCurvature_eq_secondDerivativeCommutator
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatRiemannCurvature_eq_zero
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_eq_zero
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatRicciAt_eq_zero
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatScalarCurvatureAt_eq_zero
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatSectionalCurvatureAt_eq_zero
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_antisymm_left
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_antisymm_right
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_pairSwap
#print axioms Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_firstBianchi
#print axioms Poincare.D13.MorganTianAdapter.Curvature.IsGradientShrinkerPotentialEuclidean_iff_flatRicci
#print axioms Poincare.D13.MorganTianAdapter.Curvature.shrinkerFpot_gradientShrinkerPotentialFlat
#print axioms Poincare.D13.MorganTianAdapter.Curvature.shrinkerFpot_isGradientShrinkerPotentialEuclidean
#print axioms Poincare.D13.MorganTianAdapter.Tensoriality.flatCovariantDeriv_smul
#print axioms Poincare.D13.MorganTianAdapter.Tensoriality.flatCovariantDeriv_congr_of_eq_at
#print axioms Poincare.D13.MorganTianAdapter.Tensoriality.flatCovariantDeriv_congr_of_eventuallyEq
#print axioms Poincare.D13.MorganTianAdapter.Tensoriality.flatCovariantDeriv_congr_of_eq_fderiv
#print axioms Poincare.D13.MorganTianAdapter.Tensoriality.flatRiemannCurvature_congr_of_eq_at
#print axioms Poincare.D13.MorganTianAdapter.Tensoriality.flatCurvatureFormField_eq_flatCurvatureFormAt
#print axioms Poincare.D13.MorganTianAdapter.Tensoriality.flatRiemannCurvature_congr_of_eventuallyEq
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.IsGeodesicEuclidean
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.expMapEuclidean
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.globalGeodesicEuclidean
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.flatParallelTransport
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.expMapEuclidean_eq
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.isGeodesicEuclidean_globalGeodesic
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.fderiv_expMapEuclidean_eq_id
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.expMapEuclidean_injective
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.flatParallelTransport_inner
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.flatParallelTransport_norm
#print axioms Poincare.D13.MorganTianAdapter.ExpGeodesic.flatSectionalCurvature_eq_zero_and_expDifferential_id
#print axioms Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness.flatCovariantDeriv_contDiff
#print axioms Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness.flatCovariantDeriv_eq_fderiv_apply
#print axioms Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness.flatLeviCivita_contDiff_pair
#print axioms Poincare.D13.MorganTianAdapter.BishopGromov.antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one
#print axioms Poincare.D13.MorganTianAdapter.BishopGromov.eball_ofReal_eq_ball
#print axioms Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_normalizedBallVolume_eq
#print axioms Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_ballVolumeComparison
#print axioms Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_kappaNoncollapsingCertificate
#print axioms Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_volume_ball_pos

/-! ## The fail-closed programmatic gate -/

private def d13MorganTianAdapterAuditedDeclarations : List Name :=
  [ ``Poincare.D13.MorganTianAdapter.Curvature.flatMetric,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatCovariantDeriv,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatLieBracket,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatRiemannCurvature,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormField,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatRicciAt,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatScalarCurvatureAt,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatSectionalCurvatureAt,
    ``Poincare.D13.MorganTianAdapter.Curvature.IsGradientShrinkerPotentialFlat,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatRiemannCurvature_eq_secondDerivativeCommutator,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatRiemannCurvature_eq_zero,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_eq_zero,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatRicciAt_eq_zero,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatScalarCurvatureAt_eq_zero,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatSectionalCurvatureAt_eq_zero,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_antisymm_left,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_antisymm_right,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_pairSwap,
    ``Poincare.D13.MorganTianAdapter.Curvature.flatCurvatureFormAt_firstBianchi,
    ``Poincare.D13.MorganTianAdapter.Curvature.IsGradientShrinkerPotentialEuclidean_iff_flatRicci,
    ``Poincare.D13.MorganTianAdapter.Curvature.shrinkerFpot_gradientShrinkerPotentialFlat,
    ``Poincare.D13.MorganTianAdapter.Curvature.shrinkerFpot_isGradientShrinkerPotentialEuclidean,
    ``Poincare.D13.MorganTianAdapter.Tensoriality.flatCovariantDeriv_smul,
    ``Poincare.D13.MorganTianAdapter.Tensoriality.flatCovariantDeriv_congr_of_eq_at,
    ``Poincare.D13.MorganTianAdapter.Tensoriality.flatCovariantDeriv_congr_of_eventuallyEq,
    ``Poincare.D13.MorganTianAdapter.Tensoriality.flatCovariantDeriv_congr_of_eq_fderiv,
    ``Poincare.D13.MorganTianAdapter.Tensoriality.flatRiemannCurvature_congr_of_eq_at,
    ``Poincare.D13.MorganTianAdapter.Tensoriality.flatCurvatureFormField_eq_flatCurvatureFormAt,
    ``Poincare.D13.MorganTianAdapter.Tensoriality.flatRiemannCurvature_congr_of_eventuallyEq,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.IsGeodesicEuclidean,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.expMapEuclidean,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.globalGeodesicEuclidean,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.flatParallelTransport,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.expMapEuclidean_eq,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.isGeodesicEuclidean_globalGeodesic,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.fderiv_expMapEuclidean_eq_id,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.expMapEuclidean_injective,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.flatParallelTransport_inner,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.flatParallelTransport_norm,
    ``Poincare.D13.MorganTianAdapter.ExpGeodesic.flatSectionalCurvature_eq_zero_and_expDifferential_id,
    ``Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness.flatCovariantDeriv_contDiff,
    ``Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness.flatCovariantDeriv_eq_fderiv_apply,
    ``Poincare.D13.MorganTianAdapter.LeviCivitaSmoothness.flatLeviCivita_contDiff_pair,
    ``Poincare.D13.MorganTianAdapter.BishopGromov.antitoneOn_ratio_le_one_of_tendsto_nhdsGT_one,
    ``Poincare.D13.MorganTianAdapter.BishopGromov.eball_ofReal_eq_ball,
    ``Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_normalizedBallVolume_eq,
    ``Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_ballVolumeComparison,
    ``Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_kappaNoncollapsingCertificate,
    ``Poincare.D13.MorganTianAdapter.BishopGromov.flatModel_volume_ball_pos ]

/-- The approved axiom cone: exactly the three standard Lean axioms. -/
private def d13MorganTianAdapterApprovedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

run_cmd do
  let mut unapprovedTotal : Array (Name × List Name) := #[]
  for d in d13MorganTianAdapterAuditedDeclarations do
    let axs ← Lean.collectAxioms d
    let bad := axs.toList.filter (fun a => !d13MorganTianAdapterApprovedAxioms.contains a)
    if !bad.isEmpty then
      unapprovedTotal := unapprovedTotal.push (d, bad)
  if unapprovedTotal.isEmpty then
    logInfo m!"D13MorganTianAdapterAxiomCheck: PASS — all {d13MorganTianAdapterAuditedDeclarations.length} declarations \
      of the D13 MorganTian-adapter module set depend only on [propext, Classical.choice, Quot.sound]"
  else
    for (d, bad) in unapprovedTotal do
      logError m!"D13MorganTianAdapterAxiomCheck: {d} depends on unapproved axioms {bad.map Name.toString}"
    throwError "D13MorganTianAdapterAxiomCheck: FAIL — {unapprovedTotal.size} declaration(s) with unapproved axioms"
