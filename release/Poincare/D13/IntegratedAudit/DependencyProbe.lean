/-
Copyright (c) 2026 D13-integrated-kernel-audit. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# D13 integrated kernel audit — blocker-closure dependency probe

For each `(constructor, downstream)` pair asserted by a D12 `exact_blockers_closed` record,
this probe answers three questions against the *integrated* environment:

* `exists`: both constants are present;
* `in_type`: the constructor occurs in the (transitive) constant closure of the
  downstream declaration's **type**;
* `in_proof`: the constructor occurs in the (transitive) constant closure of the
  downstream declaration's **value** (proof term / definition body).

`in_proof = true` is machine evidence that the downstream declaration actually consumes
the constructor, as opposed to merely naming it.  Emits `D13DEP` lines; the driver
`audit-evidence/tools/d13_audit.py` records them.
-/
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Lean.Elab.Command

open Lean Elab Command

namespace Poincare.D13.IntegratedAudit

/-- Does the transitive constant closure of `todo` reach `target`?  Fail-closed on
unknown constants: they contribute nothing (the `exists` column reports them). -/
partial def reaches (env : Environment) (target : Name) (seen : Array Name) (todo : List Name) : Bool :=
  match todo with
  | [] => false
  | c :: rest =>
    if c == target then true
    else if seen.contains c then reaches env target seen rest
    else
      let seen := seen.push c
      -- expansion is restricted to snapshot-internal constants: no mathlib constant can
      -- reference a Poincare D11/D12 declaration, so this preserves reachability while
      -- keeping the traversal small.  `value? true` is required: Lean 4.34 seals theorem
      -- bodies behind `allowOpaque`.
      let internal (n : Name) : Bool := n.toString.contains "Poincare"
      let next : List Name :=
        if !internal c then []
        else
          match env.find? c with
          | none => []
          | some ci =>
            let t := ci.type.getUsedConstants.toList
            let v := match ci.value? true with
              | some e => e.getUsedConstants.toList
              | none => []
            (t ++ v).filter (fun n => internal n && !seen.contains n)
      reaches env target seen (next ++ rest)

/-- Claimed `(downstream, constructor)` pairs, transcribed from the D12 result cards.
The `String` is the task id. -/
def claimedPairs : List (String × Name × Name) := [
  ("D12-connection-curvature", "Poincare.D12.ConnectionCurvature.milnorConnection".toName, "Poincare.D12.ConnectionCurvature.leviCivitaExists".toName),
  ("D12-connection-curvature", "Poincare.D12.ConnectionCurvature.leviCivitaExists".toName, "Poincare.D12.ConnectionCurvature.SoThreeModel.so3MeanLeviCivita".toName),
  ("D12-connection-curvature", "Poincare.D12.ConnectionCurvature.leviCivitaExists".toName, "Poincare.D12.ConnectionCurvature.SoThreeModel.so3_ricci_e00".toName),
  ("D12-connection-curvature", "Poincare.D12.ConnectionCurvature.milnorConnection".toName, "Poincare.D12.ConnectionCurvature.SoThreeModel.so3_ricci_e00".toName),
  ("D12-entropy-variation", "Poincare.D12.EntropyVariation.hasDerivAt_F_of_pointwise".toName, "Poincare.D12.EntropyVariation.fflow_F_hasDerivAt".toName),
  ("D12-entropy-variation", "Poincare.D12.EntropyVariation.fflow_F_hasDerivAt".toName, "Poincare.D12.EntropyVariation.fflow_F_hasDerivAt_closedForm".toName),
  ("D12-entropy-variation", "Poincare.D12.EntropyVariation.fflow_F_hasDerivAt_closedForm".toName, "Poincare.D12.EntropyVariation.fflow_F_deriv_pos".toName),
  ("D12-entropy-variation", "Poincare.D12.EntropyVariation.fflow_F_deriv_pos".toName, "Poincare.D12.EntropyVariation.fflow_F_strictMonoOn".toName),
  ("D12-entropy-variation", "Poincare.D12.EntropyVariation.fflow_F_strictMonoOn".toName, "Poincare.D12.EntropyVariation.derivative_sign_distinction".toName),
  ("D12-heat-domain-repair", "Poincare.D12.HeatDomain.notIntegrable_fast_times_kernel".toName, "Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos".toName),
  ("D12-heat-domain-repair", "Poincare.D12.HeatDomain.not_fullInitialCondition_flat_of_pos".toName, "Poincare.D12.HeatDomain.flat_positive_dimension_weak_not_full".toName),
  ("D12-heat-domain-repair", "Poincare.D12.HeatDomain.toHeatKernelData_of_weak_compact_finiteMeasure".toName, "Poincare.D7.HeatKernel.punitHeatKernelData".toName),
  ("D12-heat-domain-repair", "Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_integrableClass".toName, "Poincare.D12.HeatDomain.flatHeatKernelCore_weakInitialConditionFor_ccClass".toName),
  ("D12-heat-semigroup-analysis", "Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_of_bounded".toName, "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp".toName),
  ("D12-heat-semigroup-analysis", "Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator".toName, "Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator_integral_norm_eq_zero".toName),
  ("D12-heat-semigroup-analysis", "Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator".toName, "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp".toName),
  ("D12-heat-semigroup-analysis", "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp".toName, "Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1_tendsto_seq".toName),
  ("D12-kappa-variational", "Poincare.D12.KappaVariational.gaussianReducedVolume_eq_one".toName, "Poincare.D12.KappaVariational.gaussianReducedVolumeCertificate_volume".toName),
  ("D12-kappa-variational", "Poincare.D12.KappaVariational.gaussianReducedVolumeViaL_eq_one".toName, "Poincare.D12.KappaVariational.gaussianUniformReducedVolumeLowerBound".toName),
  ("D12-kappa-variational", "Poincare.D12.KappaVariational.constantCurvatureLMinimizerExistence".toName, "Poincare.D12.KappaVariational.constantCurvature_reducedLength_le".toName),
  ("D12-parabolic-local-existence", "Poincare.D12.ParabolicLocal.heatConv_semigroup".toName, "Poincare.D12.ParabolicLocal.linearCandidate_isFixedPt".toName),
  ("D12-parabolic-local-existence", "Poincare.D12.ParabolicLocal.gaussianS_add".toName, "Poincare.D12.ParabolicLocal.linearCandidate_isFixedPt".toName),
  ("D12-parabolic-local-existence", "Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC".toName, "Poincare.D12.ParabolicLocal.gaussianS_tendsto_self".toName),
  ("D12-parabolic-local-existence", "Poincare.D12.ParabolicLocal.heatConv_tendsto_self_BUC".toName, "Poincare.D12.ParabolicLocal.gaussianSmap_continuous".toName),
  ("D12-parabolic-local-existence", "Poincare.D12.ParabolicLocal.derivativeLossBarrier_holds".toName, "Poincare.D12.ParabolicLocal.derivativeLossBarrier_discharged".toName),
  ("D12-surgery-recognition", "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2".toName, "Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition".toName),
  ("D12-surgery-recognition", "Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient".toName, "Poincare.D12.SurgeryRecognition.sphericalPieceRecognition_of_spaceForm".toName),
  ("D12-triangulation-topology", "Poincare.D12.TriangulationTopology.coveringOfSimplyConnectedIsHomeo".toName, "Poincare.D12.TriangulationTopology.sphericalSpaceFormRecognition".toName),
  ("D12-triangulation-topology", "Poincare.D12.TriangulationTopology.alexanderHomeo".toName, "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere".toName),
  ("D12-triangulation-topology", "Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere".toName, "Poincare.D12.TriangulationTopology.sphereOfTwoDisks".toName),
  ]

end Poincare.D13.IntegratedAudit

open Poincare.D13.IntegratedAudit in
run_cmd do
  let env ← getEnv
  -- `claimedPairs` entries are `(task, constructor, downstream)`.
  for (task, ctor, down) in claimedPairs do
    let existsD := (env.find? down).isSome
    let existsC := (env.find? ctor).isSome
    if !existsD || !existsC then
      IO.println s!"D13DEP\t{task}\t{down}\t{ctor}\tEXISTS_FAIL\t{existsD}\t{existsC}"
    else
      let some dci := env.find? down | throwError "unreachable"
      let inType := reaches env ctor #[] dci.type.getUsedConstants.toList
      let inProof := match dci.value? true with
        | some v => reaches env ctor #[] v.getUsedConstants.toList
        | none => reaches env ctor #[] dci.type.getUsedConstants.toList
      IO.println s!"D13DEP\t{task}\t{down}\t{ctor}\t{inType}\t{inProof}"
