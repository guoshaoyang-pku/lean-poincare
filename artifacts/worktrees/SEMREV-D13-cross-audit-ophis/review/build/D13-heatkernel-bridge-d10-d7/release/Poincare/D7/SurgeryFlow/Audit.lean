/-
Copyright (c) 2026 The Poincaré formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-surgery-neck-extinction)

**D7 surgery flow: generated kernel axiom audit.**

`#print axioms` for every declaration of `Poincare.D7.SurgeryFlow`.  The expected cones are the
standard ones only: `{}`, `{propext}`, and `{propext, Classical.choice, Quot.sound}`.
-/

import Poincare.D7.SurgeryFlow.All

set_option autoImplicit false

#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.toSurgeryCertificate
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.compact_preserved
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.orientable_preserved
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.simplyConnected_preserved
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck_model_radius
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck_radius_pos
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck_approx_distortion
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck_antipodal_dist
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.curvatureScale
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.noncollapsing
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.certificate_scale_pos
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain.toSurgeryChain
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain.toSurgeryChain_nil
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain.toSurgeryChain_step
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain.certificate
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain.compact_preserved
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain.orientable_preserved
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain.simplyConnected_preserved
#print axioms Poincare.D7.SurgeryFlow.realLineTop
#print axioms Poincare.D7.SurgeryFlow.realLineDatum
#print axioms Poincare.D7.SurgeryFlow.realLineProcedure
#print axioms Poincare.D7.SurgeryFlow.exists_surgeryProcedureData
#print axioms Poincare.D7.SurgeryFlow.realLineProcedure_neck_radius
#print axioms Poincare.D7.SurgeryFlow.realLineProcedureChain
#print axioms Poincare.D7.SurgeryFlow.realLineProcedureChain_toSurgeryChain
#print axioms Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.strictMono
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.gap_mul_le_add
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.gap_mul_le_sub
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.gap_le_sub
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.gap_le_abs_sub
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.range_inter_Ioo_subsingleton
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.range_inter_Ioo_eq_singleton
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.isDiscrete_range
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.not_accPt
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.isClosed_range
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.derivedSet_range
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.isClosed_and_isDiscrete_range
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.finite_indices_Icc
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.finite_range_inter_Icc
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.finite_range_inter_Ioo
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface.toSchedule
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface.isDiscrete_range
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface.not_accPt
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface.derivedSet_range
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface.isClosed_and_isDiscrete_range
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface.finite_range_inter_Icc
#print axioms Poincare.D7.SurgeryFlow.procedureTimes
#print axioms Poincare.D7.SurgeryFlow.procedureTimes_derivedSet_eq_empty
#print axioms Poincare.D7.SurgeryFlow.procedureTimes_finite_range_inter_Icc
#print axioms Poincare.D7.SurgeryFlow.no_infinite_strict_decrease
#print axioms Poincare.D7.SurgeryFlow.no_infinite_steps
#print axioms Poincare.D7.SurgeryFlow.FiniteComplexity
#print axioms Poincare.D7.SurgeryFlow.finiteComplexity_toyRel
#print axioms Poincare.D7.SurgeryFlow.no_infinite_toyRel
#print axioms Poincare.D7.SurgeryFlow.toyChain_to_one
#print axioms Poincare.D7.SurgeryFlow.toy_extinction
#print axioms Poincare.D7.SurgeryFlow.toyChain_to_one_length
#print axioms Poincare.D7.SurgeryFlow.toyChain_length_unique
#print axioms Poincare.D7.SurgeryFlow.toy_extinction_bound
#print axioms Poincare.D7.SurgeryFlow.toy_extinction_time_le
#print axioms Poincare.D7.SurgeryFlow.toy_extinction_time_unique
#print axioms Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses
#print axioms Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.certifiedNeckSeparating_of_highCurvature
#print axioms Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.admissibleCutAndCap_of_highCurvature
#print axioms Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.realizesDatum_of_highCurvature
#print axioms Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.target_of_highCurvature
#print axioms Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.certificate
#print axioms Poincare.D7.SurgeryFlow.missingFullNeckAnalysis
#print axioms Poincare.D7.SurgeryFlow.missingFullNeckAnalysis_iff
#print axioms Poincare.D7.SurgeryFlow.exists_separating_of_missingFullNeckAnalysis
#print axioms Poincare.D7.SurgeryFlow.missingAPrioriCurvatureEstimates
#print axioms Poincare.D7.SurgeryFlow.missingAPrioriCurvatureEstimates_iff
#print axioms Poincare.D7.SurgeryFlow.discrete_times_of_missingAPrioriEstimates
#print axioms Poincare.D7.SurgeryFlow.finitelyMany_of_missingAPrioriEstimates
#print axioms Poincare.D7.SurgeryFlow.ExtinctionData
#print axioms Poincare.D7.SurgeryFlow.ExtinctionData.finitelyMany_surgeries
#print axioms Poincare.D7.SurgeryFlow.ExtinctionData.extinct_of_skeleton
#print axioms Poincare.D7.SurgeryFlow.ExtinctionData.terminalSphere_of_skeleton
#print axioms Poincare.D7.SurgeryFlow.missingExtinctionTheorem
#print axioms Poincare.D7.SurgeryFlow.missingExtinctionTheorem_iff
#print axioms Poincare.D7.SurgeryFlow.extinct_of_missingExtinctionTheorem
#print axioms Poincare.D7.SurgeryFlow.terminalSphere_of_missingExtinctionTheorem
#print axioms Poincare.D7.SurgeryFlow.toy_extinction_skeleton
#print axioms Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem
#print axioms Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem_iff
#print axioms Poincare.D7.SurgeryFlow.surgeryFlow_consequences
#print axioms Poincare.D7.SurgeryFlow.surgeryFlow_consequences_of_missing
#print axioms Poincare.D7.SurgeryFlow.BlockerNeckSeparating
#print axioms Poincare.D7.SurgeryFlow.BlockerCutAndCap
#print axioms Poincare.D7.SurgeryFlow.BlockerScaleCompatible
#print axioms Poincare.D7.SurgeryFlow.BlockerAPriori
#print axioms Poincare.D7.SurgeryFlow.BlockerExtinction
#print axioms Poincare.D7.SurgeryFlow.BlockerTerminalSphere
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowDependencies
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowDependencies_length
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowDependencies_ne_nil
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowDependencies_all_named
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowBlockers
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowBlockers_length
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowBlockers_ne_nil
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowBlockers_all_named
