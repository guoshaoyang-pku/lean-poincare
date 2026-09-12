/-
Copyright (c) 2026 The Poincaré formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-surgery-neck-extinction)

**D7 surgery flow: generated API probe.**

Every declaration of `Poincare.D7.SurgeryFlow` is `#check`ed here, so that a missing or renamed
declaration fails the build.  Generated from the authored sources; no declarations of its own.
-/

import Poincare.D7.SurgeryFlow.All

set_option autoImplicit false

#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.toSurgeryCertificate
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.compact_preserved
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.orientable_preserved
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.simplyConnected_preserved
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck_model_radius
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck_radius_pos
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck_approx_distortion
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.neck_antipodal_dist
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.curvatureScale
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.noncollapsing
#check @Poincare.D7.SurgeryFlow.SurgeryProcedureData.certificate_scale_pos
#check @Poincare.D7.SurgeryFlow.ProcedureChain
#check @Poincare.D7.SurgeryFlow.ProcedureChain.toSurgeryChain
#check @Poincare.D7.SurgeryFlow.ProcedureChain.toSurgeryChain_nil
#check @Poincare.D7.SurgeryFlow.ProcedureChain.toSurgeryChain_step
#check @Poincare.D7.SurgeryFlow.ProcedureChain.certificate
#check @Poincare.D7.SurgeryFlow.ProcedureChain.compact_preserved
#check @Poincare.D7.SurgeryFlow.ProcedureChain.orientable_preserved
#check @Poincare.D7.SurgeryFlow.ProcedureChain.simplyConnected_preserved
#check @Poincare.D7.SurgeryFlow.realLineTop
#check @Poincare.D7.SurgeryFlow.realLineDatum
#check @Poincare.D7.SurgeryFlow.realLineProcedure
#check @Poincare.D7.SurgeryFlow.exists_surgeryProcedureData
#check @Poincare.D7.SurgeryFlow.realLineProcedure_neck_radius
#check @Poincare.D7.SurgeryFlow.realLineProcedureChain
#check @Poincare.D7.SurgeryFlow.realLineProcedureChain_toSurgeryChain
#check @Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected
#check @Poincare.D7.SurgeryFlow.SurgerySchedule
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.strictMono
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.gap_mul_le_add
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.gap_mul_le_sub
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.gap_le_sub
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.gap_le_abs_sub
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.range_inter_Ioo_subsingleton
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.range_inter_Ioo_eq_singleton
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.isDiscrete_range
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.not_accPt
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.isClosed_range
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.derivedSet_range
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.isClosed_and_isDiscrete_range
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.finite_indices_Icc
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.finite_range_inter_Icc
#check @Poincare.D7.SurgeryFlow.SurgerySchedule.finite_range_inter_Ioo
#check @Poincare.D7.SurgeryFlow.CurvatureBoundInterface
#check @Poincare.D7.SurgeryFlow.CurvatureBoundInterface.toSchedule
#check @Poincare.D7.SurgeryFlow.CurvatureBoundInterface.isDiscrete_range
#check @Poincare.D7.SurgeryFlow.CurvatureBoundInterface.not_accPt
#check @Poincare.D7.SurgeryFlow.CurvatureBoundInterface.derivedSet_range
#check @Poincare.D7.SurgeryFlow.CurvatureBoundInterface.isClosed_and_isDiscrete_range
#check @Poincare.D7.SurgeryFlow.CurvatureBoundInterface.finite_range_inter_Icc
#check @Poincare.D7.SurgeryFlow.procedureTimes
#check @Poincare.D7.SurgeryFlow.procedureTimes_derivedSet_eq_empty
#check @Poincare.D7.SurgeryFlow.procedureTimes_finite_range_inter_Icc
#check @Poincare.D7.SurgeryFlow.no_infinite_strict_decrease
#check @Poincare.D7.SurgeryFlow.no_infinite_steps
#check @Poincare.D7.SurgeryFlow.FiniteComplexity
#check @Poincare.D7.SurgeryFlow.finiteComplexity_toyRel
#check @Poincare.D7.SurgeryFlow.no_infinite_toyRel
#check @Poincare.D7.SurgeryFlow.toyChain_to_one
#check @Poincare.D7.SurgeryFlow.toy_extinction
#check @Poincare.D7.SurgeryFlow.toyChain_to_one_length
#check @Poincare.D7.SurgeryFlow.toyChain_length_unique
#check @Poincare.D7.SurgeryFlow.toy_extinction_bound
#check @Poincare.D7.SurgeryFlow.toy_extinction_time_le
#check @Poincare.D7.SurgeryFlow.toy_extinction_time_unique
#check @Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses
#check @Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.certifiedNeckSeparating_of_highCurvature
#check @Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.admissibleCutAndCap_of_highCurvature
#check @Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.realizesDatum_of_highCurvature
#check @Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.target_of_highCurvature
#check @Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.certificate
#check @Poincare.D7.SurgeryFlow.missingFullNeckAnalysis
#check @Poincare.D7.SurgeryFlow.missingFullNeckAnalysis_iff
#check @Poincare.D7.SurgeryFlow.exists_separating_of_missingFullNeckAnalysis
#check @Poincare.D7.SurgeryFlow.missingAPrioriCurvatureEstimates
#check @Poincare.D7.SurgeryFlow.missingAPrioriCurvatureEstimates_iff
#check @Poincare.D7.SurgeryFlow.discrete_times_of_missingAPrioriEstimates
#check @Poincare.D7.SurgeryFlow.finitelyMany_of_missingAPrioriEstimates
#check @Poincare.D7.SurgeryFlow.ExtinctionData
#check @Poincare.D7.SurgeryFlow.ExtinctionData.finitelyMany_surgeries
#check @Poincare.D7.SurgeryFlow.ExtinctionData.extinct_of_skeleton
#check @Poincare.D7.SurgeryFlow.ExtinctionData.terminalSphere_of_skeleton
#check @Poincare.D7.SurgeryFlow.missingExtinctionTheorem
#check @Poincare.D7.SurgeryFlow.missingExtinctionTheorem_iff
#check @Poincare.D7.SurgeryFlow.extinct_of_missingExtinctionTheorem
#check @Poincare.D7.SurgeryFlow.terminalSphere_of_missingExtinctionTheorem
#check @Poincare.D7.SurgeryFlow.toy_extinction_skeleton
#check @Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem
#check @Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem_iff
#check @Poincare.D7.SurgeryFlow.surgeryFlow_consequences
#check @Poincare.D7.SurgeryFlow.surgeryFlow_consequences_of_missing
#check @Poincare.D7.SurgeryFlow.BlockerNeckSeparating
#check @Poincare.D7.SurgeryFlow.BlockerCutAndCap
#check @Poincare.D7.SurgeryFlow.BlockerScaleCompatible
#check @Poincare.D7.SurgeryFlow.BlockerAPriori
#check @Poincare.D7.SurgeryFlow.BlockerExtinction
#check @Poincare.D7.SurgeryFlow.BlockerTerminalSphere
#check @Poincare.D7.SurgeryFlow.surgeryFlowDependencies
#check @Poincare.D7.SurgeryFlow.surgeryFlowDependencies_length
#check @Poincare.D7.SurgeryFlow.surgeryFlowDependencies_ne_nil
#check @Poincare.D7.SurgeryFlow.surgeryFlowDependencies_all_named
#check @Poincare.D7.SurgeryFlow.surgeryFlowBlockers
#check @Poincare.D7.SurgeryFlow.surgeryFlowBlockers_length
#check @Poincare.D7.SurgeryFlow.surgeryFlowBlockers_ne_nil
#check @Poincare.D7.SurgeryFlow.surgeryFlowBlockers_all_named
