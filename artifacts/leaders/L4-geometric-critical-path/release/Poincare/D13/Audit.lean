/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (axiom audit)

# Axiom audit for the D13 layer (fail-closed)

`#print axioms` for every D13 declaration. The whole layer must depend only on
`propext`, `Classical.choice`, `Quot.sound` (the mathlib standard cone). A negative
control (`negativeControl`, never used by any theorem) is declared with `axiom` so the
audit can prove it is not vacuous: it must appear with its own name in the cone.
-/
import Poincare.D13.Bridge
import Poincare.D13.EuclideanChart
import Poincare.D13.BochnerFlat
import Poincare.D13.HeatBridge
import Poincare.D13.CertificateOn
import Poincare.D13.GaussianF
import Poincare.D13.HeatKernelBridge
import Poincare.D13.ManifoldIBP.DisjointModel
import Poincare.D13.Riemannian
import Poincare.D13.ManifoldIBP.OverlapIBPModel
import Poincare.D13.ManifoldIBP.OverlapIBPData
import Poincare.D13.ManifoldIBP.OverlapOperatorCheck
import Poincare.D13.ManifoldIBP.VolumeFormBridge
import Poincare.D13.ManifoldIBP.SmoothPartition
import Poincare.D13.ManifoldIBP.GlobalIBP
import Poincare.D13.ManifoldIBP.POUAssembly
import Poincare.D13.ManifoldIBP.POUModel
import Poincare.D13.ManifoldIBP.SmoothAtlas
import Poincare.D13.ManifoldIBP.SmoothAtlasIBP
import Poincare.D13.ManifoldIBP.SmoothAtlasModel
import Poincare.D13.ManifoldIBP.SmoothAtlasPartial
import Poincare.D13.ManifoldIBP.POUAssemblyAE
import Poincare.D13.ManifoldIBP.SmoothAtlasPartialAE
import Poincare.D13.ManifoldIBP.PartialChartModel
import Poincare.D13.ManifoldIBP.IntegrableTransfer
import Poincare.D13.ManifoldIBP.PartialChartModelPOU
import Poincare.D13.ManifoldIBP.POUConstruction

namespace Poincare.D13

/-- Negative control: if the audit machinery were blind, this would pollute cones. -/
axiom negativeControl : False

#check negativeControl

namespace Audit

open Poincare.D13.VolumeForm
open Poincare.D13.ManifoldIBP

/- VolumeForm.Basic -/
#print axioms stdOrientation
#print axioms euclideanVolumeForm
#print axioms euclideanVolumeForm_apply
#print axioms euclideanVolumeForm_ne_zero
#print axioms euclideanVolumeForm_stdFrame
#print axioms orientationVolumeForm_eq_basisDet
#print axioms chartVolumeForm
#print axioms chartVolumeForm_apply
#print axioms chartVolumeForm_ne_zero
#print axioms chartVolumeForm_positive_on_standardFrame
#print axioms chartVolumeForm_euclidean
#print axioms signedVolume
#print axioms signedVolume_eq_det
#print axioms signedVolume_orthonormal_basis_invariant
/- VolumeForm.Transformation -/
#print axioms sign_mul_eq_abs
#print axioms det_matrix_of_fderiv_frame
#print axioms chartVolumeForm_pullback_general
#print axioms chartVolumeForm_pullback_orientationPreserving
#print axioms chartVolumeForm_pullback_orientationPreserving_map
#print axioms chartVolumeForm_pullback_euclidean
/- VolumeForm.Gluing -/
#print axioms ChartPartitionOfUnity.exists_pos
#print axioms ChartPartitionOfUnity.gluedDensity
#print axioms ChartPartitionOfUnity.gluedDensity_nonneg
#print axioms ChartPartitionOfUnity.gluedDensity_measurable
#print axioms ChartPartitionOfUnity.gluedDensity_eq_of_common
#print axioms ChartPartitionOfUnity.gluedDensity_eq_of_supportCompatible
#print axioms ChartPartitionOfUnity.integral_gluedDensity_eq_sum
/- ManifoldIBP.ChartSum -/
#print axioms ChartSumData.globalWeightedIBP
#print axioms ChartSumData.globalLaplacianIntegralZero
#print axioms ChartSumData.globalDivergenceIntegralZero
#print axioms ChartSumData.globalUnweightedIBP
/- ManifoldIBP.Transfer -/
#print axioms ManifoldAtlasData
#print axioms laplacianIntegral_eq_chartSum
#print axioms gradInnerIntegral_eq_chartSum
#print axioms manifoldWeightedIBP_of_atlasData
/- Bridge -/
#print axioms Poincare.D13.Bridge.euclideanChartCalculus
#print axioms Poincare.D13.Bridge.weightedLaplacianStatement_euclidean_holds
#print axioms Poincare.D13.Bridge.RealCalculus.realEuclideanCalculus
#print axioms Poincare.D13.Bridge.RealCalculus.gaussianWeightData
#print axioms Poincare.D13.Bridge.RealCalculus.laplacian_id_eq_zero
#print axioms Poincare.D13.Bridge.RealCalculus.rhsIntegrand_eq
#print axioms Poincare.D13.Bridge.RealCalculus.gaussianOverOnePlusSq_integral_pos
#print axioms Poincare.D13.Bridge.RealCalculus.unrestrictedWeightedIBPStatement_false
#print axioms Poincare.D13.Bridge.GaussianBackward.density_integral_one
/- EuclideanChart -/
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_eq_deriv_update
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_add
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_mul
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_apply_single
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_apply_single_of_ne
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_const_mul_coord
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_const
#print axioms Poincare.D13.EuclideanChart.ChartMetric.radSq
#print axioms Poincare.D13.EuclideanChart.ChartMetric.radSq_differentiableAt
#print axioms Poincare.D13.EuclideanChart.ChartMetric.radSq_update
#print axioms Poincare.D13.EuclideanChart.ChartMetric.update_self_eq
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_radial
#print axioms Poincare.D13.EuclideanChart.ChartMetric.partialDeriv_radial_second
#print axioms Poincare.D13.EuclideanChart.ChartMetric.euclidean_density_eq_one
#print axioms Poincare.D13.EuclideanChart.ChartMetric.euclidean_grad_eq
#print axioms Poincare.D13.EuclideanChart.ChartMetric.euclidean_laplacian_eq
#print axioms Poincare.D13.EuclideanChart.ChartMetric.laplacian_radial
/- BochnerFlat -/
#print axioms Poincare.D13.BochnerFlat.partialDeriv_contDiff_two
#print axioms Poincare.D13.BochnerFlat.partialDeriv_contDiff_one_flat
#print axioms Poincare.D13.BochnerFlat.differentiableAt_of_contDiff_two
#print axioms Poincare.D13.BochnerFlat.differentiableAt_of_contDiff_one
#print axioms Poincare.D13.BochnerFlat.partialDeriv_finset_sum
#print axioms Poincare.D13.BochnerFlat.partialDeriv_const_mul
#print axioms Poincare.D13.BochnerFlat.partialDeriv_partialDeriv_comm
#print axioms Poincare.D13.BochnerFlat.partialDeriv_gradInnerSq
#print axioms Poincare.D13.BochnerFlat.partialDeriv_gradInnerSq_second
#print axioms Poincare.D13.BochnerFlat.sum_partialDeriv_partialDeriv_eq
#print axioms Poincare.D13.BochnerFlat.bochnerIdentity_euclidean
#print axioms Poincare.D13.BochnerFlat.bochnerStatement_iff_forall
#print axioms Poincare.D13.BochnerFlat.gradInner_euclideanChartCalculus
#print axioms Poincare.D13.BochnerFlat.hessSq_euclideanChartCalculus
#print axioms Poincare.D13.BochnerFlat.bochnerIdentityOn_euclidean
/- HeatBridge -/
#print axioms Poincare.D13.HeatBridge.hasDerivAt_gaussProfile
#print axioms Poincare.D13.HeatBridge.deriv_gaussProfile
#print axioms Poincare.D13.HeatBridge.deriv_deriv_gaussProfile
#print axioms Poincare.D13.HeatBridge.hasDerivAt_gaussProfile_deriv
#print axioms Poincare.D13.HeatBridge.laplacian_gaussian
#print axioms Poincare.D13.HeatBridge.gaussDensity
#print axioms Poincare.D13.HeatBridge.laplacian_gaussDensity
#print axioms Poincare.D13.HeatBridge.hasDerivAt_gaussDensity
#print axioms Poincare.D13.HeatBridge.gaussian_conjugate_heat
/- GaussianMoment -/
#print axioms Poincare.D13.GaussianMoment.hasDerivAt_sq_mul_exp_neg_mul_sq
#print axioms Poincare.D13.GaussianMoment.tendsto_mul_exp_neg_mul_sq_atTop
#print axioms Poincare.D13.GaussianMoment.integral_sq_mul_exp_neg_mul_sq_Ioi
#print axioms Poincare.D13.GaussianMoment.integral_sq_mul_exp_neg_mul_sq
#print axioms Poincare.D13.GaussianMoment.integral_vec_two_eq_prod
#print axioms Poincare.D13.GaussianMoment.radSq_eq_finTwoArrow
#print axioms Poincare.D13.GaussianMoment.integral_exp_neg_mul_radSq
#print axioms Poincare.D13.GaussianMoment.integral_radSq_mul_exp_neg_mul_radSq
#print axioms Poincare.D13.GaussianMoment.integrable_vec_two_iff
#print axioms Poincare.D13.GaussianMoment.integrable_radSq_mul_exp_neg_mul_radSq
#print axioms Poincare.D13.GaussianMoment.integrable_exp_neg_mul_radSq
#print axioms Poincare.D13.GaussianMoment.integral_gaussDensity
#print axioms Poincare.D13.GaussianMoment.integral_radSq_mul_gaussDensity
/- GaussianF -/
#print axioms Poincare.D13.GaussianF.integral_gradSq_mul_gaussDensity
#print axioms Poincare.D13.GaussianF.integral_FDissipation_gauss
#print axioms Poincare.D13.GaussianF.hasDerivAt_gaussianF
#print axioms Poincare.D13.GaussianF.hasDerivAt_gaussianF_integral
#print axioms Poincare.D13.GaussianF.contDiffOn_gaussianF
/- CertificateOn -/
#print axioms Poincare.D13.CertificateOn.BochnerIdentityOn
#print axioms Poincare.D13.CertificateOn.RestrictedWeightedIBPStatement
#print axioms Poincare.D13.CertificateOn.ContinuousMonotoneCertificateOn
#print axioms Poincare.D13.CertificateOn.ContinuousMonotoneCertificateOn.monotoneOn
#print axioms Poincare.D13.CertificateOn.ContinuousMonotoneCertificateOn.F_ge_left
#print axioms Poincare.D13.CertificateOn.ContinuousMonotoneCertificateOn.toMonotoneCertificateOnIcc
#print axioms Poincare.D13.CertificateOn.FiniteLifetimeEntropyBridge
#print axioms Poincare.D13.CertificateOn.continuousMonotoneCertificateOn_of_bridge
#print axioms Poincare.D13.CertificateOn.monotoneOn_of_bridge
#print axioms Poincare.D13.CertificateOn.continuousMonotoneCertificateOn_of_bridge_dissipation
/- ManifoldIBP.DisjointModel: the concrete glued-measure model -/
#print axioms Poincare.D13.ManifoldIBP.DisjointAtlas
#print axioms Poincare.D13.ManifoldIBP.weightedChartMeasure
#print axioms Poincare.D13.ManifoldIBP.integral_weightedChartMeasure
#print axioms Poincare.D13.ManifoldIBP.disjointAtlasMeasure
#print axioms Poincare.D13.ManifoldIBP.integral_disjointAtlasMeasure
#print axioms Poincare.D13.ManifoldIBP.disjointAtlasData
#print axioms Poincare.D13.ManifoldIBP.integrable_driftLaplacian_mul_weightedChartMeasure
#print axioms Poincare.D13.ManifoldIBP.integrable_gradInner_mul_weightedChartMeasure
#print axioms Poincare.D13.ManifoldIBP.integrable_driftLaplacian_mul_disjointAtlasMeasure
#print axioms Poincare.D13.ManifoldIBP.integrable_gradInner_mul_disjointAtlasMeasure
#print axioms Poincare.D13.ManifoldIBP.disjointAtlas_weightedIBP
/- HeatKernelBridge: the checked Gaussian consumption -/
#print axioms Poincare.D13.HeatKernelBridge.gaussTau
#print axioms Poincare.D13.HeatKernelBridge.gaussTau_of_le
#print axioms Poincare.D13.HeatKernelBridge.gaussTau_of_ge
#print axioms Poincare.D13.HeatKernelBridge.gaussTau_pos
#print axioms Poincare.D13.HeatKernelBridge.gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.exp_neg_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.contDiff_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.F_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.FDissipation_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.restrictedWeightedIBP_euclideanChartCalculus
#print axioms Poincare.D13.HeatKernelBridge.partialDeriv_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.partialDeriv_partialDeriv_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.gradInner_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.hessSq_gaussPotential
#print axioms Poincare.D13.HeatKernelBridge.hasConjugateWeight_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.extra_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.W_gaussEntropyData
#print axioms Poincare.D13.HeatKernelBridge.W_gauss_antitone
#print axioms Poincare.D13.HeatKernelBridge.hasDerivAt_gaussianW
#print axioms Poincare.D13.HeatKernelBridge.gaussCalculus
#print axioms Poincare.D13.HeatKernelBridge.finiteLifetimeEntropyBridge_gaussian
#print axioms Poincare.D13.HeatKernelBridge.monotoneOn_F_gaussian
#print axioms Poincare.D13.HeatKernelBridge.F_gauss_mono
#print axioms Poincare.D13.HeatKernelBridge.F_gauss_initial_le
#print axioms Poincare.D13.HeatKernelBridge.monotoneCertificate_gaussian
/- ManifoldIBP.GlobalMeasure: the overlapping-atlas Riemannian measure and its
   chart-independence (the port of MorganTianLib/Ch01/RiemannianMeasure.lean to the pin) -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.det_jacobianOf
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.det_matrix_transform
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.density_transform
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure_apply
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure_apply_eq
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_apply_chart
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_restrict_eq_chartMeasure
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_eq_chartMeasure_of_cover
/- ManifoldIBP.OverlapModel: the inhabited dilation-chart overlapping atlas -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_eq_jacobianMatrix
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianMatrix_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_one_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_id
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.pullbackMatrix_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.smul_one_conj_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.conj_smul_one
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.one_conj
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilate_matrix
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationChart_image_univ
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.overlapOf_dilationChart
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlas
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlas_chartMeasure_univ_eq
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlas_globalMeasure_eq_chartMeasure
/- ManifoldIBP.OverlapIBP: the manifold IBP on the glued overlapping-atlas measure -/
#print axioms Poincare.D13.ManifoldIBP.integral_eq_restrict_of_support
#print axioms Poincare.D13.ManifoldIBP.setIntegral_eq_integral_of_support
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.weight
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.weight_toReal
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.measurable_weight
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integral_chartMeasure_of_supported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integral_globalMeasure_of_supported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integral_globalMeasure_withDensity_of_supported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.weight_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalIBP_of_chartSupported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalLaplacianIntegralZero_of_chartSupported
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported_smul
/- ManifoldIBP.OverlapIBPModel: the unconditional model instance -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_image_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_metric_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chart_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_integral_eq_chart
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_chart
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weight_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_withDensity_weight_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_ibp
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_laplacianIntegralZero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_dirichletEnergy
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chartMeasure_eq
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chart_one
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_metric_one
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_density_one
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chart_integral_eq
/- ManifoldIBP.OverlapIBPData: the overlapping-atlas measure inhabits ManifoldAtlasData -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_globalMeasure_eq_chartMeasure
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chartMeasure_absolutelyContinuous
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoData
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoData_weightedIBP
/- ManifoldIBP.OverlapOperatorCheck: chart-independence of the gradient pairing on the model -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.invMatrix_dilate
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.partialDeriv_comp_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_gradInnerInverse
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_gradInnerInverse_chart_independent
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.fderiv_const_smul_comp_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_density
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_grad
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_weightedDivergence
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_laplacian
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_driftLaplacian
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_driftLaplacian_chart_independent
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_chartOne
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chartOne_laplacianIntegral_eq
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chartOne_pairingIntegral_eq
/- ManifoldIBP.VolumeFormBridge: the measure is induced by the chart volume forms -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.chartVolumeForm_stdFrame_eq_density
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_apply_chart_volumeForm
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_apply_volumeForm_of_cover
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_volume_univ
/- Riemannian metric bridge (invocation 5) -/
#print axioms Poincare.D13.Riemannian.trivializationAt_symm_eq_tangentCoordChange
#print axioms Poincare.D13.Riemannian.trivializationAt_symm_eq_sum
#print axioms Poincare.D13.Riemannian.chartGramMatrix_change_apply
#print axioms Poincare.D13.Riemannian.chartGramMatrix_change
#print axioms Poincare.D13.Riemannian.chartGramMatrix_det_change
#print axioms Poincare.D13.Riemannian.chartGramMatrix_sqrt_det_change
#print axioms Poincare.D13.Riemannian.chartGramMatrix_isHermitian
#print axioms Poincare.D13.Riemannian.chartFrameVec_linearIndependent
#print axioms Poincare.D13.Riemannian.chartGramMatrix_posDef
#print axioms Poincare.D13.Riemannian.chartGramMatrix_det_pos
#print axioms Poincare.D13.Riemannian.tangentCoordChange_eq_fderivWithin_chartTransition
#print axioms Poincare.D13.Riemannian.chartGramMatrix_change_chartTransition
#print axioms Poincare.D13.Riemannian.jacobianOf_eq_toMatrix
#print axioms Poincare.D13.Riemannian.metric_transform_chartTransition
#print axioms Poincare.D13.Riemannian.fderivWithin_chartTransition_eq_of_isOpen
#print axioms Poincare.D13.Riemannian.chartOverlap_eq_overlapOf
#print axioms Poincare.D13.Riemannian.metric_transform_chartOverlap
#print axioms Poincare.D13.Riemannian.contMDiffOn_chartFrameSection
#print axioms Poincare.D13.Riemannian.contMDiffOn_chartGramMatrix_entry
#print axioms Poincare.D13.Riemannian.contDiffOn_chartGramMatrix_coord
#print axioms Poincare.D13.Riemannian.contDiff_chartMetricCoeffExt_mul
#print axioms Poincare.D13.Riemannian.posDef_chartMetricCoeffExt
#print axioms Poincare.D13.Riemannian.extendedSmoothChartMetric
#print axioms Poincare.D13.Riemannian.extendedSmoothChartMetric_g_eq_genuine
#print axioms Poincare.D13.Riemannian.contDiff_chartMetricCoeffExt_mul_top
#print axioms Poincare.D13.Riemannian.extendedChartMetric
#print axioms Poincare.D13.Riemannian.extendedChartMetric_g_eq_genuine

/- invocation 6: smooth partition of unity on Vec d (U7-GLOBAL-POU) -/
#print axioms Poincare.D13.ManifoldIBP.exists_contDiff_bump
#print axioms Poincare.D13.ManifoldIBP.exists_smooth_partitionOfUnity_subordinate

/- invocation 6: finite-decomposition global IBP and pairing linearity -/
#print axioms Poincare.D13.ManifoldIBP.gradInnerInverse_finset_sum
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_finset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalIBP_finset

/- invocation 6: pullback invariance of the inverse-metric gradient pairing -/
#print axioms Poincare.D13.Riemannian.metricInnerInverse_eq_dotProduct
#print axioms Poincare.D13.Riemannian.dotProduct_mulVec_transpose
#print axioms Poincare.D13.Riemannian.partialDeriv_comp
#print axioms Poincare.D13.Riemannian.jacobianMatrix_det_ne_zero_of_injective
#print axioms Poincare.D13.Riemannian.inv_congruence
#print axioms Poincare.D13.Riemannian.inv_pullbackMatrix
#print axioms Poincare.D13.Riemannian.gradInnerInverse_congruence
#print axioms Poincare.D13.Riemannian.gradInnerInverse_pullbackMetric

/- invocation 6: chart-independence of the pairing on an overlapping atlas -/
#print axioms Poincare.D13.ManifoldIBP.jacobianOf_eq_jacobianMatrix
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.gradInnerInverse_chartTransition
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.gradInnerInverse_chartTransition_mul

/- invocation 6: partition-of-unity assembly of the global IBP -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.eq_sum_of_pou
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_pouData

/- invocation 6: partition-of-unity consumption on the dilation model -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.exists_pou_dilationTwo
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.tsupport_comp_const_smul_subset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.tsupport_piece_one_subset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.tsupport_piece_zero_subset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_pou_pairing_reassembly
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chart_image_univ
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_pou_weightedIBP

/- invocation 6: smooth atlas structure and the lifted partition-of-unity pieces -/
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift_apply_chart
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.support_lift_subset
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.measurable_lift
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift_apply_chart_of_mem
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.support_lift_subset_tsupport
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.overlapOf_eq_univ
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.transition_transition
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift_apply_chart_total
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPiece
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPairing
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPiece_apply
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPiece_chart
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPairing_apply
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.measurable_pouPiece
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.measurable_pouPairing
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.sum_pouPairing
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou'

/- invocation 6: the dilation model inhabits the smooth total atlas structure -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoSmooth
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoSmooth_isTotal
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou

/- invocation 6: partial-chart lift, reassembly and global IBP -/
#print axioms Poincare.D13.ManifoldIBP.support_gradInnerInverse_subset
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift_apply_chart_of_support
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPiece_chart_of_support
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPiece_apply_of_mem
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.pouPairing_apply_of_mem
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.gradInnerInverse_eq_zero_of_eventuallyEq_zero
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.sum_pouPairing_of_support
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial

/- invocation 6: almost-everywhere support layer and the null-boundary partial-chart IBP -/
#print axioms Poincare.D13.ManifoldIBP.setIntegral_eq_integral_of_ae_support
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported_ae
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_finset_ae
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_pouData_ae
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.support_pouPairing_subset_chart
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae

/- invocation 6: the genuinely partial half-space atlas (identity on `{y 0 < 1}`, dilation by
`2` on `{0 < y 0}`), its null boundaries, and the within-set Jacobian lemmas -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_id_of_uniqueDiffWithinAt
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.jacobianOf_const_smul_of_uniqueDiffWithinAt
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.volume_frontier_halfSpaceSource0
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.volume_frontier_halfSpaceSource1
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_frontier_volume_zero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_source_ne_univ
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.not_isTotal_halfSpaceAtlas
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_transition_coherence
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_transition_preimage_isCompact
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.hsAtlas
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_of_pou_partial_ae

/- invocation 7: integrability transfer for chart-supported functions -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_chartMeasure_iff
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_globalMeasure_iff
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_globalMeasure_withDensity_of_supported

/- invocation 7: explicit POU on the half-space atlas and the unconditional partial-atlas IBP -/
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.hsStep
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.hsPsi
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.contDiff_hsPsi
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.hsPsi_sum
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.hasCompactSupport_hsPsi
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.support_laplacian_subset
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet

/- invocation 7: the general constructed-POU cover theorem and its model consumption -/
#print axioms Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover_chartOne

/- negative control -/
#print axioms negativeControl

end Audit

end Poincare.D13
