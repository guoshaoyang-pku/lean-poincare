import Poincare.D13.ManifoldIBP.Blocked
import Poincare.D13.ManifoldIBP.ChartSum
import Poincare.D13.ManifoldIBP.DisjointModel
import Poincare.D13.ManifoldIBP.GlobalIBP
import Poincare.D13.ManifoldIBP.GlobalMeasure
import Poincare.D13.ManifoldIBP.IntegrableTransfer
import Poincare.D13.ManifoldIBP.OverlapIBP
import Poincare.D13.ManifoldIBP.OverlapIBPData
import Poincare.D13.ManifoldIBP.OverlapIBPModel
import Poincare.D13.ManifoldIBP.OverlapModel
import Poincare.D13.ManifoldIBP.OverlapOperatorCheck
import Poincare.D13.ManifoldIBP.POUAssembly
import Poincare.D13.ManifoldIBP.POUAssemblyAE
import Poincare.D13.ManifoldIBP.POUConstruction
import Poincare.D13.ManifoldIBP.POUModel
import Poincare.D13.ManifoldIBP.PartialChartModel
import Poincare.D13.ManifoldIBP.PartialChartModelPOU
import Poincare.D13.ManifoldIBP.SmoothAtlas
import Poincare.D13.ManifoldIBP.SmoothAtlasIBP
import Poincare.D13.ManifoldIBP.SmoothAtlasModel
import Poincare.D13.ManifoldIBP.SmoothAtlasPartial
import Poincare.D13.ManifoldIBP.SmoothAtlasPartialAE
import Poincare.D13.ManifoldIBP.SmoothPartition
import Poincare.D13.ManifoldIBP.Transfer
import Poincare.D13.ManifoldIBP.VolumeFormBridge
import Poincare.D13.Riemannian.AtlasBridge
import Poincare.D13.Riemannian.AtlasPairing
import Poincare.D13.Riemannian.ChartMetricBridge
import Poincare.D13.Riemannian.MetricBridge
import Poincare.D13.Riemannian.MetricBridgeSmooth
import Poincare.D13.Riemannian.PullbackPairing
import Poincare.D13.VolumeForm.Basic
import Poincare.D13.VolumeForm.Gluing
import Poincare.D13.VolumeForm.Transformation

set_option pp.explicit false
set_option pp.universes false

-- ==== structures ====
#print Poincare.D13.ManifoldIBP.OverlapAtlas
#print Poincare.D13.ManifoldIBP.SmoothOverlapAtlas
#print Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.IsTotal
#print Poincare.D13.ManifoldIBP.ManifoldAtlasData
#print Poincare.D13.ManifoldIBP.ChartSumData
#print Poincare.D13.Riemannian.SmoothChartMetric
#print Poincare.D13.VolumeForm.ChartPartitionOfUnity

-- ==== Blocked (statement-only) ====
#check @Poincare.D13.ManifoldIBP.manifoldGluingConstructionExists
#check @Poincare.D13.ManifoldIBP.smoothPartitionOfUnityExists
#check @Poincare.D13.ManifoldIBP.closedManifoldEntropyIdentity
#check @Poincare.D13.ManifoldIBP.manifoldStokesTheorem
#check @Poincare.D13.ManifoldIBP.orientedAtlasVolumeForm

-- ==== ChartSum (namespace ChartSumData) ====
#check @Poincare.D13.ManifoldIBP.ChartSumData.globalWeightedIBP
#check @Poincare.D13.ManifoldIBP.ChartSumData.globalLaplacianIntegralZero
#check @Poincare.D13.ManifoldIBP.ChartSumData.globalDivergenceIntegralZero
#check @Poincare.D13.ManifoldIBP.ChartSumData.globalUnweightedIBP
#check @Poincare.D13.ManifoldIBP.ChartSumData.globalIntegral

-- ==== GlobalIBP ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_finset
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalIBP_finset

-- ==== GlobalMeasure ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure_apply_eq
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_eq_chartMeasure_of_cover
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.density_transform
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure_apply
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.chartMeasure

-- ==== IntegrableTransfer ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_chartMeasure_iff
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_globalMeasure_iff
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.integrable_globalMeasure_withDensity_of_supported

-- ==== OverlapIBP (main chart-supported manifold IBP) ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.integral_globalMeasure_withDensity_of_supported
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported_smul
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalIBP_of_chartSupported
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalLaplacianIntegralZero_of_chartSupported

-- ==== OverlapIBPData / OverlapIBPModel ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoData_weightedIBP
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_ibp
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_laplacianIntegralZero
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_dirichletEnergy

-- ==== POU pipeline ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.eq_sum_of_pou
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_pouData
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_chartSupported_ae
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_finset_ae
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalWeightedIBP_of_pouData_ae

-- ==== SmoothAtlas / SmoothAtlasIBP ====
#check @Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift
#check @Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou
#check @Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou'
#check @Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial
#check @Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_pou_partial_ae
#check @Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.lift_apply_chart_of_support

-- ==== SmoothAtlasModel ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoSmooth
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwoSmooth_isTotal
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_via_pou

-- ==== POUModel / POUConstruction ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.exists_pou_dilationTwo
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_pou_weightedIBP
#check @Poincare.D13.ManifoldIBP.SmoothOverlapAtlas.globalWeightedIBP_of_cover_partial_ae
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_of_cover_chartOne

-- ==== PartialChartModel / PartialChartModelPOU ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_frontier_volume_zero
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.not_isTotal_halfSpaceAtlas
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_of_pou_partial_ae
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero

-- ==== SmoothPartition ====
#check @Poincare.D13.ManifoldIBP.exists_contDiff_bump
#check @Poincare.D13.ManifoldIBP.exists_smooth_partitionOfUnity_subordinate

-- ==== Transfer ====
#check @Poincare.D13.ManifoldIBP.manifoldWeightedIBP_of_atlasData
#check @Poincare.D13.ManifoldIBP.laplacianIntegral_eq_chartSum
#check @Poincare.D13.ManifoldIBP.gradInnerIntegral_eq_chartSum

-- ==== VolumeFormBridge ====
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.chartVolumeForm_stdFrame_eq_density
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_apply_chart_volumeForm
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.globalMeasure_apply_volumeForm_of_cover
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_volume_univ

-- ==== Riemannian ====
#check @Poincare.D13.Riemannian.metric_transform_chartTransition
#check @Poincare.D13.Riemannian.fderivWithin_chartTransition_eq_of_isOpen
#check @Poincare.D13.Riemannian.metric_transform_chartOverlap
#check @Poincare.D13.Riemannian.chartOverlap_eq_overlapOf
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.gradInnerInverse_chartTransition
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.gradInnerInverse_chartTransition_mul
#check @Poincare.D13.Riemannian.contDiffOn_chartMetricCoeff
#check @Poincare.D13.Riemannian.posDef_chartMetricCoeffExt
#check @Poincare.D13.Riemannian.extendedSmoothChartMetric_g_eq_genuine
#check @Poincare.D13.Riemannian.extendedChartMetric_g_eq_genuine
#check @Poincare.D13.Riemannian.chartGramMatrix_det_change
#check @Poincare.D13.Riemannian.chartGramMatrix_sqrt_det_change
#check @Poincare.D13.Riemannian.chartGramMatrix_posDef
#check @Poincare.D13.Riemannian.contMDiffOn_chartFrameSection
#check @Poincare.D13.Riemannian.contDiffOn_chartGramMatrix_coord
#check @Poincare.D13.Riemannian.gradInnerInverse_pullbackMetric

-- ==== VolumeForm ====
#check @Poincare.D13.VolumeForm.euclideanVolumeForm_apply
#check @Poincare.D13.VolumeForm.chartVolumeForm_apply
#check @Poincare.D13.VolumeForm.chartVolumeForm_positive_on_standardFrame
#check @Poincare.D13.VolumeForm.signedVolume_orthonormal_basis_invariant
#check @Poincare.D13.VolumeForm.ChartPartitionOfUnity.exists_pos
#check @Poincare.D13.VolumeForm.gluedDensity_eq_of_supportCompatible
#check @Poincare.D13.VolumeForm.integral_gluedDensity_eq_sum
#check @Poincare.D13.VolumeForm.chartVolumeForm_pullback_general
#check @Poincare.D13.VolumeForm.chartVolumeForm_pullback_orientationPreserving_map
#check @Poincare.D13.VolumeForm.chartVolumeForm_pullback_euclidean
