/- SEMREV cited-declaration compile check: every cited name must #check. -/
import Poincare.D12.VolumeIBP
import Poincare.D12.VolumeIBP.Basic
import Poincare.D12.VolumeIBP.Blocked
import Poincare.D12.VolumeIBP.ChangeOfVariables
import Poincare.D12.VolumeIBP.Compat
import Poincare.D12.VolumeIBP.Divergence
import Poincare.D12.VolumeIBP.Example
import Poincare.D12.VolumeIBP.IBP
import Poincare.D12.VolumeIBP.Regularity
import Poincare.D13
import Poincare.D13.BochnerFlat
import Poincare.D13.Bridge
import Poincare.D13.CertificateOn
import Poincare.D13.EuclideanChart
import Poincare.D13.GaussianF
import Poincare.D13.GaussianMoment
import Poincare.D13.HeatBridge
import Poincare.D13.HeatKernelBridge
import Poincare.D13.ManifoldIBP
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
import Poincare.D13.Riemannian
import Poincare.D13.Riemannian.AtlasBridge
import Poincare.D13.Riemannian.AtlasPairing
import Poincare.D13.Riemannian.ChartMetricBridge
import Poincare.D13.Riemannian.MetricBridge
import Poincare.D13.Riemannian.MetricBridgeSmooth
import Poincare.D13.Riemannian.PullbackPairing
import Poincare.D13.VolumeForm
import Poincare.D13.VolumeForm.Basic
import Poincare.D13.VolumeForm.Gluing
import Poincare.D13.VolumeForm.Transformation

set_option autoImplicit false

#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_weightedIBP_unconditional
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_laplacianIntegralZero
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_integrable_dirichlet
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_dirichletEnergy
#check @Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.halfSpaceAtlas_greenIdentity
