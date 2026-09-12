/-
SEMREV independent use probe for D13-integrated-kernel-audit (written for the SEMREV review).
Checks existence, type-level and value-level occurrence of closure pairs, and reverse direct use.
-/
import Poincare.D10.BochnerEuclidean.Axioms
import Poincare.D10.BochnerEuclidean.Basic
import Poincare.D10.BochnerEuclidean.Bochner
import Poincare.D10.BochnerEuclidean.Compat
import Poincare.D10.BochnerEuclidean.Corollary
import Poincare.D10.GaussianToolbox.Basic
import Poincare.D10.GaussianToolbox.Convolution
import Poincare.D10.GaussianToolbox.Multivariate
import Poincare.D10.GaussianToolbox.PrintAxioms
import Poincare.D10.HeatKernelEuclidean.AxiomAudit
import Poincare.D10.HeatKernelEuclidean.Basic
import Poincare.D10.HeatKernelEuclidean.GaussianIntegral
import Poincare.D10.HeatKernelEuclidean.HeatEquation
import Poincare.D10.HeatKernelEuclidean.Mass
import Poincare.D10.HeatKernelEuclidean.Semigroup
import Poincare.D10.JacobiConstantCurvature.AxiomAudit
import Poincare.D10.JacobiConstantCurvature.Basic
import Poincare.D10.JacobiConstantCurvature.Comparison
import Poincare.D10.JacobiConstantCurvature.ODE
import Poincare.D10.MaximumPrincipleRN.AxiomAudit
import Poincare.D10.MaximumPrincipleRN.Basic
import Poincare.D10.MaximumPrincipleRN.SecondDerivativeTest
import Poincare.D10.MaximumPrincipleRN.Semidiscrete
import Poincare.D10.MaximumPrincipleRN.WeakMaximumPrinciple
import Poincare.D10.TriangulationLowDim.Audit
import Poincare.D10.TriangulationLowDim.Complex
import Poincare.D10.TriangulationLowDim.Models
import Poincare.D10.TriangulationLowDim.Moise
import Poincare.D11.BochnerManifold.Axioms
import Poincare.D11.BochnerManifold.Basic
import Poincare.D11.BochnerManifold.Corollaries
import Poincare.D11.BochnerManifold.D7Bridge
import Poincare.D11.BochnerManifold.ModelSpace
import Poincare.D11.BochnerManifold.Probe
import Poincare.D11.BochnerManifold.RadialBochner
import Poincare.D11.ComparisonModels.AxiomAudit
import Poincare.D11.ComparisonModels.Basic
import Poincare.D11.ComparisonModels.BishopGromov
import Poincare.D11.ComparisonModels.LaplacianComparison
import Poincare.D11.ComparisonModels.ModelMetrics
import Poincare.D11.HeatKernelBridge.All
import Poincare.D11.HeatKernelBridge.AxiomAudit
import Poincare.D11.HeatKernelBridge.Basic
import Poincare.D11.HeatKernelBridge.EuclideanInstance
import Poincare.D11.HeatKernelBridge.EuclideanLaplacian
import Poincare.D11.HeatKernelBridge.InitialCondition
import Poincare.D11.HeatKernelBridge.ZeroDimension
import Poincare.D11.MaximumPrincipleTensor.AxiomAudit
import Poincare.D11.MaximumPrincipleTensor.Basic
import Poincare.D11.MaximumPrincipleTensor.Euler
import Poincare.D11.MaximumPrincipleTensor.Flow
import Poincare.D11.MaximumPrincipleTensor.ScalarODE
import Poincare.D11.ReducedVolume.All
import Poincare.D11.ReducedVolume.Audit
import Poincare.D11.ReducedVolume.Basic
import Poincare.D11.ReducedVolume.Probe
import Poincare.D11.ReducedVolume.Statements
import Poincare.D11.ReducedVolume.StraightRays
import Poincare.D11.ReducedVolume.Volume
import Poincare.D11.SpectralTorus.AxiomsCheck
import Poincare.D11.SpectralTorus.Basic
import Poincare.D11.SpectralTorus.Laplacian
import Poincare.D11.SpectralTorus.Parseval
import Poincare.D11.SpectralTorus.Poincare
import Poincare.D11.SpectralTorus.Sobolev
import Poincare.D12.ComparisonGeodesics.AxiomAudit
import Poincare.D12.ComparisonGeodesics.Definitions
import Poincare.D12.ComparisonGeodesics.ModelEuclidean
import Poincare.D12.ComparisonGeodesics.RiccatiComparison
import Poincare.D12.ComparisonGeodesics.SingularRiccati
import Poincare.D12.ComparisonGeodesics.SturmComparison
import Poincare.D12.ComparisonGeodesics.VolumeRatio
import Poincare.D12.ConnectionCurvature
import Poincare.D12.ConnectionCurvature.ChartLeviCivita
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaForm
import Poincare.D12.ConnectionCurvature.ChartLeviCivitaSmooth
import Poincare.D12.ConnectionCurvature.ChartModel1D
import Poincare.D12.ConnectionCurvature.ConformalChartModel
import Poincare.D12.ConnectionCurvature.MilnorLeviCivita
import Poincare.D12.ConnectionCurvature.RicciSymmetry
import Poincare.D12.ConnectionCurvature.SoThreeModel
import Poincare.D12.EntropyVariation.All
import Poincare.D12.EntropyVariation.AxiomAudit
import Poincare.D12.EntropyVariation.EntropyDerivative
import Poincare.D12.EntropyVariation.FFlowModel
import Poincare.D12.EntropyVariation.GaussianShrinker
import Poincare.D12.EntropyVariation.SignDistinction
import Poincare.D12.EntropyVariation.WeightedIntegral
import Poincare.D12.GeometricCompactness.AxiomAudit
import Poincare.D12.GeometricCompactness.Basic
import Poincare.D12.GeometricCompactness.Criterion
import Poincare.D12.GeometricCompactness.Frontier
import Poincare.D12.GeometricCompactness.GridFamily
import Poincare.D12.HeatDomain.All
import Poincare.D12.HeatDomain.AxiomAudit
import Poincare.D12.HeatDomain.CompactCompatibility
import Poincare.D12.HeatDomain.Counterexample
import Poincare.D12.HeatDomain.FlatInstance
import Poincare.D12.HeatDomain.TestFunction
import Poincare.D12.HeatSemigroup.All
import Poincare.D12.HeatSemigroup.AxiomAudit
import Poincare.D12.HeatSemigroup.Basic
import Poincare.D12.HeatSemigroup.Example
import Poincare.D12.HeatSemigroup.L1Contraction
import Poincare.D12.HeatSemigroup.LinfContraction
import Poincare.D12.HeatSemigroup.ManifoldObligations
import Poincare.D12.HeatSemigroup.Semigroup
import Poincare.D12.HeatSemigroup.Smoothing
import Poincare.D12.HeatSemigroup.StrongContinuity
import Poincare.D12.HeatSemigroup.StrongContinuityL1
import Poincare.D12.KappaVariational.All
import Poincare.D12.KappaVariational.Audit
import Poincare.D12.KappaVariational.CurvatureEnergy
import Poincare.D12.KappaVariational.GaussianNormalization
import Poincare.D12.KappaVariational.Statements
import Poincare.D12.KappaVariational.Transfer
import Poincare.D12.ParabolicLocal.AxiomAudit
import Poincare.D12.ParabolicLocal.BUC
import Poincare.D12.ParabolicLocal.DerivativeLoss
import Poincare.D12.ParabolicLocal.Duhamel
import Poincare.D12.ParabolicLocal.Examples
import Poincare.D12.ParabolicLocal.GaussianConv
import Poincare.D12.ParabolicLocal.GaussianSemigroup
import Poincare.D12.ParabolicLocal.GaussianSetup
import Poincare.D12.ParabolicLocal.MildExistence
import Poincare.D12.ParabolicLocal.Obligations
import Poincare.D12.ParabolicLocal.ParametricIntegral
import Poincare.D12.SemanticLedger.AxiomAudit
import Poincare.D12.SemanticLedger.Defect
import Poincare.D12.SemanticLedger.LedgerProbe
import Poincare.D12.SpectralSobolev.All
import Poincare.D12.SpectralSobolev.AxiomAudit
import Poincare.D12.SpectralSobolev.Basic
import Poincare.D12.SpectralSobolev.Examples
import Poincare.D12.SpectralSobolev.HeatConvergence
import Poincare.D12.SpectralSobolev.Poincare
import Poincare.D12.SpectralSobolev.Semigroup
import Poincare.D12.SurgeryRecognition.All
import Poincare.D12.SurgeryRecognition.Audit
import Poincare.D12.SurgeryRecognition.BallGluing
import Poincare.D12.SurgeryRecognition.ConnectedSumTopology
import Poincare.D12.SurgeryRecognition.CoveringRecognition
import Poincare.D12.SurgeryRecognition.DeckTrivial
import Poincare.D12.SurgeryRecognition.ExpandedInterfaces
import Poincare.D12.SurgeryRecognition.SphereOfSpheres
import Poincare.D12.TensorMaximumBochner.Audit
import Poincare.D12.TensorMaximumBochner.BochnerIdentity
import Poincare.D12.TensorMaximumBochner.PositivityPreservation
import Poincare.D12.TensorMaximumBochner.So3Model
import Poincare.D12.TensorMaximumBochner.So3Polynomial
import Poincare.D12.TensorMaximumBochner.So3RicciFlow
import Poincare.D12.TensorMaximumBochner.TangentCone
import Poincare.D12.TensorMaximumBochner.TensorCalculus
import Poincare.D12.TriangulationTopology.AntipodalQuotient
import Poincare.D12.TriangulationTopology.AxiomAudit
import Poincare.D12.TriangulationTopology.CoveringLemma
import Poincare.D12.TriangulationTopology.DiskGluing
import Poincare.D12.TriangulationTopology.Downstream
import Poincare.D12.TriangulationTopology.HemisphereDisk
import Poincare.D12.TriangulationTopology.MoiseBranch
import Poincare.D12.TriangulationTopology.SimplexBoundary
import Poincare.D12.TriangulationTopology.SimplexCone
import Poincare.D12.TriangulationTopology.SphereGluing
import Poincare.D12.TriangulationTopology.SphereMissedPoint
import Poincare.D12.TriangulationTopology.SphereOfTwoDisks
import Poincare.D12.TriangulationTopology.SpherePolygonal
import Poincare.D12.TriangulationTopology.SphereRecognition
import Poincare.D12.TriangulationTopology.SphereSimplyConnected
import Poincare.D12.TriangulationTopology.SphereSimplyConnectedMain
import Poincare.D12.TriangulationTopology.TwoHemisphereInstance
import Poincare.D12.VolumeIBP
import Poincare.D12.VolumeIBP.Basic
import Poincare.D12.VolumeIBP.Blocked
import Poincare.D12.VolumeIBP.ChangeOfVariables
import Poincare.D12.VolumeIBP.Compat
import Poincare.D12.VolumeIBP.Divergence
import Poincare.D12.VolumeIBP.Example
import Poincare.D12.VolumeIBP.IBP
import Poincare.D12.VolumeIBP.Regularity
import Poincare.D13.IntegratedAudit.AuditCore
import Poincare.D13.IntegratedAudit.DependencyProbe
import Poincare.D13.IntegratedAudit.ExpectedModules
import Poincare.D13.IntegratedAudit.FullAudit
import Poincare.D13.IntegratedAudit.KernelAudit
import Poincare.D13.IntegratedAudit.NonvacuityProbe
import Poincare.D13.IntegratedAudit.SelfAudit
import Poincare.D13.IntegratedAudit.SnapshotRoot
import Poincare.D13.IntegratedAudit.StatementAudit
import Poincare.D13.IntegratedAudit.UsageProbe
import Poincare.D7.Bochner.Audit
import Poincare.D7.Bochner.Basic
import Poincare.D7.Bochner.Blocked
import Poincare.D7.Bochner.Euclidean
import Poincare.D7.Bochner.Example
import Poincare.D7.Bochner.GradientEstimate
import Poincare.D7.Bochner.Probe
import Poincare.D7.Canonical.All
import Poincare.D7.Canonical.Audit
import Poincare.D7.Canonical.Basic
import Poincare.D7.Canonical.Classification
import Poincare.D7.Canonical.Curvature
import Poincare.D7.Canonical.Models
import Poincare.D7.Canonical.Probe
import Poincare.D7.Canonical.Statements
import Poincare.D7.Compactness.All
import Poincare.D7.Compactness.Audit
import Poincare.D7.Compactness.Basic
import Poincare.D7.Compactness.ManifoldStatements
import Poincare.D7.Compactness.Nonvacuity
import Poincare.D7.Compactness.Probe
import Poincare.D7.Compactness.TotalBounded
import Poincare.D7.Compactness.ToyCompactness
import Poincare.D7.ConjugateHeat.All
import Poincare.D7.ConjugateHeat.Audit
import Poincare.D7.ConjugateHeat.Basic
import Poincare.D7.ConjugateHeat.Blocked
import Poincare.D7.ConjugateHeat.Example
import Poincare.D7.ConjugateHeat.Instance
import Poincare.D7.ConjugateHeat.Laplacian
import Poincare.D7.ConjugateHeat.Probe
import Poincare.D7.ConjugateHeat.Slab
import Poincare.D7.Curvature
import Poincare.D7.Curvature.Audit
import Poincare.D7.Curvature.Basic
import Poincare.D7.Curvature.Blocked
import Poincare.D7.Curvature.Bridge
import Poincare.D7.Curvature.Example
import Poincare.D7.Curvature.Probe
import Poincare.D7.Curvature.Sectional
import Poincare.D7.Curvature.Symmetries
import Poincare.D7.Divergence
import Poincare.D7.Divergence.Audit
import Poincare.D7.Divergence.Basic
import Poincare.D7.Divergence.Blocked
import Poincare.D7.Divergence.Example
import Poincare.D7.Divergence.Graph
import Poincare.D7.Divergence.Probe
import Poincare.D7.Divergence.Slab
import Poincare.D7.EvolutionSharp.AxiomAudit
import Poincare.D7.EvolutionSharp.Certificates
import Poincare.D7.EvolutionSharp.FunctionalSharp
import Poincare.D7.EvolutionSharp.GibbsSharp
import Poincare.D7.EvolutionSharp.Implications
import Poincare.D7.EvolutionSharp.ReleaseAudit
import Poincare.D7.EvolutionSharp.Witnesses
import Poincare.D7.Geodesic.AxiomAudit
import Poincare.D7.Geodesic.Basic
import Poincare.D7.Geodesic.FlatUniqueness
import Poincare.D7.Geodesic.ManifoldInterfaces
import Poincare.D7.Geodesic.MathlibProbe
import Poincare.D7.Geodesic.MetricSpeed
import Poincare.D7.Geodesic.Reparam
import Poincare.D7.Geodesic.Smoke
import Poincare.D7.HeatKernel.All
import Poincare.D7.HeatKernel.Audit
import Poincare.D7.HeatKernel.Basic
import Poincare.D7.HeatKernel.Blocked
import Poincare.D7.HeatKernel.Content
import Poincare.D7.HeatKernel.Example
import Poincare.D7.HeatKernel.Grid
import Poincare.D7.HeatKernel.Instance
import Poincare.D7.HeatKernel.Probe
import Poincare.D7.Kappa.Basic
import Poincare.D7.LeviCivita.Audit
import Poincare.D7.LeviCivita.Basic
import Poincare.D7.LeviCivita.Blocked
import Poincare.D7.LeviCivita.Coefficients
import Poincare.D7.LeviCivita.Koszul
import Poincare.D7.LeviCivita.Probe
import Poincare.D7.LeviCivita.Smoke
import Poincare.D7.Limit.All
import Poincare.D7.Limit.Audit
import Poincare.D7.Limit.Basic
import Poincare.D7.Limit.Blocked
import Poincare.D7.Limit.Convergence
import Poincare.D7.Limit.ErrorRecursion
import Poincare.D7.Limit.Example
import Poincare.D7.Limit.Probe
import Poincare.D7.Limit.Refinement
import Poincare.D7.Limit.Stability
import Poincare.D7.Monotonicity.ReducedVolumeInput
import Poincare.D7.Recognition.All
import Poincare.D7.Recognition.Assembly
import Poincare.D7.Recognition.Audit
import Poincare.D7.Recognition.Basic
import Poincare.D7.Recognition.Homeomorphism
import Poincare.D7.Recognition.Probe
import Poincare.D7.Reduced.All
import Poincare.D7.Reduced.Audit
import Poincare.D7.Reduced.Basic
import Poincare.D7.Reduced.Certificate
import Poincare.D7.Reduced.Gaussian
import Poincare.D7.Reduced.Probe
import Poincare.D7.Reduced.Statements
import Poincare.D7.RicciScalar
import Poincare.D7.RicciScalar.Audit
import Poincare.D7.RicciScalar.Basic
import Poincare.D7.RicciScalar.Bridge
import Poincare.D7.RicciScalar.Example
import Poincare.D7.RicciScalar.Probe
import Poincare.D7.RicciScalar.Product
import Poincare.D7.RicciScalar.Scalar
import Poincare.D7.RicciScalar.Variation
import Poincare.D7.ShortTime
import Poincare.D7.ShortTime.Audit
import Poincare.D7.ShortTime.Basic
import Poincare.D7.ShortTime.Equivalence
import Poincare.D7.ShortTime.Example
import Poincare.D7.ShortTime.Gauge
import Poincare.D7.ShortTime.MatrixDeriv
import Poincare.D7.ShortTime.ODE
import Poincare.D7.ShortTime.Probe
import Poincare.D7.ShortTime.Statements
import Poincare.D7.SurgeryFlow.All
import Poincare.D7.SurgeryFlow.Audit
import Poincare.D7.SurgeryFlow.Basic
import Poincare.D7.SurgeryFlow.Extinction
import Poincare.D7.SurgeryFlow.Probe
import Poincare.D7.SurgeryFlow.Statements
import Poincare.D7.SurgeryFlow.Times
import Poincare.D7.TensorLaplacian
import Poincare.D7.TensorLaplacian.Audit
import Poincare.D7.TensorLaplacian.Basic
import Poincare.D7.TensorLaplacian.Blocked
import Poincare.D7.TensorLaplacian.Commutation
import Poincare.D7.TensorLaplacian.Evolution
import Poincare.D7.TensorLaplacian.Example
import Poincare.D7.TensorLaplacian.Probe
import Poincare.D7.Volume
import Poincare.D7.Volume.Audit
import Poincare.D7.Volume.Basic
import Poincare.D7.Volume.Blocked
import Poincare.D7.Volume.ChangeOfVariables
import Poincare.D7.Volume.Example
import Poincare.D7.Volume.Probe
import Poincare.D7.Volume.Scaling
import Poincare.D8.Fidelity.AxiomAudit
import Poincare.D8.Fidelity.Bridge
import Poincare.D8.Fidelity.FidelityCard
import Poincare.D8.Fidelity.MoiseData
import Poincare.D8.Fidelity.MoiseStatement
import Poincare.D8.Fidelity.SmoothStructure
import Poincare.D9.AncientKappa.Basic
import Poincare.D9.AncientKappa.Classification
import Poincare.D9.AncientKappa.GaussianSoliton
import Poincare.D9.AncientKappa.PrintAxioms
import Poincare.D9.CheegerGromov.AxiomAudit
import Poincare.D9.CheegerGromov.CheegerGromov
import Poincare.D9.CheegerGromov.DiscreteModel
import Poincare.D9.CheegerGromov.PointedConvergence
import Poincare.D9.DeTurck.ConnectionLayer
import Poincare.D9.DeTurck.StatementOnly
import Poincare.D9.DeTurck.SymbolModel
import Poincare.D9.ParabolicEstimates.AxiomAudit
import Poincare.D9.ParabolicEstimates.Basic
import Poincare.D9.ParabolicEstimates.Gronwall
import Poincare.D9.ParabolicEstimates.MatrixModel
import Poincare.D9.ParabolicEstimates.Statements
import Poincare.D9.Surfaces.All
import Poincare.D9.Surfaces.AxiomAudit
import Poincare.D9.Surfaces.Basic
import Poincare.D9.Surfaces.HomogeneousODE
import Poincare.D9.Surfaces.Statements
import Poincare.D9.TensorAlgebra.AxiomAudit
import Poincare.D9.TensorAlgebra.Interface
import Poincare.D9.TensorAlgebra.Props
import Poincare.D9.TensorAlgebra.Toy
import Poincare.VKPort.HatcherLib.Ch1.AlgebraicConstructions
import Poincare.VKPort.HatcherLib.Ch1.BasicConstructions
import Poincare.VKPort.HatcherLib.Ch1.VanKampen
import Poincare.VKPort.HatcherLib.Ch1.VanKampenAdaptedGrid
import Poincare.VKPort.HatcherLib.Ch1.VanKampenGlobalSweep
import Poincare.VKPort.HatcherLib.Ch1.VanKampenGrid
import Poincare.VKPort.HatcherLib.Ch1.VanKampenSubdivision
import Poincare.VKPort.HatcherLib.Ch1.VanKampenSweep
import Poincare.VKPort.HatcherLib.Ch1.VanKampenWordCalculus
import Poincare.VKPort.HatcherLib.VKProbe
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace SEMREVUse_D13_integrated_kernel_audit

def existsNames : List Name := [
  "Poincare.D7.ConjugateHeat.ConjugateHeatData".toName,
  "Poincare.D12.HeatSemigroup.heatOperatorBCF_comp".toName,
  "Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1_tendsto_seq".toName,
  "Poincare.D12.ConnectionCurvature.leviCivitaExists".toName,
  "Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent".toName,
  "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap".toName,
  "Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2".toName]

def pairs : List (Name × Name) := [
  ("Poincare.D12.HeatSemigroup.heatOperatorBCF_comp".toName, "Poincare.D12.HeatSemigroup.heatOperator_gaussianKernel_L1_tendsto_seq".toName),
  ("Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2".toName, "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses".toName)]

def reverseNames : List Name := [
  "Poincare.D12.ConnectionCurvature.leviCivitaExists".toName,
  "Poincare.D12.EntropyVariation.fDerivativeStatement_of_corrected_of_idempotent".toName,
  "Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap".toName,
  "Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses".toName]

def scanPrefixes : List Name := [
  "Poincare".toName]

end SEMREVUse_D13_integrated_kernel_audit

open SEMREVUse_D13_integrated_kernel_audit in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  for n in existsNames do
    match env.find? n with
    | none => IO.println s!"USE_EXISTS\t{n}\tMISSING"
    | some ci =>
        let axs ← try Lean.collectAxioms n catch _ => pure #[]
        IO.println s!"USE_EXISTS\t{n}\tOK\t{";".intercalate (axs.toList.map Name.toString)}"
  for (ctor, down) in pairs do
    let ci? := env.find? down
    let inType := match ci? with
      | some ci => ci.type.getUsedConstants.contains ctor
      | none => false
    let inValue := match ci? with
      | some ci => (match ci.value? true with
          | some v => v.getUsedConstants.contains ctor
          | none => false)
      | none => false
    IO.println s!"USE_PAIR\t{ctor}\t{down}\texists={(env.find? down).isSome}\ttype={inType}\tvalue={inValue}"
  for ctor in reverseNames do
    let mut direct : Array Name := #[]
    for (d, _) in env.constants.toList do
      if d == ctor then continue
      let inScan : Bool :=
        match env.getModuleIdxFor? d with
        | some i => scanPrefixes.any (fun r => r.isPrefixOf (mods.getD i .anonymous))
        | none => false
      if !inScan then continue
      match env.find? d with
      | some ci =>
          let inT := ci.type.getUsedConstants.contains ctor
          let inV := match ci.value? true with
            | some v => v.getUsedConstants.contains ctor
            | none => false
          if inT || inV then direct := direct.push d
      | none => pure ()
    IO.println s!"USE_REVERSE\t{ctor}\t{direct.size}"
    for d in direct.qsort (fun a b => a.toString < b.toString) do
      IO.println s!"USE_USER\t{ctor}\t{d}"
  IO.println s!"USE_DONE\tD13-integrated-kernel-audit"
