/- INDEPENDENT spot-check driver (verifier lane) -/
import Audit.CounterexampleAudit
import Audit.CurvatureODEAudit
import Audit.EvolutionAudit
import Audit.GeometryAudit
import Audit.PromotedEvolutionAudit
import D6AuditReport
import Ledger.DefinitionSmoke
import Ledger.PerelmanDefinitions
import Poincare.Basic
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
import Poincare.D12.TriangulationTopology.NegControl.NegControl
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
import Poincare.D12.VolumeIBP.Audit
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
import Poincare.Longrun.CurvatureODE
import Poincare.Longrun.CurvatureODE.Bridge
import Poincare.Longrun.CurvatureODE.Evolution
import Poincare.Longrun.CurvatureODE.Invariant
import Poincare.Longrun.CurvatureODE.Monotonicity
import Poincare.Longrun.CurvatureODE.ScalarODE
import Poincare.Longrun.CurvatureODE.State
import Poincare.Longrun.Entropy
import Poincare.Longrun.Entropy.AxiomAudit
import Poincare.Longrun.Entropy.Bridge
import Poincare.Longrun.Entropy.Certificate
import Poincare.Longrun.Entropy.DiscreteHeat
import Poincare.Longrun.Entropy.FiniteGeometry
import Poincare.Longrun.Entropy.Functional
import Poincare.Longrun.Evolution
import Poincare.Longrun.Evolution.Bridge
import Poincare.Longrun.Evolution.Continuous
import Poincare.Longrun.Evolution.Counterexample
import Poincare.Longrun.Evolution.Discrete
import Poincare.Longrun.Evolution.Functional
import Poincare.Longrun.Evolution.Gibbs
import Poincare.Longrun.Geometry
import Poincare.Longrun.Geometry.ConnectionAdapter
import Poincare.Longrun.Geometry.Contraction
import Poincare.Longrun.Geometry.LeviCivitaBlocked
import Poincare.Longrun.Geometry.MetricData
import Poincare.Longrun.PDE.AxiomAudit
import Poincare.Longrun.PDE.ContinuousInterface
import Poincare.Longrun.PDE.DiscreteMaximumPrinciple
import Poincare.Longrun.PDE.Energy
import Poincare.Longrun.PDE.HeatGrid
import Poincare.Longrun.Surgery
import Poincare.Longrun.Surgery.Axioms
import Poincare.Longrun.Surgery.Basic
import Poincare.Longrun.Surgery.Chain
import Poincare.Longrun.Surgery.Missing
import Poincare.Longrun.Surgery.Toy
import Poincare.Longrun.Topology.AxiomAudit
import Poincare.Longrun.Topology.Basic
import Poincare.Longrun.Topology.CompactThreeManifold
import Poincare.Longrun.Topology.MissingTheorems
import Poincare.Longrun.Topology.Noncollapsing
import Poincare.Longrun.Topology.NormalizedVolume
import Poincare.Longrun.Topology.Stage6Bridge
import Poincare.Stage1.CurvatureAlgebra
import Poincare.Stage1.RiemannAdapter
import Poincare.Stage6.SphereSimplyConnected
import Poincare.Stage6.TopologyBridge
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
import Probe.GeometryApi
import Probe.PdeApi
import ReleaseAudit
import ReleaseCheck

#print axioms D4Audit.NoSignEvolution
#print axioms D4Audit.noSignEvolution_neg
#print axioms D6AuditReport.kindOf.match_1
#print axioms HatcherLib.CoveredPathChain.brecOn.go
#print axioms HatcherLib.CoveredPathChain.prefix_loops_mem_carrierSets._simp_1_5
#print axioms HatcherLib.Path.Homotopic
#print axioms HatcherLib.VanKampenRectangularSubdivision.horizontalCut
#print axioms HatcherLib.VanKampenSquareGrid.cellConvexHomotopy._proof_1
#print axioms HatcherLib.VanKampenSquareGrid.horizontalEdgeClassInCell.eq_1
#print axioms HatcherLib.VanKampenSquareGrid.noConfusionType
#print axioms HatcherLib.VanKampenSquareGrid.verticalCut_zero
#print axioms HatcherLib.VanKampenSweepCell.ctorIdx
#print axioms HatcherLib.VanKampenSweepCell.right
#print axioms HatcherLib.VanKampenSweepRow.rightBoundary._f
#print axioms HatcherLib.VanKampenSweepStage.noConfusion
#print axioms HatcherLib.coverIntersectionInclusionRight
#print axioms HatcherLib.exists_vanKampenSquareGrid._proof_1_2
#print axioms HatcherLib.pathInSubtypeBetween._proof_1
#print axioms HatcherLib.vanKampenMap_factorRepresentative
#print axioms HatcherLib.vanKampenWordLoop_homotopic_of_equivalent
#print axioms Perelman.MetricFlowData._sizeOf_inst
#print axioms Perelman.RicciTensor._proof_3
#print axioms Perelman.VolumeFormData.noConfusion
#print axioms Perelman.riemannianVolumeDensity_pos_of_posDef
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.endoRicci.eq_1
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.recOn
#print axioms Poincare.D10.BochnerEuclidean.D.eq_1
#print axioms Poincare.D10.BochnerEuclidean.hessNormSq.eq_1
#print axioms Poincare.D10.HeatKernelEuclidean.innerCLM._proof_6
#print axioms Poincare.D10.MaximumPrincipleRN.HeatSubsolutionData.of_twoSided
#print axioms Poincare.D10.MaximumPrincipleRN.weak_maximum_principle
#print axioms Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex.mk._flat_ctor
#print axioms Poincare.D10.TriangulationLowDim.circleS1_vertices_card
#print axioms Poincare.D10.TriangulationLowDim.torus7_isClosedSurface
#print axioms Poincare.D10.hasDerivAt_jacobiSol
#print axioms Poincare.D10.jacobiSolSphere_pos
#print axioms Poincare.D11.BochnerManifold.flatCertificateWitness._proof_3
#print axioms Poincare.D11.BochnerManifold.lapG.eq_1
#print axioms Poincare.D11.BochnerManifold.radial_bochner_identity
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.mk.sizeOf_spec
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore_c_lo
#print axioms Poincare.D11.HeatKernelBridge.mem_contDiffTwoSubmodule._simp_1
#print axioms Poincare.D11.MaximumPrincipleTensor.exp_shift_forward_invariance
#print axioms Poincare.D11.MaximumPrincipleTensor.quadForm_smul
#print axioms Poincare.D11.ReducedVolume.euclideanFlow_metric
#print axioms Poincare.D11.ReducedVolume.flatReducedLength._proof_1
#print axioms Poincare.D11.ReducedVolume.straightRay_length
#print axioms Poincare.D11.SpectralTorus.innerForm._proof_1
#print axioms Poincare.D11.SpectralTorus.one_add_normSq_inv_le_prod._simp_1_6
#print axioms Poincare.D11.SpectralTorus.summable_sobolevWeight_inv._simp_1_4
#print axioms Poincare.D11.SpectralTorus.trigPolyDerivL2._proof_4
#print axioms Poincare.D11.ballVolume.eq_1
#print axioms Poincare.D11.polarMetric._proof_1
#print axioms Poincare.D12.ComparisonGeodesics.RiccatiEqOn.hasDerivAt_m
#print axioms Poincare.D12.ComparisonGeodesics.euclidModelA_zero
#print axioms Poincare.D12.ComparisonGeodesics.logDeriv_le_of_le._simp_1_7
#print axioms Poincare.D12.ConnectionCurvature.ChartMetricCoefficients
#print axioms Poincare.D12.ConnectionCurvature.ChartModel1D.chart1D._proof_1
#print axioms Poincare.D12.ConnectionCurvature.SmoothChartData.gInv_smooth
#print axioms Poincare.D12.ConnectionCurvature.SoThreeModel.dot3._proof_9
#print axioms Poincare.D12.ConnectionCurvature.chartCurvatureOperator_apply
#print axioms Poincare.D12.ConnectionCurvature.curvatureEndo._proof_4
#print axioms Poincare.D12.ConnectionCurvature.nablaOf._proof_1
#print axioms Poincare.D12.EntropyVariation.fflowGradSq._proof_1
#print axioms Poincare.D12.EntropyVariation.fflow_F_value
#print axioms Poincare.D12.EntropyVariation.hasDerivAt_F_of_pointwise
#print axioms Poincare.D12.EntropyVariation.normSq_exp_neg_mul_le._simp_1_2
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_W_value
#print axioms Poincare.D12.GeometricCompactness.cover_transfer_of_ghDist
#print axioms Poincare.D12.GeometricCompactness.isCompact_unitSquare
#print axioms Poincare.D12.HeatDomain.AdmissibleTestClass.mk._flat_ctor
#print axioms Poincare.D12.HeatDomain.notIntegrable_fast_times_kernel._simp_1_2
#print axioms Poincare.D12.HeatSemigroup.gaussianKernelFDerivCLM._proof_1
#print axioms Poincare.D12.HeatSemigroup.heatOperator_comp_heatOperator
#print axioms Poincare.D12.HeatSemigroup.lintegral_enorm_heatKernelProduct_le
#print axioms Poincare.D12.KappaVariational.constantCurvatureFlow._proof_5
#print axioms Poincare.D12.KappaVariational.gaussianReducedVolumeDensity_ne_zero
#print axioms Poincare.D12.KappaVariational.ncf12ModelClosure.eq_1
#print axioms Poincare.D12.ParabolicLocal.BUCf.instAddCommGroupBUCn._proof_6
#print axioms Poincare.D12.ParabolicLocal.BUCf.rec
#print axioms Poincare.D12.ParabolicLocal.DuhamelSetup.duhamelMap_pointwise_lipschitz
#print axioms Poincare.D12.ParabolicLocal.arctanF_not_additive
#print axioms Poincare.D12.ParabolicLocal.gaussianS._proof_1
#print axioms Poincare.D12.ParabolicLocal.heatConv_nonneg
#print axioms Poincare.D12.ParabolicLocal.kernelIntegrandFderiv._proof_6
#print axioms Poincare.D12.ParabolicLocal.sq_mul_exp_neg_mul_sq_le
#print axioms Poincare.D12.SemanticLedger.tendsto_testFunction_atTop
#print axioms Poincare.D12.SpectralSobolev.heatWeight_zero
#print axioms Poincare.D12.SurgeryRecognition.ConnectedSumDecompositionV2.mk._flat_ctor
#print axioms Poincare.D12.SurgeryRecognition.RemainingRecognitionHypotheses.noConfusion
#print axioms Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3.spaceForm
#print axioms Poincare.D12.SurgeryRecognition.SphericalSum._sizeOf_1
#print axioms Poincare.D12.SurgeryRecognition.ballOrigin
#print axioms Poincare.D12.SurgeryRecognition.equatorHomeoS2._proof_4
#print axioms Poincare.D12.SurgeryRecognition.iteratedSphereSum._proof_6
#print axioms Poincare.D12.SurgeryRecognition.quotientHomeoOfSubsingleton
#print axioms Poincare.D12.SurgeryRecognition.sphere2ToBall_continuous
#print axioms Poincare.D12.SurgeryRecognition.up
#print axioms Poincare.D12.TensorMaximumBochner.Bochner.D_one
#print axioms Poincare.D12.TensorMaximumBochner.Bochner.cG_antisym._abel_1_1
#print axioms Poincare.D12.TensorMaximumBochner.Bochner.lap
#print axioms Poincare.D12.TensorMaximumBochner.Bochner.weitzenboeck_half._abel_1_1
#print axioms Poincare.D12.TensorMaximumBochner.So3Polynomial.D_rotVec
#print axioms Poincare.D12.TensorMaximumBochner.So3Polynomial.polyVec
#print axioms Poincare.D12.TensorMaximumBochner.So3RicciFlow.metricMatrix_at_one
#print axioms Poincare.D12.TensorMaximumBochner.hasDerivAt_lambdaInv._simp_1_3
#print axioms Poincare.D12.TriangulationTopology.SuspCyl
#print axioms Poincare.D12.TriangulationTopology.coneMap_mem
#print axioms Poincare.D12.TriangulationTopology.coveringMap_injective_of_simplyConnected
#print axioms Poincare.D12.TriangulationTopology.dist_restrictionPiece_left
#print axioms Poincare.D12.TriangulationTopology.hemisphere_cover._simp_1_1
#print axioms Poincare.D12.TriangulationTopology.norm_radialExtend
#print axioms Poincare.D12.TriangulationTopology.restrictionChain_apply_eq_clampedMap_idChain
#print axioms Poincare.D12.TriangulationTopology.segPiece
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryNonempty
#print axioms Poincare.D12.TriangulationTopology.simplexConeMapQuot_surjective
#print axioms Poincare.D12.TriangulationTopology.simplexRadialTime_pos_of_ne_center
#print axioms Poincare.D12.TriangulationTopology.sphereThreeGluedDisks
#print axioms Poincare.D12.TriangulationTopology.suspMapQuot
#print axioms Poincare.D12.TriangulationTopology.zmod2Mul_eq_ofAdd_one_or_one
#print axioms Poincare.D12.VolumeIBP.ChartMetric.densityNNReal_eq
#print axioms Poincare.D12.VolumeIBP.ChartMetric.gradInnerInverse
#print axioms Poincare.D12.VolumeIBP.ChartMetric.mk._flat_ctor
#print axioms Poincare.D12.VolumeIBP.manifoldOrientationVolumeFormCompat
#print axioms Poincare.D13.IntegratedAudit.reaches._unsafe_rec
#print axioms Poincare.D7.Bochner.RawGradientModel._sizeOf_1
#print axioms Poincare.D7.Bochner.SmoothBochnerDatum.mk.injEq
#print axioms Poincare.D7.Bochner.diff_sub
#print axioms Poincare.D7.Bochner.negativeControl._proof_5
#print axioms Poincare.D7.Canonical.CanonicalKind.cap.sizeOf_spec
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.scale_pos
#print axioms Poincare.D7.Canonical.CapInterface.mk.inj
#print axioms Poincare.D7.Canonical.CylinderInterface
#print axioms Poincare.D7.Canonical.EpsilonApproximation.distortion
#print axioms Poincare.D7.Canonical.EpsilonCap.mk.sizeOf_spec
#print axioms Poincare.D7.Canonical.EpsilonSpherical.mk.noConfusion
#print axioms Poincare.D7.Canonical.SphereInterface.mk.sizeOf_spec
#print axioms Poincare.D7.Canonical.instInhabitedCanonicalKind.default
#print axioms Poincare.D7.Canonical.piIntervalSphereInterface._proof_6
#print axioms Poincare.D7.Compactness.CheegerGromovConvergenceData._sizeOf_inst
#print axioms Poincare.D7.Compactness.GHConvergenceData.comp
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.uniform_finite_net
#print axioms Poincare.D7.Compactness.PointedMetricSpace.rec
#print axioms Poincare.D7.Compactness.missingPointedGHConvergentSubsequence_iff
#print axioms Poincare.D7.ConjugateHeat.Blocker.mk.inj
#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatSpacetime.conjugateHeat.eq_1
#print axioms Poincare.D7.ConjugateHeat.boundaryForm_antisymm
#print axioms Poincare.D7.ConjugateHeat.cycleSlab
#print axioms Poincare.D7.ConjugateHeat.edgeLapAt
#print axioms Poincare.D7.ConjugateHeat.pairingLM_apply
#print axioms Poincare.D7.Curvature.CovariantDerivativeOfCurvature.rec
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvatureForm_add₂
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.meanData
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.sectionalCurvature_gl2
#print axioms Poincare.D7.Curvature.So3.so3_isNondegenerate2Plane_e0_e1
#print axioms Poincare.D7.Divergence.DivergenceData.boundaryIn.eq_1
#print axioms Poincare.D7.Divergence.DivergenceData.src
#print axioms Poincare.D7.Divergence.ManifoldDivergenceDatum
#print axioms Poincare.D7.Divergence.edgeData_divergence_zero
#print axioms Poincare.D7.Divergence.triangleData
#print axioms Poincare.D7.EvolutionSharp.gibbsTerm_step_lt_old_recovered
#print axioms Poincare.D7.EvolutionSharp.sharpWitnessTraj.eq_2
#print axioms Poincare.D7.Geodesic.GeodesicContext.mk
#print axioms Poincare.D7.Geodesic.GeodesicData.reparam_v
#print axioms Poincare.D7.Geodesic.flatGeodesicData._proof_6
#print axioms Poincare.D7.HeatKernel.FiniteGridHeatKernel.K
#print axioms Poincare.D7.HeatKernel.GridHeatSolution.recOn
#print axioms Poincare.D7.HeatKernel.HeatKernelData.normalization_symm
#print axioms Poincare.D7.HeatKernel.IsClosedRiemannianManifold.casesOn
#print axioms Poincare.D7.HeatKernel.gridKernel._proof_2
#print axioms Poincare.D7.HeatKernel.punitHeatKernelData._proof_12
#print axioms Poincare.D7.HeatKernel.u0.eq_1
#print axioms Poincare.D7.Kappa.KappaCertificate.casesOn
#print axioms Poincare.D7.Kappa.KappaComparisonData.mk.inj
#print axioms Poincare.D7.LeviCivita.BlockerCovariantDerivativeCurvature_ne_nil
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.affineCombination
#print axioms Poincare.D7.LeviCivita.affineConnection_self._simp_1_1
#print axioms Poincare.D7.LeviCivita.differenceTensor_add_right
#print axioms Poincare.D7.Limit.Blocker
#print axioms Poincare.D7.Limit.ConsistencyCertificate.error_step
#print axioms Poincare.D7.Limit.GridMesh.casesOn
#print axioms Poincare.D7.Limit.HeatMeshSequence.grid
#print axioms Poincare.D7.Limit.SlabGrid._sizeOf_inst
#print axioms Poincare.D7.Limit.TimeMesh.time
#print axioms Poincare.D7.Limit.quadCertificate._proof_3
#print axioms Poincare.D7.Recognition.CanonicalNeighborhoodInput
#print axioms Poincare.D7.Recognition.ConnectedSumDecomposition.mk.noConfusion
#print axioms Poincare.D7.Recognition.ExtinctionConclusion.casesOn
#print axioms Poincare.D7.Recognition.RecognitionHypotheses
#print axioms Poincare.D7.Recognition.SphericalPiece.homeomorphic
#print axioms Poincare.D7.Recognition.finalHomeomorphismBlockers_ne_nil
#print axioms Poincare.D7.Reduced.FiniteReducedVolumeCertificate.derivative_nonpos
#print axioms Poincare.D7.Reduced.JacobianComparisonInterface.recOn
#print axioms Poincare.D7.Reduced.MetricFlowInterface.Llength_eq_LlengthAlong
#print axioms Poincare.D7.Reduced.ReducedLengthData.mk.noConfusion
#print axioms Poincare.D7.Reduced.ReducedLengthDensityCertificate.noConfusion
#print axioms Poincare.D7.Reduced.ReducedVolumeCertificate.volume_le_one
#print axioms Poincare.D7.Reduced.gaussianReducedLengthData.eq_1
#print axioms Poincare.D7.Reduced.integral_one_div_sqrt._simp_1_2
#print axioms Poincare.D7.RicciScalar.FlowPath.LeviCivitaEvolution.hasDeriv
#print axioms Poincare.D7.RicciScalar.FlowPath.mk._flat_ctor
#print axioms Poincare.D7.RicciScalar.prodConn._proof_5
#print axioms Poincare.D7.RicciScalar.ricciTensor_symm
#print axioms Poincare.D7.RicciScalar.so3_ricciTrace_permBasis_e0_e0
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.mk.injEq
#print axioms Poincare.D7.ShortTime.DeTurckParabolicProblem.mk.sizeOf_spec
#print axioms Poincare.D7.ShortTime.MissingDependency.mk.noConfusion
#print axioms Poincare.D7.ShortTime.RicciLipschitzInterface.ctorIdx
#print axioms Poincare.D7.ShortTime.gaugeAction_inv
#print axioms Poincare.D7.ShortTime.nilpotentDeTurckCertificate._proof_4
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface._sizeOf_1
#print axioms Poincare.D7.SurgeryFlow.ExtinctionData.mk.injEq
#print axioms Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.target_of_realizes
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData._sizeOf_1
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.toSurgeryCertificate
#print axioms Poincare.D7.SurgeryFlow.extinct_of_missingExtinctionTheorem
#print axioms Poincare.D7.SurgeryFlow.surgeryFlowDependencies_all_named
#print axioms Poincare.D7.TensorLaplacian.IsSmoothTensorLaplacianDatum
#print axioms Poincare.D7.TensorLaplacian.ScalarEvolutionCertificate.velocity
#print axioms Poincare.D7.TensorLaplacian.SmoothTensorLaplacianDatum.isSmoothTensorField
#print axioms Poincare.D7.TensorLaplacian.TensorConnectionData.RicciCommutationCertificate._sizeOf_inst
#print axioms Poincare.D7.TensorLaplacian.TensorConnectionData.commutator_term._abel_1_5
#print axioms Poincare.D7.TensorLaplacian.TensorConnectionData.rec
#print axioms Poincare.D7.TensorLaplacian.WrongBianchiData.mk.sizeOf_spec
#print axioms Poincare.D7.TensorLaplacian.prodTensorData._proof_25
#print axioms Poincare.D7.TensorLaplacian.wrongBianchiExample._proof_3
#print axioms Poincare.D7.Volume.TopFormBundle.normedAddCommGroupF
#print axioms Poincare.D7.Volume.VolumeFormData.scaledBasis_orthonormal._simp_1_4
#print axioms Poincare.D7.Volume.sqrtInvUnit
#print axioms Poincare.D8.Fidelity.MoiseData.mk
#print axioms Poincare.D8.Fidelity.SmoothStructure._sizeOf_1
#print axioms Poincare.D8.Fidelity.moiseExistence_of_moiseTheorem
#print axioms Poincare.D9.CheegerGromov.CkCloseAtScale.mono_scale._proof_1
#print axioms Poincare.D9.CheegerGromov.CompactExhaustion._sizeOf_1
#print axioms Poincare.D9.CheegerGromov.DiscreteMetricDatum.exists_convergent_subsequence
#print axioms Poincare.D9.CheegerGromov.PointedManifold.metricBall
#print axioms Poincare.D9.CheegerGromov.ckCloseAtScale_self._proof_2
#print axioms Poincare.D9.ParabolicEstimates.ClassicalSolution.mk.sizeOf_spec
#print axioms Poincare.D9.ParabolicEstimates.EnergyFunctional.integrable_energy
#print axioms Poincare.D9.ParabolicEstimates.ParabolicData.f
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.matrixDirichletForm
#print axioms Poincare.D9.ParabolicEstimates.SobolevScale.mk.sizeOf_spec
#print axioms Poincare.D9.ParabolicEstimates.forcingEnergy
#print axioms Poincare.D9.ParabolicEstimates.zeroDirichletForm._proof_1
#print axioms Poincare.D9.Surfaces.IsLogisticSolution
#print axioms Poincare.D9.Surfaces.averageScalar
#print axioms Poincare.D9.Surfaces.tendsto_homogeneousSolution_zero
#print axioms Poincare.D9.TensorAlgebra.TensorBundleData.mk.sizeOf_spec
#print axioms Poincare.D9.TensorAlgebra.Toy.metric._proof_3
#print axioms Poincare.D9.TensorAlgebra.flat_smooth
#print axioms Poincare.GaussianToolbox.integral_moment_succ
#print axioms Poincare.Longrun.AncientKappa.AncientSolution.time_le_zero
#print axioms Poincare.Longrun.AncientKappa.GradientShrinkingSoliton.mk.sizeOf_spec
#print axioms Poincare.Longrun.AncientKappa.ManifoldGradientShrinkingSoliton.rec
#print axioms Poincare.Longrun.AncientKappa.ThreeDimKappaSolution.noConfusion
#print axioms Poincare.Longrun.AncientKappa.hessianCLM._proof_1
#print axioms Poincare.Longrun.CurvatureODE.ReactionField._sizeOf_inst
#print axioms Poincare.Longrun.CurvatureODE.TensorRicciFlowODEBridge.mk.inj
#print axioms Poincare.Longrun.CurvatureODE.scalarOfState_monotone
#print axioms Poincare.Longrun.DeTurck.ConnectionLayer.gtildeinv_symm
#print axioms Poincare.Longrun.DeTurck.FlowInterface.noConfusion
#print axioms Poincare.Longrun.DeTurck.bilinTrace
#print axioms Poincare.Longrun.DeTurck.ricciSymbol.eq_1
#print axioms Poincare.Longrun.Entropy.ContinuousAntitoneCertificate._sizeOf_inst
#print axioms Poincare.Longrun.Entropy.ContinuousMonotoneCertificate.mk.noConfusion
#print axioms Poincare.Longrun.Entropy.EntropyData.mk.inj
#print axioms Poincare.Longrun.Entropy.LinearDecayCertificate.mk.injEq
#print axioms Poincare.Longrun.Entropy.WeightedCalculus.metric
#print axioms Poincare.Longrun.Entropy.finiteCurvatureDatum_W
#print axioms Poincare.Longrun.Evolution.PerelmanApproximation.mk.noConfusion
#print axioms Poincare.Longrun.Evolution.finiteReactionEntropyData_F_antitone
#print axioms Poincare.Longrun.Evolution.perelmanF_one_two_le
#print axioms Poincare.Longrun.Geometry.AbstractConnection.curvatureEndo._proof_1
#print axioms Poincare.Longrun.Geometry.LeviCivitaData
#print axioms Poincare.Longrun.Geometry.LieBracketData.mk.sizeOf_spec
#print axioms Poincare.Longrun.Geometry.MetricData.raiseIndex._proof_2
#print axioms Poincare.Longrun.Geometry.meanConnection_lie
#print axioms Poincare.Longrun.PDE.HeatGridEvolution.rec
#print axioms Poincare.Longrun.PDE.sum_shift_pred
#print axioms Poincare.Longrun.Surgery.ExtinctionTheorem.ctorIdx
#print axioms Poincare.Longrun.Surgery.MissingInputs._sizeOf_inst
#print axioms Poincare.Longrun.Surgery.NeckAnalysis.recOn
#print axioms Poincare.Longrun.Surgery.SurgeryChain.ctorElimType
#print axioms Poincare.Longrun.Surgery.SurgeryDatum.trivial
#print axioms Poincare.Longrun.Surgery.canonicalLedger
#print axioms Poincare.Longrun.Topology.CompactThreeManifold.noConfusion
#print axioms Poincare.Longrun.Topology.NormalizedBallVolumeLowerBound.r0_pos
#print axioms Poincare.Longrun.Topology.missingReducedVolumeMonotonicity
#print axioms Poincare.RiemannAdapter.RiemannianCurvatureData.curvatureForm_first_pair_skew
#print axioms Poincare.Stage6.simplyConnectedSpace_of_homeomorph
#print axioms Probe.CurvatureTensor.noConfusionType
#print axioms Probe.CurvatureTensor.toCurvatureOperator._proof_4
#print axioms Probe.PdeApi.heat_slab_zero_interface
#print axioms _private.Poincare.D12.ConnectionCurvature.ConformalChartModel.0.Poincare.D12.ConnectionCurvature.conformalGamma.match_1.eq_1
#print axioms _private.Poincare.D12.ParabolicLocal.DerivativeLoss.0.Poincare.D12.ParabolicLocal.fderiv_heatConv_testF_coord._simp_1_5
#print axioms _private.Poincare.Stage6.TopologyBridge.0._aux_Poincare_Stage6_TopologyBridge___macroRules__private_Poincare_Stage6_TopologyBridge_0_termℝ___1
#print axioms _private.Poincare.VKPort.HatcherLib.Ch1.VanKampenAdaptedGrid.0.HatcherLib.rightCell._proof_3
#print axioms dotProductBilin.congr_simp
