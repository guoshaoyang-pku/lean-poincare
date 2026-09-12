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

#print axioms D4Audit.counterexample_continuous_c_half_is_evolution
#print axioms D4Audit.transfer_nonvacuous
#print axioms HatcherLib.CoveredPathChain.PrefixDecomposition.casesOn
#print axioms HatcherLib.CoveredPathChain.extend.congr_simp
#print axioms HatcherLib.CoveredSubdivisionPrefix.chain
#print axioms HatcherLib.PathConnectedOpenCover.noConfusionType
#print axioms HatcherLib.VanKampenSquareGrid.CellBoundaryRelation
#print axioms HatcherLib.VanKampenSquareGrid.coordinateLine._proof_1
#print axioms HatcherLib.VanKampenSquareGrid.horizontalParameterEdge
#print axioms HatcherLib.VanKampenSquareGrid.vertex.eq_1
#print axioms HatcherLib.VanKampenSquareGrid.verticalParameterEdge._proof_1
#print axioms HatcherLib.VanKampenSweepCell.mk._flat_ctor
#print axioms HatcherLib.VanKampenSweepRow.mk.noConfusion
#print axioms HatcherLib.VanKampenSweepStage.chainInput.match_1
#print axioms HatcherLib.VanKampenWordMove.eraseOne
#print axioms HatcherLib.coveredSubdivisionPrefix._proof_10
#print axioms HatcherLib.fundamentalGroup_mapOfEq_rfl
#print axioms HatcherLib.subgroup_of_free_is_free
#print axioms HatcherLib.vanKampenWordEquivalent_cellBoundary
#print axioms Perelman.FProfile
#print axioms Perelman.MetricFlowData.zero_mem
#print axioms Perelman.ScalarCurvatureLowerBound
#print axioms Perelman.constantFlow._proof_4
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.ScalarContractionData.noConfusionType
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.first_pair_skew_add_zero'
#print axioms Poincare.CurvatureAlgebra.CurvatureOperator.scalarCurvature.eq_1
#print axioms Poincare.D10.BochnerEuclidean.basis_apply
#print axioms Poincare.D10.HeatKernelEuclidean.gaussianKernel._proof_1
#print axioms Poincare.D10.MaximumPrincipleRN.HeatSubsolutionData.casesOn
#print axioms Poincare.D10.MaximumPrincipleRN.hasDerivWithinAt_nonneg_of_isMaxOn_Icc
#print axioms Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex.decidableIsTwoDimensional._aux_1
#print axioms Poincare.D10.TriangulationLowDim.FiniteAbstractSimplicialComplex.vertices.eq_1
#print axioms Poincare.D10.TriangulationLowDim.tetrahedronBoundary_eulerChar
#print axioms Poincare.D10.algebra_hyperbolic._simp_1_2
#print axioms Poincare.D10.jacobiSolFlat_solvesJacobiODE
#print axioms Poincare.D11.BochnerManifold.d7_gradient_estimate_gives_model_subharmonic
#print axioms Poincare.D11.BochnerManifold.jacobiMeanCurvature_deriv_eq._simp_1_1
#print axioms Poincare.D11.BochnerManifold.modelLap
#print axioms Poincare.D11.HeatKernelBridge.HeatKernelCore.c_up_pos
#print axioms Poincare.D11.HeatKernelBridge.flatHeatKernelCore
#print axioms Poincare.D11.HeatKernelBridge.flatKernel.eq_1
#print axioms Poincare.D11.MaximumPrincipleTensor.PositivityPreserving.comp
#print axioms Poincare.D11.MaximumPrincipleTensor.posSemidef_iff_quadForm_nonneg
#print axioms Poincare.D11.ReducedVolume.ManifoldReducedVolumeInterface.casesOn
#print axioms Poincare.D11.ReducedVolume.euclideanReducedVolumeCertificate_flow
#print axioms Poincare.D11.ReducedVolume.reducedVolumeIntegrand
#print axioms Poincare.D11.SpectralTorus.fact_zero_lt_one
#print axioms Poincare.D11.SpectralTorus.mFourier_ne_zero
#print axioms Poincare.D11.SpectralTorus.sobolevNorm.eq_1
#print axioms Poincare.D11.SpectralTorus.torusQuotHom
#print axioms Poincare.D11.SpectralTorus.trigPoly_pointwise_le
#print axioms Poincare.D11.divergenceLaplacian_id_jacobiSol
#print axioms Poincare.D11.wronskian_le_zero
#print axioms Poincare.D12.ComparisonGeodesics.areaRatio_hasDerivAt._simp_1_4
#print axioms Poincare.D12.ComparisonGeodesics.hasDerivAtR_id
#print axioms Poincare.D12.ComparisonGeodesics.sign_constant_of_no_zero
#print axioms Poincare.D12.ConnectionCurvature.ChartMetricCoefficients.g_symm
#print axioms Poincare.D12.ConnectionCurvature.SmoothChartData._sizeOf_inst
#print axioms Poincare.D12.ConnectionCurvature.SmoothChartData.nabla_smul
#print axioms Poincare.D12.ConnectionCurvature.VectorField
#print axioms Poincare.D12.ConnectionCurvature.conformalGamma.match_1
#print axioms Poincare.D12.ConnectionCurvature.form_nabla_second_eq_sum
#print axioms Poincare.D12.EntropyVariation.Euc
#print axioms Poincare.D12.EntropyVariation.fflow_FDissipation_value
#print axioms Poincare.D12.EntropyVariation.fflow_riccHess_justified
#print axioms Poincare.D12.EntropyVariation.integrable_shrinkerWDissipationDensity_mul
#print axioms Poincare.D12.EntropyVariation.shrinkerEntropyData_FDissipationCorrected_value._simp_1_7
#print axioms Poincare.D12.EntropyVariation.shrinker_W_derivative_identity
#print axioms Poincare.D12.GeometricCompactness.gridSet
#print axioms Poincare.D12.GeometricCompactness.unitSquare
#print axioms Poincare.D12.HeatDomain.bump_weakInitialConditionFor_ccClass
#print axioms Poincare.D12.HeatDomain.volume_set_norm_ge_eq_top
#print axioms Poincare.D12.HeatSemigroup.heatKernelMulFDerivCLM_apply._simp_1_6
#print axioms Poincare.D12.HeatSemigroup.heatOperator_lintegral_enorm_le
#print axioms Poincare.D12.KappaVariational.ClosureRecord.downstreamUseDecl
#print axioms Poincare.D12.KappaVariational.constantCurvature_length_le
#print axioms Poincare.D12.KappaVariational.gaussianVecTau_def
#print axioms Poincare.D12.ParabolicLocal.BUCf._sizeOf_1
#print axioms Poincare.D12.ParabolicLocal.BUCf.instNormedAddCommGroupBUCn._proof_4
#print axioms Poincare.D12.ParabolicLocal.DuhamelSetup.casesOn
#print axioms Poincare.D12.ParabolicLocal.DuhamelSetup.mk.noConfusion
#print axioms Poincare.D12.ParabolicLocal.derivativeLossBarrier
#print axioms Poincare.D12.ParabolicLocal.heatConv.eq_1
#print axioms Poincare.D12.ParabolicLocal.heatOperatorCLM
#print axioms Poincare.D12.ParabolicLocal.linearCandidate_isFixedPt._simp_1_7
#print axioms Poincare.D12.SemanticLedger.R_sq
#print axioms Poincare.D12.SpectralSobolev.heatCoeffs_apply
#print axioms Poincare.D12.SpectralSobolev.sq_eigenvalue_pos
#print axioms Poincare.D12.SurgeryRecognition.EndGameDecomposition.noConfusion
#print axioms Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2.rec
#print axioms Poincare.D12.SurgeryRecognition.SphericalSpaceFormModel.instMulAction
#print axioms Poincare.D12.SurgeryRecognition.antipodalGroup_card
#print axioms Poincare.D12.SurgeryRecognition.downPoint_continuous
#print axioms Poincare.D12.SurgeryRecognition.height_sphereBallPart_eq_neg_fst_of_nonpos
#print axioms Poincare.D12.SurgeryRecognition.northPole
#print axioms Poincare.D12.SurgeryRecognition.southHemisphereHomeo
#print axioms Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition
#print axioms Poincare.D12.TensorMaximumBochner.Audit.d12_so3_bochner_audited
#print axioms Poincare.D12.TensorMaximumBochner.Bochner.DerivationData.mk.noConfusion
#print axioms Poincare.D12.TensorMaximumBochner.Bochner.gamma._proof_2
#print axioms Poincare.D12.TensorMaximumBochner.Bochner.sum_gammaX_bilin_pair._abel_1_1
#print axioms Poincare.D12.TensorMaximumBochner.So3.stdMetric
#print axioms Poincare.D12.TensorMaximumBochner.So3Polynomial.crossDerivation._proof_1
#print axioms Poincare.D12.TensorMaximumBochner.So3Polynomial.xVec
#print axioms Poincare.D12.TensorMaximumBochner.counterexampleA
#print axioms Poincare.D12.TensorMaximumBochner.quadSelfSquareSub
#print axioms Poincare.D12.TriangulationTopology.antipodalSmul.eq_1
#print axioms Poincare.D12.TriangulationTopology.continuous_esnoc'
#print axioms Poincare.D12.TriangulationTopology.diskGlueRel
#print axioms Poincare.D12.TriangulationTopology.esnoc'
#print axioms Poincare.D12.TriangulationTopology.loop_cast_source
#print axioms Poincare.D12.TriangulationTopology.radialExtend._proof_1
#print axioms Poincare.D12.TriangulationTopology.rpCompactSpace
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryConeHomeoSimplex._proof_2
#print axioms Poincare.D12.TriangulationTopology.simplexBoundaryToSphere
#print axioms Poincare.D12.TriangulationTopology.simplexLambda_pos_of_unit
#print axioms Poincare.D12.TriangulationTopology.sphereOfTwoDisks._proof_10
#print axioms Poincare.D12.TriangulationTopology.sphere_pi1_subsingleton
#print axioms Poincare.D12.TriangulationTopology.trivialization_id._proof_6
#print axioms Poincare.D12.VolumeIBP.ChartDiffeomorphism.recOn
#print axioms Poincare.D12.VolumeIBP.ChartMetric.driftLaplacian.eq_1
#print axioms Poincare.D12.VolumeIBP.ChartMetric.invMatrix_symm
#print axioms Poincare.D12.VolumeIBP.ChartMetric.recOn
#print axioms Poincare.D13.IntegratedAudit.claimedPairs
#print axioms Poincare.D7.Bochner.BlockerHessian_ne_nil
#print axioms Poincare.D7.Bochner.Conf
#print axioms Poincare.D7.Bochner.RawGradientModel.rec
#print axioms Poincare.D7.Bochner.curvedExampleCertificate._proof_4
#print axioms Poincare.D7.Canonical.BlockerCurvature
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodCertificate.capOf
#print axioms Poincare.D7.Canonical.CanonicalNeighborhoodHypotheses.mk.inj
#print axioms Poincare.D7.Canonical.CurvatureScaleDatum.inst₁
#print axioms Poincare.D7.Canonical.CylinderInterface.rec
#print axioms Poincare.D7.Canonical.EpsilonApproximation.refl._proof_3
#print axioms Poincare.D7.Canonical.EpsilonNeck.mk.sizeOf_spec
#print axioms Poincare.D7.Canonical.MetricNoncollapsing.mk.noConfusion
#print axioms Poincare.D7.Canonical.cylinder_certificate._proof_3
#print axioms Poincare.D7.Canonical.not_conclusion_scale_of_two_mul_lt
#print axioms Poincare.D7.Canonical.twoIntervalCap_certificate
#print axioms Poincare.D7.Compactness.ConstSubsequence.ctorIdx
#print axioms Poincare.D7.Compactness.GHConvergenceData.mono._proof_3
#print axioms Poincare.D7.Compactness.GHPrecompactCertificate.mk._flat_ctor
#print axioms Poincare.D7.Compactness.ManifoldFamilyHypotheses.noConfusionType
#print axioms Poincare.D7.Compactness.constSubsequence._proof_2
#print axioms Poincare.D7.Compactness.unitFamily_isCompact_closedBall
#print axioms Poincare.D7.ConjugateHeat.ConjugateHeatSpacetime.zero_volume
#print axioms Poincare.D7.ConjugateHeat.conjugateHeatStep_eq_add_generator
#print axioms Poincare.D7.ConjugateHeat.cycle_conjugateHeatJet
#print axioms Poincare.D7.ConjugateHeat.laplaceBeltrami._proof_2
#print axioms Poincare.D7.Curvature.BlockerSecondBianchi_ne_nil
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.TwoPlane.mk.sizeOf_spec
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.curvature_apply_eq
#print axioms Poincare.D7.Curvature.RiemannCurvatureData.recOn
#print axioms Poincare.D7.Curvature.So3.crossBracket
#print axioms Poincare.D7.Divergence.BlockerManifoldBoundary
#print axioms Poincare.D7.Divergence.DivergenceData.inFlux
#print axioms Poincare.D7.Divergence.IBPCertificate.eq_zero_of_boundaryTerm_eq_zero
#print axioms Poincare.D7.Divergence.ManifoldDivergenceDatum.volume
#print axioms Poincare.D7.Divergence.slabExample_fluxTerm
#print axioms Poincare.D7.EvolutionSharp.PerelmanFStepLtOld
#print axioms Poincare.D7.EvolutionSharp.perelmanAntitoneCertificate_discrete_sharp_lower
#print axioms Poincare.D7.Geodesic.FlatMetric.mk
#print axioms Poincare.D7.Geodesic.GeodesicData.isGeodesic
#print axioms Poincare.D7.Geodesic.IsMetricCompatible._proof_2
#print axioms Poincare.D7.Geodesic.isGeodesic_zero_iff
#print axioms Poincare.D7.HeatKernel.FiniteGridHeatKernel.recOn
#print axioms Poincare.D7.HeatKernel.HeatKernelData.dist_self
#print axioms Poincare.D7.HeatKernel.HeatSpacetime.isClosedRiemannian_zero_of_isEmpty
#print axioms Poincare.D7.HeatKernel.IsHeatKernel.positive
#print axioms Poincare.D7.HeatKernel.heatStep_stepSub_u0
#print axioms Poincare.D7.HeatKernel.stepSub_col'
#print axioms Poincare.D7.Kappa.BallVolumeComparison.mk
#print axioms Poincare.D7.Kappa.KappaCertificate.noConfusionType
#print axioms Poincare.D7.Kappa.KappaComparisonData.v0_le_volume
#print axioms Poincare.D7.Kappa.phi_uniformLowerBound
#print axioms Poincare.D7.LeviCivita.ChartMetricData.mk.sizeOf_spec
#print axioms Poincare.D7.LeviCivita.SmoothCoefficientSystem.mk.noConfusion
#print axioms Poincare.D7.LeviCivita.connectionCoefficient
#print axioms Poincare.D7.LeviCivita.isMetricCompatible_coefficient_relation_affine
#print axioms Poincare.D7.Limit.ConsistencyCertificate.alpha_eq
#print axioms Poincare.D7.Limit.ConsistencyCertificate.toHeatGridEvolution._proof_3
#print axioms Poincare.D7.Limit.GridMesh.x_le_b
#print axioms Poincare.D7.Limit.HeatMeshSequence.Δt
#print axioms Poincare.D7.Limit.SlabGrid.toHeatGridEvolution._proof_1
#print axioms Poincare.D7.Limit.heatMeshConvergence_of_stability
#print axioms Poincare.D7.Limit.quad_error_zero
#print axioms Poincare.D7.Monotonicity.ReducedVolumeWDuality.recOn
#print axioms Poincare.D7.Recognition.CanonicalNeighborhoodInput.rec
#print axioms Poincare.D7.Recognition.ExtinctionCertificate.extinctsInFiniteTime
#print axioms Poincare.D7.Recognition.ExtinctionConclusion.recOn
#print axioms Poincare.D7.Recognition.RecognitionHypotheses.mk.sizeOf_spec
#print axioms Poincare.D7.Recognition.SphericalPieceRecognition._sizeOf_inst
#print axioms Poincare.D7.Recognition.sphericalPieces_of_geometrization
#print axioms Poincare.D7.Reduced.JacobianComparison
#print axioms Poincare.D7.Reduced.LPath.mk.inj
#print axioms Poincare.D7.Reduced.MetricFlowInterface.noConfusionType
#print axioms Poincare.D7.Reduced.ReducedLengthDensityCertificate.density_hasDerivAt
#print axioms Poincare.D7.Reduced.ReducedVolumeCertificate.derivative_nonpos
#print axioms Poincare.D7.Reduced.gaussianFlow._proof_3
#print axioms Poincare.D7.Reduced.gaussian_integrand._simp_1_2
#print axioms Poincare.D7.RicciScalar.BlockerPerelmanScalarRealization_ne_nil
#print axioms Poincare.D7.RicciScalar.FlowPath.TraceCommutationStatement
#print axioms Poincare.D7.RicciScalar.permBasis._proof_1
#print axioms Poincare.D7.RicciScalar.prodData_scalarMetricTrace
#print axioms Poincare.D7.RicciScalar.scalarCurvature_eq_basisTrace
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.gauge
#print axioms Poincare.D7.ShortTime.DeTurckCertificate.ricci_congruence_gauge
#print axioms Poincare.D7.ShortTime.LipschitzVectorField.mk.inj
#print axioms Poincare.D7.ShortTime.RicciFlowData.mk.noConfusion
#print axioms Poincare.D7.ShortTime.deTurckRHS_add_gauge._abel_1_1
#print axioms Poincare.D7.ShortTime.matrixProblem
#print axioms Poincare.D7.ShortTime.trivialDeTurckCertificate._proof_2
#print axioms Poincare.D7.SurgeryFlow.CurvatureBoundInterface.noConfusionType
#print axioms Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses.certificate
#print axioms Poincare.D7.SurgeryFlow.ProcedureChain.noConfusion
#print axioms Poincare.D7.SurgeryFlow.SurgeryProcedureData.mk.injEq
#print axioms Poincare.D7.SurgeryFlow.SurgerySchedule.isClosed_and_isDiscrete_range
#print axioms Poincare.D7.SurgeryFlow.realLineProcedure
#print axioms Poincare.D7.SurgeryFlow.toy_extinction_time_le._proof_1_1
#print axioms Poincare.D7.TensorLaplacian.ScalarEvolutionCertificate.mk.congr_simp
#print axioms Poincare.D7.TensorLaplacian.SmoothScalarEvolutionDatum.noConfusion
#print axioms Poincare.D7.TensorLaplacian.So3Example.so3EvolutionCertificate._proof_1
#print axioms Poincare.D7.TensorLaplacian.TensorConnectionData.ScalarCurvatureCommutationCertificate.frame_trace_eq
#print axioms Poincare.D7.TensorLaplacian.TensorConnectionData.curvature_zero₃
#print axioms Poincare.D7.TensorLaplacian.TensorConnectionData.roughLaplacianₗ._proof_1
#print axioms Poincare.D7.TensorLaplacian.pairingH
#print axioms Poincare.D7.TensorLaplacian.prodTensorData._proof_9
#print axioms Poincare.D7.Volume.TopFormBundle
#print axioms Poincare.D7.Volume.VolumeFormData.mk.sizeOf_spec
#print axioms Poincare.D7.Volume.VolumeFormData.volumeForm_def
#print axioms Poincare.D8.Fidelity.FidelityEntry.mk._flat_ctor
#print axioms Poincare.D8.Fidelity.PLStructure.homeo
#print axioms Poincare.D8.Fidelity.SmoothStructure.smooth
#print axioms Poincare.D9.CheegerGromov.CkCloseAtScale.ball_subset_chart
#print axioms Poincare.D9.CheegerGromov.CkConvergence.isImmersion_emb
#print axioms Poincare.D9.CheegerGromov.CompactExhaustion.subset_of_le
#print axioms Poincare.D9.CheegerGromov.PointedManifold.CkCloseOnChart.mono
#print axioms Poincare.D9.CheegerGromov.PointedManifoldWithRadius.casesOn
#print axioms Poincare.D9.CheegerGromov.pullbackMetric._proof_4
#print axioms Poincare.D9.ParabolicEstimates.DirichletForm.mk.inj
#print axioms Poincare.D9.ParabolicEstimates.IsMatrixLaplacian.mk
#print axioms Poincare.D9.ParabolicEstimates.ParabolicL2ToHkSmoothing
#print axioms Poincare.D9.ParabolicEstimates.SemiDiscreteHeatFlow.rec
#print axioms Poincare.D9.ParabolicEstimates.WeakSolution.noConfusion
#print axioms Poincare.D9.ParabolicEstimates.matrix_parabolicL2Bound
#print axioms Poincare.D9.Surfaces.BernsteinBandoShiUnnormalizedStatement
#print axioms Poincare.D9.Surfaces.SurfaceFlow.casesOn
#print axioms Poincare.D9.Surfaces.isLogisticSolution_deficit
#print axioms Poincare.D9.TensorAlgebra.TensorBundleData.dualPairing_add_right
#print axioms Poincare.D9.TensorAlgebra.TensorFiber._proof_2
#print axioms Poincare.D9.TensorAlgebra.TraceDivergenceInterface._sizeOf_inst
#print axioms Poincare.GaussianToolbox.gaussianVariance_convolutionParam
#print axioms Poincare.Longrun.AncientKappa.AncientSolution.casesOn
#print axioms Poincare.Longrun.AncientKappa.CanonicalNeighborhoodType.ofNat
#print axioms Poincare.Longrun.AncientKappa.KappaNoncollapsingAllScales.toKappaNoncollapsing
#print axioms Poincare.Longrun.AncientKappa.PointedKappaSolution3D.noConfusion
#print axioms Poincare.Longrun.AncientKappa.fderiv_fderiv_gaussianPotential
#print axioms Poincare.Longrun.CurvatureODE.DiscreteEvolution.step
#print axioms Poincare.Longrun.CurvatureODE.ReactionField.mk.inj
#print axioms Poincare.Longrun.CurvatureODE.eulerStep
#print axioms Poincare.Longrun.DeTurck.ConnectionLayer.casesOn
#print axioms Poincare.Longrun.DeTurck.FlowInterface.PullbackEquivalenceBackward
#print axioms Poincare.Longrun.DeTurck.RicciDeTurckComponents.flowRHS
#print axioms Poincare.Longrun.DeTurck.laplacianSymbol
#print axioms Poincare.Longrun.Entropy.AntitoneCertificate.lower_le
#print axioms Poincare.Longrun.Entropy.ContinuousAntitoneCertificate.rec
#print axioms Poincare.Longrun.Entropy.EntropyData.HasConjugateWeight
#print axioms Poincare.Longrun.Entropy.EntropyRegularityBridge.mk
#print axioms Poincare.Longrun.Entropy.MonotoneCertificate.mk._flat_ctor
#print axioms Poincare.Longrun.Entropy.continuousMonotoneCertificate_zero
#print axioms Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman
#print axioms Poincare.Longrun.Evolution.continuousPerelmanCertificate._proof_2
#print axioms Poincare.Longrun.Evolution.perelmanAntitoneCertificate._proof_2
#print axioms Poincare.Longrun.Evolution.unitReactionField.eq_1
#print axioms Poincare.Longrun.Geometry.AbstractConnection.noConfusionType
#print axioms Poincare.Longrun.Geometry.LeviCivitaData.toCurvatureOperator
#print axioms Poincare.Longrun.Geometry.MetricData.form
#print axioms Poincare.Longrun.Geometry.RiemannCurvatureTensor_bianchi
#print axioms Poincare.Longrun.PDE.HeatGridEvolution.boundary_right
#print axioms Poincare.Longrun.PDE.discreteLaplacian._proof_1
#print axioms Poincare.Longrun.Surgery.ChainCertificate.orientable_preserved
#print axioms Poincare.Longrun.Surgery.LedgerPredicates
#print axioms Poincare.Longrun.Surgery.NeckAnalysis.casesOn
#print axioms Poincare.Longrun.Surgery.SurgeryCertificate.trivial
#print axioms Poincare.Longrun.Surgery.SurgeryDatum.casesOn
#print axioms Poincare.Longrun.Surgery.ToyChain
#print axioms Poincare.Longrun.Surgery.toyRel_nonempty
#print axioms Poincare.Longrun.Topology.KappaNoncollapsingCertificate.exists_uniform_unit_ball_lower_bound
#print axioms Poincare.Longrun.Topology.NormalizedVolumeLowerBound.recOn
#print axioms Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold
#print axioms Poincare.RiemannAdapter.RiemannianCurvatureData.rec
#print axioms Probe.CurvatureTensor
#print axioms Probe.CurvatureTensor.toCurvatureOperator._proof_19
#print axioms Probe.CurvatureTensor.zero.eq_1
#print axioms _private.Poincare.D10.HeatKernelEuclidean.AxiomAudit.0.heatKernelAuditedDeclarations
#print axioms _private.Poincare.D12.HeatSemigroup.Semigroup.0.Poincare.D12.HeatSemigroup.truncation_tendsto
#print axioms _private.Poincare.D12.TriangulationTopology.SpherePolygonal.0.Poincare.D12.TriangulationTopology.restrictionChain.match_1.eq_1
#print axioms _private.Poincare.VKPort.HatcherLib.Ch1.VanKampenAdaptedGrid.0.HatcherLib.dominoAnchor_le_or_succ._proof_1_1
#print axioms _private.Poincare.VKPort.HatcherLib.Ch1.VanKampenGlobalSweep.0.HatcherLib.VanKampenSweepCell.outputWord.match_1.splitter
