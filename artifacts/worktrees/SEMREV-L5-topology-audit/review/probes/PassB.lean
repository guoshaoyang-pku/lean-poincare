/- SEMREV-L5 independent whole-release audit pass B: 437 modules. -/
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
import Poincare.D11.BochnerManifold.Basic
import Poincare.D11.BochnerManifold.Corollaries
import Poincare.D11.BochnerManifold.ModelSpace
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
import Poincare.D13.CriticalPathReview.AxiomAudit
import Poincare.D13.CriticalPathReview.B1DimensionOne
import Poincare.D13.CriticalPathReview.NegControl
import Poincare.D13.CriticalPathReview.PrintAxioms
import Poincare.D13.CriticalPathReview.PrintAxiomsAll
import Poincare.D13.CriticalPathReview.ScalarViability
import Poincare.D13.CriticalPathReview.StatementAudit
import Poincare.D13.CriticalPathReview.UsageProbe
import Poincare.D13.IntegratedAudit.AuditCore
import Poincare.D13.IntegratedAudit.ExpectedModules
import Poincare.D7.Bochner.Blocked
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
import Poincare.D7.ConjugateHeat.Laplacian
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
import Poincare.D7.Kappa.All
import Poincare.D7.Kappa.Audit
import Poincare.D7.Kappa.Basic
import Poincare.D7.Kappa.EntropyBridge
import Poincare.D7.Kappa.Nonvacuity
import Poincare.D7.Kappa.Probe
import Poincare.D7.Kappa.Statements
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
import Poincare.D7.Monotonicity.All
import Poincare.D7.Monotonicity.Blockers
import Poincare.D7.Monotonicity.BochnerCertificate
import Poincare.D7.Monotonicity.BochnerGradientEstimate
import Poincare.D7.Monotonicity.ConjugateHeatCertificate
import Poincare.D7.Monotonicity.FMonotonicity
import Poincare.D7.Monotonicity.Nonvacuity
import Poincare.D7.Monotonicity.ReducedVolumeInput
import Poincare.D7.Monotonicity.WMuMonotonicity
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
import Lean.Util.CollectAxioms
import Lean.Elab.Command

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command

namespace SemRevPassB

def approvedAxioms : List Name := [`propext,
  `Classical.choice,
  `Quot.sound]

def negControls : List Name := [`d12NegControlBadAxiom,
  `d12NegControlBadTheorem,
  `Poincare.D12.VolumeIBP.Audit.negativeControl,
  `Poincare.D13.CriticalPathReview.NegControl.negControlBadAxiom,
  `Poincare.D13.CriticalPathReview.NegControl.negControlBadTheorem]

def useTargets : List Name := [`Poincare.D12.SurgeryRecognition.doubleBallHomeoSphere,
  `Poincare.D12.SurgeryRecognition.sphereConnectSum_homeo_sphere,
  `Poincare.D12.SurgeryRecognition.sphereConnectSum_transported,
  `Poincare.D12.SurgeryRecognition.iteratedSphereSum_homeo_sphere,
  `Poincare.D12.SurgeryRecognition.ConnectedSumDecomposition.mkV2,
  `Poincare.D12.SurgeryRecognition.finiteFreeOrbit_isQuotientCoveringMap,
  `Poincare.D12.SurgeryRecognition.deckTrivial_of_simplyConnected_quotient,
  `Poincare.D12.SurgeryRecognition.stage6Target_of_v2decomposition,
  `Poincare.D12.SurgeryRecognition.stage6Target_of_v2hypotheses,
  `Poincare.D12.SurgeryRecognition.stage6Target_of_v3hypotheses,
  `Poincare.D12.SurgeryRecognition.AntipodalGroup,
  `Poincare.D7.Recognition.stage6Target_of_certificates,
  `Poincare.D12.TriangulationTopology.diskGlueQuotHomeoSphere,
  `Poincare.D12.TriangulationTopology.alexanderHomeo,
  `Poincare.D12.TriangulationTopology.alexanderHomeo_eq_refl_iff,
  `Poincare.D12.TriangulationTopology.sphereOfTwoDisks,
  `Poincare.D12.TriangulationTopology.sphereOfTwoDisks_hemisphere_instance,
  `Poincare.D7.SurgeryFlow.realLineProcedureChain_simplyConnected,
  `Poincare.Longrun.Topology.stage6Target_of_sphereRecognition,
  `Poincare.Longrun.Topology.stage6Target_of_compactThreeManifold,
  `Poincare.D7.Limit.HeatMeshConvergence,
  `Poincare.Longrun.Topology.stage6Target_iff_sphereRecognition,
  `Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses,
  `Poincare.D7.SurgeryFlow.missingFullNeckAnalysis,
  `Poincare.D7.SurgeryFlow.missingExtinctionTheorem,
  `Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem,
  `Poincare.Longrun.Surgery.ExtinctionTheorem,
  `Poincare.Longrun.Surgery.MissingInputs,
  `Poincare.Longrun.Evolution.FiniteMeshConvergence,
  `Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman,
  `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary,
  `Poincare.Longrun.Evolution.PerelmanApproximation,
  `Poincare.D7.Limit.HeatMeshConvergenceTheorem]

def inhabitTargets : List Name := [`Poincare.D10.TriangulationLowDim.MoiseTriangulationTheorem,
  `Poincare.D7.Limit.HeatMeshConvergenceTheorem,
  `Poincare.D7.Limit.ContinuousHeatMaximumPrincipleConjecture,
  `Poincare.D7.SurgeryFlow.missingFullNeckAnalysis,
  `Poincare.D7.SurgeryFlow.missingExtinctionTheorem,
  `Poincare.D7.SurgeryFlow.missingSurgeryFlowTheorem,
  `Poincare.D7.SurgeryFlow.missingAPrioriCurvatureEstimates,
  `Poincare.Longrun.Evolution.FiniteMeshConvergence,
  `Poincare.Longrun.Evolution.FiniteRepresentsContinuousPerelman,
  `Poincare.Longrun.Evolution.ContinuousPerelmanFMonotonicity,
  `Poincare.Longrun.Evolution.PerelmanApproximation,
  `Poincare.Longrun.Evolution.PerelmanEvolutionBoundary,
  `Poincare.D7.Recognition.ExtinctionCertificate,
  `Poincare.D7.Recognition.SphericalPieceRecognition,
  `Poincare.D7.Recognition.CanonicalNeighborhoodInput,
  `Poincare.D7.Recognition.RecognitionHypotheses,
  `Poincare.D12.SurgeryRecognition.ConnectedSumDecompositionV2,
  `Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV2,
  `Poincare.D12.SurgeryRecognition.RemainingRecognitionHypothesesV3,
  `Poincare.Longrun.Surgery.NeckAnalysis,
  `Poincare.Longrun.Surgery.MissingInputs,
  `Poincare.Longrun.Surgery.ExtinctionTheorem,
  `Poincare.D7.SurgeryFlow.NeckAnalysisHypotheses,
  `Poincare.D7.SurgeryFlow.ExtinctionData]

def packageRoots : List Name := [
  `Poincare, `Probe, `Ledger, `Audit, `ReleaseCheck, `ReleaseAudit, `D6AuditReport,
  `ReleaseClaims, `D6LedgerProbe]

def isUnder (roots : List Name) (m : Name) : Bool :=
  roots.any (fun r => r.isPrefixOf m)


run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let moduleOf (n : Name) : Name :=
    match env.getModuleIdxFor? n with
    | some i => mods.getD i .anonymous
    | none => .anonymous
  let inPkg (n : Name) : Bool := isUnder packageRoots (moduleOf n)
  let mut decls := 0
  let mut theorems := 0
  let mut axiomsUnexpected : Array Name := #[]
  let mut unsafeD : Array Name := #[]
  let mut partialD : Array Name := #[]
  let mut sorryUnexpected : Array Name := #[]
  let mut nativeUnexpected : Array Name := #[]
  let mut unapproved : Array (Name × Name) := #[]
  let mut proofWanted : Array Name := #[]
  let mut collectFail : Array (Name × String) := #[]
  let mut rows : Array (Name × ConstantInfo) := #[]
  for (n, ci) in env.constants.toList do
    if inPkg n then
      rows := rows.push (n, ci)
      decls := decls + 1
      if n.toString.contains "proof_wanted" then proofWanted := proofWanted.push n
      match ci with
      | .thmInfo _ => theorems := theorems + 1
      | .defnInfo v =>
          match v.safety with
          | .«unsafe» => unsafeD := unsafeD.push n
          | .«partial» => partialD := partialD.push n
          | .safe => pure ()
      | .axiomInfo _ => axiomsUnexpected := axiomsUnexpected.push n
      | _ => pure ()
      let axs ←
        try Lean.collectAxioms n
        catch _ => do
          collectFail := collectFail.push (n, "collectAxioms raised")
          pure #[]
      for a in axs do
        if a == `sorryAx then sorryUnexpected := sorryUnexpected.push n
        else if a == `Lean.ofReduceBool || a == `ofReduceBool then nativeUnexpected := nativeUnexpected.push n
        else if !approvedAxioms.contains a then
          unapproved := unapproved.push (n, a)
  -- registered negative controls are excused from the unapproved count but reported by name
  let unapprovedUnexpected := unapproved.filter (fun (n, _) => !negControls.contains n)
  IO.println s!"SEMREVPKG	decls	{decls}"
  IO.println s!"SEMREVPKG	theorems	{theorems}"
  IO.println s!"SEMREVPKG	axioms_unexpected	{axiomsUnexpected.size}"
  IO.println s!"SEMREVPKG	unsafe	{unsafeD.size}"
  IO.println s!"SEMREVPKG	partial	{partialD.size}"
  IO.println s!"SEMREVPKG	sorryAx_unexpected	{sorryUnexpected.size}"
  IO.println s!"SEMREVPKG	native_decide_unexpected	{nativeUnexpected.size}"
  IO.println s!"SEMREVPKG	unapproved_axiom_all	{unapproved.size}"
  IO.println s!"SEMREVPKG	unapproved_axiom_unexpected	{unapprovedUnexpected.size}"
  IO.println s!"SEMREVPKG	proof_wanted	{proofWanted.size}"
  IO.println s!"SEMREVPKG	collect_failures	{collectFail.size}"
  for n in axiomsUnexpected do IO.println s!"SEMREVFAIL	project_axiom	{n}"
  for n in unsafeD do IO.println s!"SEMREVFAIL	unsafe	{n}"
  for n in sorryUnexpected do IO.println s!"SEMREVFAIL	sorryAx	{n}"
  for n in nativeUnexpected do IO.println s!"SEMREVFAIL	native_decide	{n}"
  for n in proofWanted do IO.println s!"SEMREVFAIL	proof_wanted	{n}"
  for (n, a) in unapprovedUnexpected do IO.println s!"SEMREVFAIL	unapproved_axiom	{n}	{a}"
  for (n, e) in collectFail do IO.println s!"SEMREVFAIL	collect_exception	{n}	{e}"
  -- environment-level consumer counts for the cited declarations (own implementation)
  let useSet : NameSet := useTargets.foldl (fun acc t => acc.insert t) ({} : NameSet)
  let mut consumers : NameMap (Array Name) := {}
  for (n, ci) in rows do
    let used := ci.type.getUsedConstants.toList.eraseDups.toArray
    let used := match ci.value? true with
      | some v => used ++ v.getUsedConstants.toList.eraseDups.toArray
      | none => used
    for u in used do
      if useSet.contains u then
        consumers := consumers.insert u (((consumers.find? u).getD #[]).push n)
  for t in useTargets do
    let cs := (consumers.find? t).getD #[]
    IO.println s!"SEMREVUSE	{t}	{cs.size}	{";".intercalate (cs.toList.eraseDups.take 12 |>.map Name.toString)}"
  -- inhabitant scan: any package declaration whose type concludes in a statement-only target
  let inhSet : NameSet := inhabitTargets.foldl (fun acc t => acc.insert t) ({} : NameSet)
  let inhabitants ← liftTermElabM do
    let mut inhabitants : Array (Name × Name × String) := #[]
    let rec peelForalls (e : Expr) : Expr :=
      match e with
      | .forallE _ _ b _ => peelForalls b
      | e => e
    for (n, ci) in rows do
      if n == `sorryAx then continue
      match ci with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
          let hitTarget (e : Expr) : Option Name :=
            let head := e.getAppFn
            match head with
            | .const h _ =>
                if inhSet.contains h && h != n then some h
                else if h == ``Nonempty then
                  match e.getAppArgs[0]? with
                  | some a =>
                      match a.getAppFn with
                      | .const h2 _ => if inhSet.contains h2 && h2 != n then some h2 else none
                      | _ => none
                  | none => none
                else none
            | _ => none
          match hitTarget (peelForalls ci.type) with
          | some h => inhabitants := inhabitants.push (n, h, "syntactic")
          | none =>
              let hit ← try
                  Meta.forallTelescopeReducing ci.type fun _ body => do
                    return hitTarget body
                catch _ => pure none
              if let some h := hit then
                inhabitants := inhabitants.push (n, h, "reduced")
      | _ => pure ()
    return inhabitants
  IO.println s!"SEMREVINH	count	{inhabitants.size}"
  for (n, t, how) in inhabitants do IO.println s!"SEMREVINH	{n}	{t}	{how}"
  -- conclusion-equivalence scan (reviewer's own implementation):
  -- a theorem whose hypothesis type is definitionally equal to its conclusion
  let equiv ← liftTermElabM do
    let mut hits : Array (Name × Nat) := #[]
    for (n, ci) in rows do
      match ci with
      | .thmInfo _ =>
          let hit ← try
              Meta.forallTelescopeReducing ci.type fun _ body => do
                let lctx ← getLCtx
                let mut found : Option Nat := none
                let mut idx := 0
                for x in lctx do
                  if !x.isLet && !x.isImplementationDetail then
                    let same := Expr.equal x.type body
                    let deq ← try Meta.isDefEq x.type body catch _ => pure false
                    if (same || deq) && found.isNone then found := some idx
                    idx := idx + 1
                return found
            catch _ => pure none
          if let some i := hit then hits := hits.push (n, i)
      | _ => pure ()
    return hits
  IO.println s!"SEMREVEQUIV	count	{equiv.size}"
  for (n, i) in equiv do IO.println s!"SEMREVEQUIV	{n}	hyp#{i}"
  IO.println "SEMREVPASS DONE"


end SemRevPassB
