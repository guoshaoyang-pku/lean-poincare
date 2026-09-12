/-
SEMREV independent fail-closed census probe for D13-heatkernel-bridge-d10-d7.
Written for longrun task SEMREV-D13-cross-audit-ophis; imports the transported snapshot only.
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
import Poincare.D11.HeatKernelBridge.All
import Poincare.D11.HeatKernelBridge.AxiomAudit
import Poincare.D11.HeatKernelBridge.Basic
import Poincare.D11.HeatKernelBridge.EuclideanInstance
import Poincare.D11.HeatKernelBridge.EuclideanLaplacian
import Poincare.D11.HeatKernelBridge.InitialCondition
import Poincare.D11.HeatKernelBridge.ZeroDimension
import Poincare.D12.HeatDomain.All
import Poincare.D12.HeatDomain.AxiomAudit
import Poincare.D12.HeatDomain.CompactCompatibility
import Poincare.D12.HeatDomain.Counterexample
import Poincare.D12.HeatDomain.FlatInstance
import Poincare.D12.HeatDomain.TestFunction
import Poincare.D13.HeatKernelBridge.All
import Poincare.D13.HeatKernelBridge.AxiomAudit
import Poincare.D13.HeatKernelBridge.Basic
import Poincare.D13.HeatKernelBridge.CompactUpgrade
import Poincare.D13.HeatKernelBridge.ConjugateHeatBridge
import Poincare.D13.HeatKernelBridge.DataRefutation
import Poincare.D13.HeatKernelBridge.EuclideanTransport
import Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness
import Poincare.D13.HeatKernelBridge.FiniteSpaceHeat
import Poincare.D13.HeatKernelBridge.FiniteUniqueness
import Poincare.D13.HeatKernelBridge.GeometricRepair
import Poincare.D13.HeatKernelBridge.LaplacianSymmetryRefutation
import Poincare.D13.HeatKernelBridge.PDERepair
import Poincare.D13.HeatKernelBridge.PredicateSemantics
import Poincare.D13.HeatKernelBridge.StatementRefutation
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
import Poincare.D7.ConjugateHeat.Status
import Poincare.D7.ConjugateHeat.UniquenessStatus
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
import Poincare.D7.HeatKernel.DataStatus
import Poincare.D7.HeatKernel.Example
import Poincare.D7.HeatKernel.FiniteStatus
import Poincare.D7.HeatKernel.Grid
import Poincare.D7.HeatKernel.Instance
import Poincare.D7.HeatKernel.Probe
import Poincare.D7.HeatKernel.RepairStatus
import Poincare.D7.HeatKernel.StatementStatus
import Poincare.D7.HeatKernel.UniquenessStatus
import Poincare.D7.HeatKernel.V1Interface
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
import Lean.Util.CollectAxioms

open Lean Elab Command

namespace SEMREV_D13_heatkernel_bridge_d10_d7

def approvedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def negativeControlModules : List Name := [
  ]

def auditedModules : List Name := [
  "Poincare.D10.BochnerEuclidean.Axioms".toName,
  "Poincare.D10.BochnerEuclidean.Basic".toName,
  "Poincare.D10.BochnerEuclidean.Bochner".toName,
  "Poincare.D10.BochnerEuclidean.Compat".toName,
  "Poincare.D10.BochnerEuclidean.Corollary".toName,
  "Poincare.D10.GaussianToolbox.Basic".toName,
  "Poincare.D10.GaussianToolbox.Convolution".toName,
  "Poincare.D10.GaussianToolbox.Multivariate".toName,
  "Poincare.D10.GaussianToolbox.PrintAxioms".toName,
  "Poincare.D10.HeatKernelEuclidean.AxiomAudit".toName,
  "Poincare.D10.HeatKernelEuclidean.Basic".toName,
  "Poincare.D10.HeatKernelEuclidean.GaussianIntegral".toName,
  "Poincare.D10.HeatKernelEuclidean.HeatEquation".toName,
  "Poincare.D10.HeatKernelEuclidean.Mass".toName,
  "Poincare.D10.HeatKernelEuclidean.Semigroup".toName,
  "Poincare.D10.JacobiConstantCurvature.AxiomAudit".toName,
  "Poincare.D10.JacobiConstantCurvature.Basic".toName,
  "Poincare.D10.JacobiConstantCurvature.Comparison".toName,
  "Poincare.D10.JacobiConstantCurvature.ODE".toName,
  "Poincare.D10.MaximumPrincipleRN.AxiomAudit".toName,
  "Poincare.D10.MaximumPrincipleRN.Basic".toName,
  "Poincare.D10.MaximumPrincipleRN.SecondDerivativeTest".toName,
  "Poincare.D10.MaximumPrincipleRN.Semidiscrete".toName,
  "Poincare.D10.MaximumPrincipleRN.WeakMaximumPrinciple".toName,
  "Poincare.D10.TriangulationLowDim.Audit".toName,
  "Poincare.D10.TriangulationLowDim.Complex".toName,
  "Poincare.D10.TriangulationLowDim.Models".toName,
  "Poincare.D10.TriangulationLowDim.Moise".toName,
  "Poincare.D11.HeatKernelBridge.All".toName,
  "Poincare.D11.HeatKernelBridge.AxiomAudit".toName,
  "Poincare.D11.HeatKernelBridge.Basic".toName,
  "Poincare.D11.HeatKernelBridge.EuclideanInstance".toName,
  "Poincare.D11.HeatKernelBridge.EuclideanLaplacian".toName,
  "Poincare.D11.HeatKernelBridge.InitialCondition".toName,
  "Poincare.D11.HeatKernelBridge.ZeroDimension".toName,
  "Poincare.D12.HeatDomain.All".toName,
  "Poincare.D12.HeatDomain.AxiomAudit".toName,
  "Poincare.D12.HeatDomain.CompactCompatibility".toName,
  "Poincare.D12.HeatDomain.Counterexample".toName,
  "Poincare.D12.HeatDomain.FlatInstance".toName,
  "Poincare.D12.HeatDomain.TestFunction".toName,
  "Poincare.D13.HeatKernelBridge.All".toName,
  "Poincare.D13.HeatKernelBridge.AxiomAudit".toName,
  "Poincare.D13.HeatKernelBridge.Basic".toName,
  "Poincare.D13.HeatKernelBridge.CompactUpgrade".toName,
  "Poincare.D13.HeatKernelBridge.ConjugateHeatBridge".toName,
  "Poincare.D13.HeatKernelBridge.ConjugateScalarCurvature".toName,
  "Poincare.D13.HeatKernelBridge.DataRefutation".toName,
  "Poincare.D13.HeatKernelBridge.EuclideanTransport".toName,
  "Poincare.D13.HeatKernelBridge.FiniteConjugateUniqueness".toName,
  "Poincare.D13.HeatKernelBridge.FiniteSpaceHeat".toName,
  "Poincare.D13.HeatKernelBridge.FiniteUniqueness".toName,
  "Poincare.D13.HeatKernelBridge.GeometricRepair".toName,
  "Poincare.D13.HeatKernelBridge.LaplacianSymmetryRefutation".toName,
  "Poincare.D13.HeatKernelBridge.PDERepair".toName,
  "Poincare.D13.HeatKernelBridge.PredicateSemantics".toName,
  "Poincare.D13.HeatKernelBridge.StatementRefutation".toName,
  "Poincare.D7.Bochner.Audit".toName,
  "Poincare.D7.Bochner.Basic".toName,
  "Poincare.D7.Bochner.Blocked".toName,
  "Poincare.D7.Bochner.Euclidean".toName,
  "Poincare.D7.Bochner.Example".toName,
  "Poincare.D7.Bochner.GradientEstimate".toName,
  "Poincare.D7.Bochner.Probe".toName,
  "Poincare.D7.Canonical.All".toName,
  "Poincare.D7.Canonical.Audit".toName,
  "Poincare.D7.Canonical.Basic".toName,
  "Poincare.D7.Canonical.Classification".toName,
  "Poincare.D7.Canonical.Curvature".toName,
  "Poincare.D7.Canonical.Models".toName,
  "Poincare.D7.Canonical.Probe".toName,
  "Poincare.D7.Canonical.Statements".toName,
  "Poincare.D7.Compactness.All".toName,
  "Poincare.D7.Compactness.Audit".toName,
  "Poincare.D7.Compactness.Basic".toName,
  "Poincare.D7.Compactness.ManifoldStatements".toName,
  "Poincare.D7.Compactness.Nonvacuity".toName,
  "Poincare.D7.Compactness.Probe".toName,
  "Poincare.D7.Compactness.TotalBounded".toName,
  "Poincare.D7.Compactness.ToyCompactness".toName,
  "Poincare.D7.ConjugateHeat.All".toName,
  "Poincare.D7.ConjugateHeat.Audit".toName,
  "Poincare.D7.ConjugateHeat.Basic".toName,
  "Poincare.D7.ConjugateHeat.Blocked".toName,
  "Poincare.D7.ConjugateHeat.Example".toName,
  "Poincare.D7.ConjugateHeat.Instance".toName,
  "Poincare.D7.ConjugateHeat.Laplacian".toName,
  "Poincare.D7.ConjugateHeat.Probe".toName,
  "Poincare.D7.ConjugateHeat.Slab".toName,
  "Poincare.D7.ConjugateHeat.Status".toName,
  "Poincare.D7.ConjugateHeat.UniquenessStatus".toName,
  "Poincare.D7.Curvature".toName,
  "Poincare.D7.Curvature.Audit".toName,
  "Poincare.D7.Curvature.Basic".toName,
  "Poincare.D7.Curvature.Blocked".toName,
  "Poincare.D7.Curvature.Bridge".toName,
  "Poincare.D7.Curvature.Example".toName,
  "Poincare.D7.Curvature.Probe".toName,
  "Poincare.D7.Curvature.Sectional".toName,
  "Poincare.D7.Curvature.Symmetries".toName,
  "Poincare.D7.Divergence".toName,
  "Poincare.D7.Divergence.Audit".toName,
  "Poincare.D7.Divergence.Basic".toName,
  "Poincare.D7.Divergence.Blocked".toName,
  "Poincare.D7.Divergence.Example".toName,
  "Poincare.D7.Divergence.Graph".toName,
  "Poincare.D7.Divergence.Probe".toName,
  "Poincare.D7.Divergence.Slab".toName,
  "Poincare.D7.EvolutionSharp.AxiomAudit".toName,
  "Poincare.D7.EvolutionSharp.Certificates".toName,
  "Poincare.D7.EvolutionSharp.FunctionalSharp".toName,
  "Poincare.D7.EvolutionSharp.GibbsSharp".toName,
  "Poincare.D7.EvolutionSharp.Implications".toName,
  "Poincare.D7.EvolutionSharp.ReleaseAudit".toName,
  "Poincare.D7.EvolutionSharp.Witnesses".toName,
  "Poincare.D7.Geodesic.AxiomAudit".toName,
  "Poincare.D7.Geodesic.Basic".toName,
  "Poincare.D7.Geodesic.FlatUniqueness".toName,
  "Poincare.D7.Geodesic.ManifoldInterfaces".toName,
  "Poincare.D7.Geodesic.MathlibProbe".toName,
  "Poincare.D7.Geodesic.MetricSpeed".toName,
  "Poincare.D7.Geodesic.Reparam".toName,
  "Poincare.D7.Geodesic.Smoke".toName,
  "Poincare.D7.HeatKernel.All".toName,
  "Poincare.D7.HeatKernel.Audit".toName,
  "Poincare.D7.HeatKernel.Basic".toName,
  "Poincare.D7.HeatKernel.Blocked".toName,
  "Poincare.D7.HeatKernel.Content".toName,
  "Poincare.D7.HeatKernel.DataStatus".toName,
  "Poincare.D7.HeatKernel.Example".toName,
  "Poincare.D7.HeatKernel.FiniteStatus".toName,
  "Poincare.D7.HeatKernel.Grid".toName,
  "Poincare.D7.HeatKernel.Instance".toName,
  "Poincare.D7.HeatKernel.Probe".toName,
  "Poincare.D7.HeatKernel.RepairStatus".toName,
  "Poincare.D7.HeatKernel.StatementStatus".toName,
  "Poincare.D7.HeatKernel.UniquenessStatus".toName,
  "Poincare.D7.HeatKernel.V1Interface".toName,
  "Poincare.D7.Kappa.All".toName,
  "Poincare.D7.Kappa.Audit".toName,
  "Poincare.D7.Kappa.Basic".toName,
  "Poincare.D7.Kappa.EntropyBridge".toName,
  "Poincare.D7.Kappa.Nonvacuity".toName,
  "Poincare.D7.Kappa.Probe".toName,
  "Poincare.D7.Kappa.Statements".toName,
  "Poincare.D7.LeviCivita.Audit".toName,
  "Poincare.D7.LeviCivita.Basic".toName,
  "Poincare.D7.LeviCivita.Blocked".toName,
  "Poincare.D7.LeviCivita.Coefficients".toName,
  "Poincare.D7.LeviCivita.Koszul".toName,
  "Poincare.D7.LeviCivita.Probe".toName,
  "Poincare.D7.LeviCivita.Smoke".toName,
  "Poincare.D7.Limit.All".toName,
  "Poincare.D7.Limit.Audit".toName,
  "Poincare.D7.Limit.Basic".toName,
  "Poincare.D7.Limit.Blocked".toName,
  "Poincare.D7.Limit.Convergence".toName,
  "Poincare.D7.Limit.ErrorRecursion".toName,
  "Poincare.D7.Limit.Example".toName,
  "Poincare.D7.Limit.Probe".toName,
  "Poincare.D7.Limit.Refinement".toName,
  "Poincare.D7.Limit.Stability".toName,
  "Poincare.D7.Monotonicity.All".toName,
  "Poincare.D7.Monotonicity.Blockers".toName,
  "Poincare.D7.Monotonicity.BochnerCertificate".toName,
  "Poincare.D7.Monotonicity.BochnerGradientEstimate".toName,
  "Poincare.D7.Monotonicity.ConjugateHeatCertificate".toName,
  "Poincare.D7.Monotonicity.FMonotonicity".toName,
  "Poincare.D7.Monotonicity.Nonvacuity".toName,
  "Poincare.D7.Monotonicity.ReducedVolumeInput".toName,
  "Poincare.D7.Monotonicity.WMuMonotonicity".toName,
  "Poincare.D7.Recognition.All".toName,
  "Poincare.D7.Recognition.Assembly".toName,
  "Poincare.D7.Recognition.Audit".toName,
  "Poincare.D7.Recognition.Basic".toName,
  "Poincare.D7.Recognition.Homeomorphism".toName,
  "Poincare.D7.Recognition.Probe".toName,
  "Poincare.D7.Reduced.All".toName,
  "Poincare.D7.Reduced.Audit".toName,
  "Poincare.D7.Reduced.Basic".toName,
  "Poincare.D7.Reduced.Certificate".toName,
  "Poincare.D7.Reduced.Gaussian".toName,
  "Poincare.D7.Reduced.Probe".toName,
  "Poincare.D7.Reduced.Statements".toName,
  "Poincare.D7.RicciScalar".toName,
  "Poincare.D7.RicciScalar.Audit".toName,
  "Poincare.D7.RicciScalar.Basic".toName,
  "Poincare.D7.RicciScalar.Bridge".toName,
  "Poincare.D7.RicciScalar.Example".toName,
  "Poincare.D7.RicciScalar.Probe".toName,
  "Poincare.D7.RicciScalar.Product".toName,
  "Poincare.D7.RicciScalar.Scalar".toName,
  "Poincare.D7.RicciScalar.Variation".toName,
  "Poincare.D7.ShortTime".toName,
  "Poincare.D7.ShortTime.Audit".toName,
  "Poincare.D7.ShortTime.Basic".toName,
  "Poincare.D7.ShortTime.Equivalence".toName,
  "Poincare.D7.ShortTime.Example".toName,
  "Poincare.D7.ShortTime.Gauge".toName,
  "Poincare.D7.ShortTime.MatrixDeriv".toName,
  "Poincare.D7.ShortTime.ODE".toName,
  "Poincare.D7.ShortTime.Probe".toName,
  "Poincare.D7.ShortTime.Statements".toName,
  "Poincare.D7.SurgeryFlow.All".toName,
  "Poincare.D7.SurgeryFlow.Audit".toName,
  "Poincare.D7.SurgeryFlow.Basic".toName,
  "Poincare.D7.SurgeryFlow.Extinction".toName,
  "Poincare.D7.SurgeryFlow.Probe".toName,
  "Poincare.D7.SurgeryFlow.Statements".toName,
  "Poincare.D7.SurgeryFlow.Times".toName,
  "Poincare.D7.TensorLaplacian".toName,
  "Poincare.D7.TensorLaplacian.Audit".toName,
  "Poincare.D7.TensorLaplacian.Basic".toName,
  "Poincare.D7.TensorLaplacian.Blocked".toName,
  "Poincare.D7.TensorLaplacian.Commutation".toName,
  "Poincare.D7.TensorLaplacian.Evolution".toName,
  "Poincare.D7.TensorLaplacian.Example".toName,
  "Poincare.D7.TensorLaplacian.Probe".toName,
  "Poincare.D7.Volume".toName,
  "Poincare.D7.Volume.Audit".toName,
  "Poincare.D7.Volume.Basic".toName,
  "Poincare.D7.Volume.Blocked".toName,
  "Poincare.D7.Volume.ChangeOfVariables".toName,
  "Poincare.D7.Volume.Example".toName,
  "Poincare.D7.Volume.Probe".toName,
  "Poincare.D7.Volume.Scaling".toName,
  "Poincare.D8.Fidelity.AxiomAudit".toName,
  "Poincare.D8.Fidelity.Bridge".toName,
  "Poincare.D8.Fidelity.FidelityCard".toName,
  "Poincare.D8.Fidelity.MoiseData".toName,
  "Poincare.D8.Fidelity.MoiseStatement".toName,
  "Poincare.D8.Fidelity.SmoothStructure".toName,
  "Poincare.D9.AncientKappa.Basic".toName,
  "Poincare.D9.AncientKappa.Classification".toName,
  "Poincare.D9.AncientKappa.GaussianSoliton".toName,
  "Poincare.D9.AncientKappa.PrintAxioms".toName,
  "Poincare.D9.CheegerGromov.AxiomAudit".toName,
  "Poincare.D9.CheegerGromov.CheegerGromov".toName,
  "Poincare.D9.CheegerGromov.DiscreteModel".toName,
  "Poincare.D9.CheegerGromov.PointedConvergence".toName,
  "Poincare.D9.DeTurck.ConnectionLayer".toName,
  "Poincare.D9.DeTurck.StatementOnly".toName,
  "Poincare.D9.DeTurck.SymbolModel".toName,
  "Poincare.D9.ParabolicEstimates.AxiomAudit".toName,
  "Poincare.D9.ParabolicEstimates.Basic".toName,
  "Poincare.D9.ParabolicEstimates.Gronwall".toName,
  "Poincare.D9.ParabolicEstimates.MatrixModel".toName,
  "Poincare.D9.ParabolicEstimates.Statements".toName,
  "Poincare.D9.Surfaces.All".toName,
  "Poincare.D9.Surfaces.AxiomAudit".toName,
  "Poincare.D9.Surfaces.Basic".toName,
  "Poincare.D9.Surfaces.HomogeneousODE".toName,
  "Poincare.D9.Surfaces.Statements".toName,
  "Poincare.D9.TensorAlgebra.AxiomAudit".toName,
  "Poincare.D9.TensorAlgebra.Interface".toName,
  "Poincare.D9.TensorAlgebra.Props".toName,
  "Poincare.D9.TensorAlgebra.Toy".toName]

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo v => match v.safety with
      | .«unsafe» => "unsafe_def"
      | .«partial» => "partial_def"
      | .safe => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _ => "ctor"
  | .recInfo _ => "rec"

end SEMREV_D13_heatkernel_bridge_d10_d7

open SEMREV_D13_heatkernel_bridge_d10_d7 in
run_cmd do
  let env ← getEnv
  let mods := env.header.moduleNames
  let auditedSet : Std.HashSet Name :=
    auditedModules.foldl (fun acc m => acc.insert m) ∅
  let rows := env.constants.fold (fun acc n ci =>
    match env.getModuleIdxFor? n with
    | some midx =>
        let m := mods.getD midx .anonymous
        if auditedSet.contains m && !negativeControlModules.contains m then acc.push (n, ci, m)
        else acc
    | none => acc) #[]
  let mut nAxiom := 0
  let mut nUnsafe := 0
  let mut nSorry := 0
  let mut nNative := 0
  let mut nOther := 0
  let mut nFail := 0
  let mut nPartial := 0
  let mut nThm := 0
  let mut nOpaque := 0
  let mut nProofWanted := 0
  for (n, ci, m) in rows do
    if n.toString.contains "proof_wanted" then nProofWanted := nProofWanted + 1
    match ci with
    | .axiomInfo _ => nAxiom := nAxiom + 1
    | .opaqueInfo _ => nOpaque := nOpaque + 1
    | .defnInfo v =>
        match v.safety with
        | .«unsafe» => nUnsafe := nUnsafe + 1
        | .«partial» => nPartial := nPartial + 1
        | .safe => pure ()
    | .thmInfo _ => nThm := nThm + 1
    | _ => pure ()
    let axs ←
      try Lean.collectAxioms n
      catch _ => nFail := nFail + 1; pure #[]
    for a in axs do
      if a == ``sorryAx then nSorry := nSorry + 1
      else if a == ``ofReduceBool || a.toString.contains "native_decide" then nNative := nNative + 1
      else if !approvedAxioms.contains a then nOther := nOther + 1
    IO.println s!"XDECL\t{n}\t{kindOf ci}\t{m}\t{";".intercalate (axs.toList.map Name.toString)}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tdeclarations\t{rows.size}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\ttheorems\t{nThm}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tpartial_defs\t{nPartial}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\topaque\t{nOpaque}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tproject_axioms\t{nAxiom}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tunsafe\t{nUnsafe}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tsorry_cones\t{nSorry}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tnative_decide_cones\t{nNative}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tunapproved_axiom_cones\t{nOther}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tcollect_failures\t{nFail}"
  IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tproof_wanted\t{nProofWanted}"
  if nAxiom + nUnsafe + nSorry + nNative + nOther + nFail + nProofWanted > 0 then
    IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tVERDICT\tFAIL"
    throwError "SEMREV: forbidden dependency found (D13-heatkernel-bridge-d10-d7)"
  else
    IO.println s!"XAUDIT\tD13-heatkernel-bridge-d10-d7\tVERDICT\tPASS"
