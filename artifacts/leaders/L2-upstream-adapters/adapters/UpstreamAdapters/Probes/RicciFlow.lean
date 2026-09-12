import MorganTianLib
import Topping
import Topping.MaximumPrinciple.Riemannian
import Topping.MaximumPrinciple.CanonicalVolumeEvolution
import Topping.Riemannian.CovariantTensor
import Topping.Riemannian.VariationScalar
import Topping.ParabolicPDE.LaplaceBeltrami
import KleinerLott
import KleinerLott.RicciFlow.Noncollapsing
import KleinerLott.RicciFlow.Pinching
import KleinerLott.RicciFlow.PointSelection

/-!
# Compile-time API probes: Ricci flow and Perelman machinery (U2, U6-U10, U12)

`MorganTianLib` (Morgan-Tian, *Ricci Flow and the Poincaré Conjecture*),
`Topping` (*Lectures on the Ricci Flow*) and `KleinerLott` (Perelman's papers /
geometrization) carry the Ricci-flow layer of the snapshot.

The probes record named declarations for: Ricci/scalar curvature at a point
(U2), Hamilton tensor maximum principles (U6), divergence/volume/Bochner
identities (U7, U10), the Ricci-flow equation predicate (U8), κ-noncollapsing
and point selection (U9), and the smooth-complete-flow interface.

Note: `IsRicciFlowOn` is a *structure of hypotheses* (an explicit interface);
declarations named `..._of_isRicciFlowOn` are conditional on it.  The probes
only assert the names exist; semantic classification is recorded in
`evidence/claim-classification.json` and the result card.

The upstream root modules `Topping.lean` and `KleinerLott.lean` import only a
subset of their own files, so the relevant modules are imported explicitly.
-/

namespace UpstreamAdapters.Probes.RicciFlow

-- U2: Ricci form, Ricci tensor at a point, scalar curvature
#check @MorganTianLib.ricciForm
#check @MorganTianLib.ricciAt
#check @MorganTianLib.scalarCurvature
#check @MorganTianLib.scalarCurvatureAt
#check @MorganTianLib.chartScalarCurvatureOnE_eq_scalarCurvatureAt
#check @MorganTianLib.sum_metricInner_riemannCurvature_frame_eq_ricciAt
#check @MorganTianLib.trace_frameCurvOp_eq_ricciAt
#check @MorganTianLib.ricci_curvature_comparison

-- U6: Hamilton tensor maximum principles (continuous parabolic layer)
#check @MorganTianLib.hamilton_tensor_maximum_principle_compact
#check @MorganTianLib.hamilton_tensor_maximum_principle_bounded
#check @MorganTianLib.hamilton_tensor_maximum_principle_compact_support
#check @MorganTianLib.hamilton_tensor_maximum_principle_of_parallel_frame
#check @Topping.weak_maximum_principle
#check @Topping.weak_maximum_principle_of_pos

-- U7/U10: divergence, Laplacian, volume density, Bochner formula
#check @MorganTianLib.laplacianAt_eq_chart_divergence
#check @MorganTianLib.chartVolumeDensity_mul_laplacianAt_eq_divergence
#check @MorganTianLib.function_bochner_formula
#check @Topping.divergence
#check @Topping.divergence_apply
#check @Topping.divergence_ricciTensorField
#check @Topping.ParabolicPDE.metricLaplacianAt_eq_laplaceBeltramiChart_divergence

-- U8: the Ricci-flow equation and curvature evolution under it
#check @MorganTianLib.IsRicciFlowEquationOn
#check @MorganTianLib.IsRicciFlowOn
#check @MorganTianLib.IsRicciFlowOn.metricInner_hasDerivAt
#check @MorganTianLib.IsRicciFlowOn.inner_hasDerivWithinAt
#check @MorganTianLib.ricciFlowRiemannVariationIntrinsic_eq_curvature_evolution_explicit
#check @MorganTianLib.hasDerivAt_chartRiemannEnergyOnE_of_isRicciFlowOn
#check @MorganTianLib.ricciFlowFrameCurvatureEnergy_nonneg
#check @Topping.hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn
#check @Topping.riemannianVolume_antitoneOn_of_isRicciFlowOn

-- U9/U12: Perelman-era machinery available in the snapshot
#check @KleinerLott.IsKappaNoncollapsedOnScale
#check @KleinerLott.SmoothCompleteRicciFlowOn
#check @KleinerLott.RiemannCurvatureFamily.ricciAt
#check @KleinerLott.IsHamiltonIveyPinched
#check @KleinerLott.exists_point_selection_of_bounded_moving_curvature

end UpstreamAdapters.Probes.RicciFlow
