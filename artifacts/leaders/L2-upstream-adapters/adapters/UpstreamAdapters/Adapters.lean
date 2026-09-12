import DoCarmoLib
import MorganTianLib
import Topping
import Topping.MaximumPrinciple.Riemannian
import Topping.MaximumPrinciple.CanonicalVolumeEvolution
import Topping.Riemannian.CovariantTensor
import Topping.Riemannian.VariationScalar
import Topping.Riemannian.ContractedBianchi
import Topping.ParabolicPDE.LaplaceBeltrami
import KleinerLott
import KleinerLott.RicciFlow.Noncollapsing
import KleinerLott.RicciFlow.Pinching
import KleinerLott.RicciFlow.PointSelection
import HatcherLib

/-!
# Adapter aliases for audited upstream declarations

`alias` creates a new declaration with the *same type and the same proof term*
as the upstream declaration: it is a renaming, not a restatement, so it cannot
silently weaken or strengthen the upstream statement.  Downstream consumers get
a stable, locally owned name while the upstream pin stays authoritative.

The axiom cone of every alias is exactly the axiom cone of the upstream
declaration; `UpstreamAdapters.Audit` prints those cones and fails closed if
anything outside `{propext, Classical.choice, Quot.sound}` appears (in
particular `sorryAx`, which would indicate an admitted upstream proof).

Names are grouped by the source project, not by local blocker, so the
provenance of every name stays visible.  `PetersenLib` aliases live in the
separate `UpstreamAdaptersPetersen` library because PetersenLib and Shared
cannot share one Lean environment (duplicate `metric_simp` attribute).

Note on imports: the upstream root modules (`Topping.lean`,
`KleinerLott.lean`) only import a subset of their own files, so the specific
modules are imported explicitly here.
-/

namespace UpstreamAdapters.Adapters

namespace DoCarmo

-- U4: Levi-Civita connection
alias leviCivita_chartContraction_eq :=
  Riemannian.RiemannianMetric.leviCivita_chartContraction_eq
alias leviCivita_covDerivAlong_eq :=
  Riemannian.RiemannianMetric.leviCivita_covDerivAlong_eq
alias preservesMetricUnderParallelTransport_iff_isMetricCompatible :=
  Riemannian.AffineConnection.preservesMetricUnderParallelTransport_iff_isMetricCompatible

-- U1: curvature operator and curvature form
alias curvature_zero_left := Riemannian.AffineConnection.curvature_zero_left
alias curvature_zero_right := Riemannian.AffineConnection.curvature_zero_right
alias curvature_apply_congr := Riemannian.AffineConnection.curvature_apply_congr
alias curvatureOperatorAt_add_left :=
  Riemannian.AffineConnection.curvatureOperatorAt_add_left
alias curvatureOperatorAt_smul_left :=
  Riemannian.AffineConnection.curvatureOperatorAt_smul_left
alias leviCivita_curvature_frame_expansion :=
  Riemannian.leviCivita_curvature_frame_expansion
alias leviCivita_curvature_chartFrame_expansion :=
  Riemannian.leviCivita_curvature_chartFrame_expansion

-- U2: sectional and Ricci curvature
alias sectionalCurvature_eq_of_orthonormal := Riemannian.sectionalCurvature_eq_of_orthonormal
alias ricciForm_self_eq_sum_sectionalCurvature :=
  Riemannian.ricciForm_self_eq_sum_sectionalCurvature
alias hasRicciLowerBound_of_sectionalCurvatureLowerBound :=
  Riemannian.Variation.hasRicciLowerBound_of_sectionalCurvatureLowerBound
-- Round 5: the remaining U2 entry points inventoried in the API map.
alias ricciForm := Riemannian.ricciForm
alias scalarCurvature := Riemannian.scalarCurvature
alias sectionalCurvature := Riemannian.sectionalCurvature
alias ricciForm_symm := Riemannian.ricciForm_symm

-- U3: geodesics and parallel transport
alias isGeodesic_iff_covDerivAlong_velocity_eq_zero :=
  Riemannian.Geodesic.isGeodesic_iff_covDerivAlong_velocity_eq_zero
alias continuous_and_isGeodesic_iff_leviCivita_covDerivAlong_velocity_eq_zero :=
  Riemannian.Geodesic.continuous_and_isGeodesic_iff_leviCivita_covDerivAlong_velocity_eq_zero
alias hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero :=
  Riemannian.Geodesic.hasGeodesicEquationAt_iff_covDerivAlong_velocity_eq_zero
alias metricInner_parallelTransportTangentEquiv :=
  Riemannian.metricInner_parallelTransportTangentEquiv
-- Round 5: the predicate and the transport equivalence themselves.
alias IsGeodesic := Riemannian.Geodesic.IsGeodesic
alias HasGeodesicEquationAt := Riemannian.Geodesic.HasGeodesicEquationAt
alias parallelTransportTangentEquiv := Riemannian.parallelTransportTangentEquiv

end DoCarmo

namespace MorganTian

-- U1: pointwise curvature (0,4)-form symmetries
-- (`MorganTianLib` Ch01 PointwiseCurvature.lean already states these at the
-- pointwise level; the operator-level versions are the new consumers in
-- `UpstreamAdapters.DownstreamGeometry`.)
alias curvatureFormAt_antisymm_left := MorganTianLib.curvatureFormAt_antisymm_left
alias curvatureFormAt_antisymm_right := MorganTianLib.curvatureFormAt_antisymm_right
alias curvatureFormAt_bianchi := MorganTianLib.curvatureFormAt_bianchi
alias isAlgCurvatureForm_curvatureFormAt :=
  MorganTianLib.isAlgCurvatureForm_curvatureFormAt

-- U2: pointwise Ricci and scalar curvature
alias ricciAt := MorganTianLib.ricciAt
alias scalarCurvatureAt := MorganTianLib.scalarCurvatureAt
alias sum_metricInner_riemannCurvature_frame_eq_ricciAt :=
  MorganTianLib.sum_metricInner_riemannCurvature_frame_eq_ricciAt
alias trace_frameCurvOp_eq_ricciAt := MorganTianLib.trace_frameCurvOp_eq_ricciAt

-- U6: Hamilton tensor maximum principles
alias hamilton_tensor_maximum_principle_compact :=
  MorganTianLib.hamilton_tensor_maximum_principle_compact
alias hamilton_tensor_maximum_principle_bounded :=
  MorganTianLib.hamilton_tensor_maximum_principle_bounded
-- Round 5: the parallel-frame variant and the pointwise Ricci/scalar surface.
alias hamilton_tensor_maximum_principle_of_parallel_frame :=
  MorganTianLib.hamilton_tensor_maximum_principle_of_parallel_frame
alias ricciForm := MorganTianLib.ricciForm
alias scalarCurvature := MorganTianLib.scalarCurvature
alias ricci_curvature_comparison := MorganTianLib.ricci_curvature_comparison

-- U7/U10: divergence and Bochner identities
alias laplacianAt_eq_chart_divergence := MorganTianLib.laplacianAt_eq_chart_divergence
alias chartVolumeDensity_mul_laplacianAt_eq_divergence :=
  MorganTianLib.chartVolumeDensity_mul_laplacianAt_eq_divergence
alias function_bochner_formula := MorganTianLib.function_bochner_formula

-- U8: Ricci-flow equation (hypothesis structure)
alias IsRicciFlowEquationOn := MorganTianLib.IsRicciFlowEquationOn
alias IsRicciFlowOn := MorganTianLib.IsRicciFlowOn
alias IsRicciFlowOn.metricInner_hasDerivAt := MorganTianLib.IsRicciFlowOn.metricInner_hasDerivAt
alias IsRicciFlowOn.inner_hasDerivWithinAt := MorganTianLib.IsRicciFlowOn.inner_hasDerivWithinAt

end MorganTian

namespace Topping

alias weak_maximum_principle := Topping.weak_maximum_principle
alias weak_maximum_principle_of_pos := Topping.weak_maximum_principle_of_pos
alias divergence_ricciTensorField := Topping.divergence_ricciTensorField
alias hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn :=
  Topping.hasVolumeDerivativeOn_riemannianMeasure_of_isRicciFlowOn
alias riemannianVolume_antitoneOn_of_isRicciFlowOn :=
  Topping.riemannianVolume_antitoneOn_of_isRicciFlowOn
-- Round 5: the U7 divergence family and the Laplace-Beltrami identity.
alias divergence := Topping.divergence
alias divergence_apply := Topping.divergence_apply
alias divergence_differentialOneForm := Topping.divergence_differentialOneForm
alias divergence_covTensorOfBilin_neg_two_ricci :=
  Topping.divergence_covTensorOfBilin_neg_two_ricci
alias divergence_gravitationTensor_ricciTensorField :=
  Topping.divergence_gravitationTensor_ricciTensorField
alias metricLaplacianAt_eq_laplaceBeltramiChart_divergence :=
  Topping.ParabolicPDE.metricLaplacianAt_eq_laplaceBeltramiChart_divergence

end Topping

namespace KleinerLott

alias IsKappaNoncollapsedOnScale := KleinerLott.IsKappaNoncollapsedOnScale
alias IsHamiltonIveyPinched := KleinerLott.IsHamiltonIveyPinched
alias exists_point_selection_of_bounded_moving_curvature :=
  KleinerLott.exists_point_selection_of_bounded_moving_curvature
alias exists_point_of_bounded_curvature := KleinerLott.exists_point_of_bounded_curvature
-- Round 5: the U9 flow interfaces themselves.
alias SmoothCompleteRicciFlowOn := KleinerLott.SmoothCompleteRicciFlowOn
alias RicciFlowData := KleinerLott.RicciFlowData

end KleinerLott

namespace Hatcher

alias simplyConnected_iff_unique_path_class := HatcherLib.simplyConnected_iff_unique_path_class
alias IsUniversalCoveringMap.simplyConnectedSpace :=
  HatcherLib.IsUniversalCoveringMap.simplyConnectedSpace
alias attachingSpace_homotopyEquiv := HatcherLib.attachingSpace_homotopyEquiv
alias homotopyEquivPiOneMulEquiv := HatcherLib.homotopyEquivPiOneMulEquiv
alias collapseMk_homotopyEquiv := HatcherLib.collapseMk_homotopyEquiv
alias simplyConnectedSpace_of_pathConnectedOpenCover :=
  HatcherLib.simplyConnectedSpace_of_pathConnectedOpenCover
-- Round 5: the universal-cover construction (M4).
alias universalCover_simplyConnectedSpace :=
  HatcherLib.UniversalCoverConstruction.universalCover_simplyConnectedSpace

end Hatcher

end UpstreamAdapters.Adapters
