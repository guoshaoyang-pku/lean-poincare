import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Topology.MetricSpace.GromovHausdorffRealized
import Mathlib.MeasureTheory.Measure.Doubling
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.CoveringExponent
import Mathlib.MeasureTheory.Covering.VitaliFamily
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.BoxIntegral.DivergenceTheorem
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric
import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique

/-! ## Q2 Gromov-Hausdorff -/
#check @GromovHausdorff.GHSpace
#check @GromovHausdorff.toGHSpace
#check @GromovHausdorff.GHSpace.Rep
#check @GromovHausdorff.ghDist
#check @GromovHausdorff.dist_ghDist
#check @GromovHausdorff.ghDist_le_hausdorffDist
#check @GromovHausdorff.ghDist_eq_hausdorffDist
#check @GromovHausdorff.ghDist_le_of_approx_subsets
#check @GromovHausdorff.totallyBounded
#check @GromovHausdorff.ghDist_le_nonemptyCompacts_dist
#check @GromovHausdorff.toGHSpace_lipschitz
#check @GromovHausdorff.toGHSpace_continuous
#check @GromovHausdorff.instCompleteSpaceGHSpace
#check @GromovHausdorff.instSecondCountableTopologyGHSpace
#check @GromovHausdorff.instMetricSpaceGHSpace
#check @GromovHausdorffRealized.HD
#check @GromovHausdorffRealized.premetricOptimalGHDist
#check @GromovHausdorffRealized.OptimalGHCoupling
#check @GromovHausdorffRealized.isometry_optimalGHInjl
#check @GromovHausdorffRealized.isometry_optimalGHInjr
#check @GromovHausdorffRealized.hausdorffDist_optimal_le_HD
#check @GromovHausdorffRealized.compactSpace_optimalGHCoupling

/-! ## Q3 doubling / covering -/
#print IsUnifLocDoublingMeasure
#check @IsUnifLocDoublingMeasure.doublingConstant
#check @IsUnifLocDoublingMeasure.eventually_measure_le_doublingConstant_mul
#check @IsUnifLocDoublingMeasure.scalingConstantOf
#check @IsUnifLocDoublingMeasure.measure_mul_le_scalingConstantOf_mul
#check @IsUnifLocDoublingMeasure.eventually_measure_le_scaling_constant_mul
#check @Metric.coveringNumber
#check @Metric.externalCoveringNumber
#check @Metric.packingNumber
#print Metric.HasCoveringExponent
#check @Metric.HasCoveringExponent.coveringNumber_lt_top
#check @Metric.coveringNumber_two_mul_le_externalCoveringNumber
#check @Metric.coveringNumber_le_packingNumber
#check @Metric.packingNumber_two_mul_le_externalCoveringNumber
#check @Metric.minimalCover
#check @Metric.maximalSeparatedSet
#check @MeasureTheory.VitaliFamily
#check @MeasureTheory.VitaliFamily.FineSubfamilyOn.exists_disjoint_covering_ae
#check @MeasureTheory.VitaliFamily.FineSubfamilyOn.measure_le_tsum

/-! ## Q5 volume form / orientation / integration -/
#check @Orientation
#check @Orientation.volumeForm
#check @Orientation.measure_eq_volume
#check @Orientation.measure_orthonormalBasis
#check @OrthonormalBasis.addHaar_eq_volume
#check @MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
#check @BoxIntegral.hasIntegral_GP_divergence_of_forall_hasDerivWithinAt

/-! ## Q1 Riemannian manifold API -/
#check @IsRiemannianManifold
#check @riemannianMetricVectorSpace
#check @Manifold.riemannianEDist
#check @Manifold.pathELength
#check @Manifold.riemannianEDist_le_pathELength
#check @EMetricSpace.ofRiemannianMetric
#check @PseudoEMetricSpace.ofRiemannianMetric
#check @CovariantDerivative.IsLeviCivitaConnection
#check @CovariantDerivative.leviCivitaConnection
#check @CovariantDerivative.IsMetricCompatible
#check @IsMIntegralCurve
#check @IsMIntegralCurveAt
#check @IsMIntegralCurveAt_of_contMDiffAt
#check @mfderiv
#check @VectorField
#check @mlieBracket

/-! ## Q6 ODE comparison -/
#check @IsPicardLindelof
#check @IsPicardLindelof.exists_eq_forall_mem_Icc_eq_picard
#check @ODE_solution_unique
#check @ODE_solution_unique_of_mem_Icc
