import Poincare.D9.CheegerGromov.PointedConvergence
import Poincare.D9.CheegerGromov.DiscreteModel
import Poincare.D9.CheegerGromov.CheegerGromov

/-!
# Poincare.D9.CheegerGromov.AxiomAudit

**D9 / Cheeger–Gromov compactness: the kernel axiom audit.**

Every declaration authored by the D9 task is printed with `#print axioms`, so the compiled output of
this file is the per-declaration axiom cone required by the task card.  The expected cones are
subsets of `{propext, Classical.choice, Quot.sound}`; the state-only Props are plain `Prop`-valued
definitions and should not depend on any axioms.

Compile with `lake env lean Poincare/D9/CheegerGromov/AxiomAudit.lean` (exit 0) and capture stdout.
-/

namespace Poincare
namespace D9
namespace CheegerGromov

/-! ## Pointed convergence interface (`PointedConvergence.lean`) -/

#print axioms PointedManifold
#print axioms PointedManifold.metricBall
#print axioms PointedManifold.basepoint_mem_metricBall
#print axioms PointedManifold.metricBall_mono
#print axioms PointedManifold.HasCompactMetricBalls
#print axioms PointedManifold.IsCompleteMetric
#print axioms CompactExhaustion
#print axioms CompactExhaustion.subset_succ
#print axioms CompactExhaustion.subset_of_le
#print axioms CompactExhaustion.exists_subset
#print axioms pullbackMetric
#print axioms pullbackMetric_id
#print axioms PointedManifold.metricDiffCoeff
#print axioms PointedManifold.metricDiffCoeff_id
#print axioms PointedManifold.CkCloseOnChart
#print axioms PointedManifold.CkCloseOnChart.mono
#print axioms PointedManifold.CkCloseOnChart.mono_order
#print axioms PointedManifold.CkCloseOnChart.mono_set
#print axioms CkCloseAtScale
#print axioms CkCloseAtScale.mono
#print axioms CkCloseAtScale.mono_scale
#print axioms CkCloseAtScale.mono_order
#print axioms CkCloseAtScaleProp
#print axioms ckCloseAtScale_self
#print axioms ckCloseAtScaleProp_self
#print axioms CkConvergesTo
#print axioms CkConvergesToNat
#print axioms CkConvergesTo.toNat
#print axioms CkConvergesToNat.toReal
#print axioms ckConvergesTo_nat_iff
#print axioms ckConvergesTo_const
#print axioms CkConvergence
#print axioms CkConvergence.convergesTo

/-! ## Discrete model (`DiscreteModel.lean`) -/

#print axioms exists_strictMono_const_of_finite
#print axioms RawFiniteDatum
#print axioms IsBoundedFiniteMetric
#print axioms DiscreteMetricDatum
#print axioms DiscreteMetricDatum.finite_of_bounded
#print axioms DiscreteMetricDatum.dist
#print axioms DiscreteMetricDatum.base
#print axioms DiscreteMetricDatum.dist_self
#print axioms DiscreteMetricDatum.dist_comm
#print axioms DiscreteMetricDatum.dist_triangle
#print axioms DiscreteMetricDatum.dist_le_upper
#print axioms DiscreteMetricDatum.le_dist_of_ne
#print axioms DiscreteMetricDatum.dist_pos_of_ne
#print axioms DiscreteMetricDatum.relabellingSet
#print axioms DiscreteMetricDatum.pointedDist
#print axioms DiscreteMetricDatum.dist_nonneg
#print axioms DiscreteMetricDatum.relabellingSet_nonempty
#print axioms DiscreteMetricDatum.relabellingSet_bddBelow
#print axioms DiscreteMetricDatum.pointedDist_nonneg
#print axioms DiscreteMetricDatum.pointedDist_self
#print axioms DiscreteMetricDatum.relabellingSet_comm
#print axioms DiscreteMetricDatum.pointedDist_comm
#print axioms DiscreteMetricDatum.relabellingSet_add
#print axioms DiscreteMetricDatum.pointedDist_triangle
#print axioms DiscreteMetricDatum.exists_convergent_subsequence
#print axioms DiscreteMetricDatum.discrete_cheegerGromov
#print axioms DiscreteMetricDatum.exists_finset_net_pointedDist
#print axioms DiscreteCheegerGromovCompactness
#print axioms discreteCheegerGromovCompactness_holds
#print axioms exists_finset_net
#print axioms exists_grid_approximation

/-! ## State-only Props and interface lemmas (`CheegerGromov.lean`) -/

#print axioms CurvatureNormBound
#print axioms curvatureNormBound_zero
#print axioms PointedManifoldWithRadius
#print axioms InjectivityRadiusAtLeast
#print axioms UniformCurvatureBounds
#print axioms uniformCurvatureBounds_zero
#print axioms uniformCurvatureBounds_implies_curvatureNormBound
#print axioms ckConvergesTo_mono_order
#print axioms CheegerGromovCompactness
#print axioms CheegerGromovCompactnessSmooth
#print axioms InjectivityRadiusLowerBoundPassesToLimit
#print axioms ckConvergesTo_all_implies_one
#print axioms discrete_analogue_is_proved

end CheegerGromov
end D9
end Poincare
