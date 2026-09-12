import PetersenLib
import PetersenLib.Ch03.EuclideanCurvature
import UpstreamAdaptersPetersen.Adapters

/-!
# Constructed-input consumers for the Petersen curvature and exponential APIs

The companion of `UpstreamAdapters.DownstreamGeometry` in the Petersen family
(which cannot share a Lean environment with `Shared`/`DoCarmoLib` because both
call `register_simp_attr metric_simp`).  The constructed input is the concrete
Euclidean space `EuclideanSpace ℝ (Fin 2)` with the canonical flat metric.

* `euclidean_curvatureTensorAt_eq_zero` — the **pointwise** curvature tensor of
  the Levi-Civita connection of the canonical flat metric vanishes.  Upstream
  `euclideanSpace_curvature_eq_zero` states the field-level identity; the
  pointwise form is obtained through the upstream well-definedness bridge
  `curvatureTensorAt_apply`.
* `euclidean_expMap_zero` — the exponential map of the constructed Euclidean
  metric sends `0` to the base point.
* `euclidean_expMap_zero_smul` — the same at a scaled zero velocity, exercising
  the ray form of the exponential API on constructed input.

Semantic class: `proved` (unconditional consequences about the concrete flat
Euclidean model).
-/

namespace UpstreamAdaptersPetersen.DownstreamUse

open scoped Manifold ContDiff

noncomputable section

/-- Constructed input manifold: the Euclidean plane as a vector-space model. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- **Math.** **U1 constructed-input consumer (Petersen family).** The
pointwise curvature tensor of the Levi-Civita connection of the canonical flat
metric on the Euclidean plane vanishes at every point and every triple of
tangent vectors. -/
theorem euclidean_curvatureTensorAt_eq_zero (p : Plane)
    (u v w : TangentSpace (modelWithCornersSelf ℝ Plane) p) :
    PetersenLib.curvatureTensorAt
      ((PetersenLib.innerProductSpaceMetric Plane).leviCivita).toAffineConnection
      p u v w = 0 := by
  rw [PetersenLib.curvatureTensorAt]
  exact PetersenLib.euclideanSpace_curvature_eq_zero
    (PetersenLib.extendTangentVector p u).smooth
    (PetersenLib.extendTangentVector p v).smooth
    (PetersenLib.extendTangentVector p w).smooth p

/-- **Math.** **U3 constructed-input consumer (Petersen family).** The
exponential map of the constructed Euclidean metric sends the zero tangent
vector to the base point. -/
theorem euclidean_expMap_zero (p : Plane) :
    PetersenLib.expMap (PetersenLib.euclideanMetric 2) p
      (0 : TangentSpace (modelWithCornersSelf ℝ Plane) p) = p :=
  PetersenLib.expMap_zero (PetersenLib.euclideanMetric 2) p

/-- **Math.** **U3 constructed-input consumer (Petersen family).** The ray form
of the exponential at a scaled zero velocity of the constructed Euclidean
metric: `exp_p(t·0) = p`. -/
theorem euclidean_expMap_zero_smul (p : Plane) (t : ℝ) :
    PetersenLib.expMap (PetersenLib.euclideanMetric 2) p
      (t • (0 : TangentSpace (modelWithCornersSelf ℝ Plane) p)) = p := by
  rw [smul_zero]
  exact euclidean_expMap_zero p

end

end UpstreamAdaptersPetersen.DownstreamUse
