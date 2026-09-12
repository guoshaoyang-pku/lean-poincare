import DoCarmoLib
import UpstreamAdapters.Adapters

/-!
# Pointwise curvature-form symmetries with the hypotheses each one needs (U1)

Upstream states the symmetries of the metric-lowered curvature `(0,4)`-form in
two places:

* **field level**, each with its own hypotheses: `curvatureForm_antisymm_left`
  (any connection), `curvatureForm_antisymm_right` (metric-compatible
  connection), `curvatureForm_bianchi` (symmetric connection) and
  `curvatureForm_pairSwap` (symmetric and metric-compatible connection);
* **pointwise**, but only bundled for the *Levi-Civita* connection inside
  `AffineConnection.isAlgCurvatureForm_curvatureFormAt`, which requires
  `nabla.IsLeviCivita g` and installs a local `RiemannianBundle` instance.

A downstream lane that has, say, only `hcompat : nabla.IsMetricCompatible g`
cannot use the bundled route without also producing symmetry of the connection;
this module exposes the four symmetries as named pointwise lemmas with the
hypotheses each one actually needs.

**Status.** These are *derived consumers*, not new mathematics: every proof
rewrites the pointwise form to the field-level form with the upstream
`curvatureFormAt_eq` tensoriality bridge and then applies the upstream field
lemma.  The genuinely new pointwise **operator**-level statements are in
`UpstreamAdapters.DownstreamGeometry`.  The pointwise form-level symmetries for
the Levi-Civita connection are *already upstream* (MorganTian's
`curvatureFormAt_antisymm_left/_right/_bianchi` and DoCarmo's
`isAlgCurvatureForm_curvatureFormAt`); the only thing added here is the explicit
weaker-hypothesis form, and the card records it as such.
-/

namespace UpstreamAdapters.PointwiseSymmetries

open Riemannian
open scoped Manifold ContDiff

noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **U1 pointwise form consumer (no hypotheses on the connection).**
The pointwise curvature `(0,4)`-form of *any* affine connection is antisymmetric
in its first two arguments.  Upstream has the field-level
`curvatureForm_antisymm_left`; the pointwise form is available upstream only
bundled for a Levi-Civita connection inside `isAlgCurvatureForm_curvatureFormAt`. -/
theorem curvatureFormAt_skew_fst (nabla : AffineConnection I M) (g : RiemannianMetric I M)
    (p : M) (x y z t : TangentSpace I p) :
    nabla.curvatureFormAt g p x y z t = -nabla.curvatureFormAt g p y x z t := by
  rw [nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p x)
      (AffineConnection.extendField_apply p y) (AffineConnection.extendField_apply p z)
      (AffineConnection.extendField_apply p t),
    nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p y)
      (AffineConnection.extendField_apply p x) (AffineConnection.extendField_apply p z)
      (AffineConnection.extendField_apply p t)]
  exact nabla.curvatureForm_antisymm_left g _ _ _ _ p

/-- **Math.** **U1 pointwise form consumer (metric-compatible connection).** The
pointwise curvature `(0,4)`-form of a metric-compatible connection is
antisymmetric in its last two arguments.  This weakens the hypothesis of the
upstream bundled pointwise route (`IsLeviCivita`, i.e. symmetric *and*
compatible) to compatibility alone. -/
theorem curvatureFormAt_skew_snd_of_isMetricCompatible (nabla : AffineConnection I M)
    (g : RiemannianMetric I M) (hcompat : nabla.IsMetricCompatible g) (p : M)
    (x y z t : TangentSpace I p) :
    nabla.curvatureFormAt g p x y z t = -nabla.curvatureFormAt g p x y t z := by
  rw [nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p x)
      (AffineConnection.extendField_apply p y) (AffineConnection.extendField_apply p z)
      (AffineConnection.extendField_apply p t),
    nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p x)
      (AffineConnection.extendField_apply p y) (AffineConnection.extendField_apply p t)
      (AffineConnection.extendField_apply p z)]
  exact nabla.curvatureForm_antisymm_right g hcompat _ _ _ _ p

/-- **Math.** **U1 pointwise form consumer (symmetric connection).** The pointwise
first Bianchi identity for the `(0,4)`-form of a symmetric affine connection.
This weakens the hypothesis of the upstream bundled pointwise route to symmetry
alone (no metric compatibility needed). -/
theorem curvatureFormAt_bianchi_of_isSymmetric (nabla : AffineConnection I M)
    (g : RiemannianMetric I M) (hsym : nabla.IsSymmetric) (p : M)
    (x y z t : TangentSpace I p) :
    nabla.curvatureFormAt g p x y z t + nabla.curvatureFormAt g p y z x t
      + nabla.curvatureFormAt g p z x y t = 0 := by
  rw [nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p x)
      (AffineConnection.extendField_apply p y) (AffineConnection.extendField_apply p z)
      (AffineConnection.extendField_apply p t),
    nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p y)
      (AffineConnection.extendField_apply p z) (AffineConnection.extendField_apply p x)
      (AffineConnection.extendField_apply p t),
    nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p z)
      (AffineConnection.extendField_apply p x) (AffineConnection.extendField_apply p y)
      (AffineConnection.extendField_apply p t)]
  exact nabla.curvatureForm_bianchi g hsym _ _ _ _ p

/-- **Math.** **U1 pointwise form consumer (symmetric and metric-compatible
connection).** The pointwise pair-swap symmetry
`R(x,y,z,t) = R(z,t,x,y)` of the `(0,4)`-form.  This is the pointwise form of
the upstream field-level `curvatureForm_pairSwap`; upstream states the pointwise
`(0,4)` symmetries explicitly only for the Levi-Civita connection. -/
theorem curvatureFormAt_pairSwap_of_isSymmetric_of_isMetricCompatible
    (nabla : AffineConnection I M) (g : RiemannianMetric I M) (hsym : nabla.IsSymmetric)
    (hcompat : nabla.IsMetricCompatible g) (p : M) (x y z t : TangentSpace I p) :
    nabla.curvatureFormAt g p x y z t = nabla.curvatureFormAt g p z t x y := by
  rw [nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p x)
      (AffineConnection.extendField_apply p y) (AffineConnection.extendField_apply p z)
      (AffineConnection.extendField_apply p t),
    nabla.curvatureFormAt_eq g p (AffineConnection.extendField_apply p z)
      (AffineConnection.extendField_apply p t) (AffineConnection.extendField_apply p x)
      (AffineConnection.extendField_apply p y)]
  exact nabla.curvatureForm_pairSwap g hsym hcompat _ _ _ _ p

end General

end

end UpstreamAdapters.PointwiseSymmetries
