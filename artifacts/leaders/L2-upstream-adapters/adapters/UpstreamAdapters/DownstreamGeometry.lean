import DoCarmoLib
import DoCarmoLib.Riemannian.Manifold.EuclideanFlat
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3Euclidean
import UpstreamAdapters.Adapters

/-!
# Constructed-input consumers for the curvature and geodesic APIs (U1, U3)

`DownstreamUse.lean` consumes the adapter layer only at very small inputs
(algebraic bilinear forms, constant paths, the manifold `ℝ`).  This module is
the *geometric* consumer: it constructs a concrete Riemannian manifold — the
Euclidean plane `EuclideanSpace ℝ (Fin 2)` with its canonical flat connection
`euclideanConnection` and metric `DCEuclideanMetric` — and proves new statements
by applying the audited upstream curvature / geodesic / exponential /
parallel-transport API to it.

Everything here is a **new** statement about the constructed model, not a
restatement of an upstream theorem:

* `euclidean_curvatureOperatorAt_eq_zero` — the pointwise `(1,3)` curvature
  operator of the flat plane vanishes (upstream states only the field-level
  vanishing `euclideanConnection_curvature`), proved through the upstream
  tensoriality bridge `curvatureOperatorAt_eq`.
* `euclidean_curvatureFormAt_eq_zero` — the pointwise `(0,4)` curvature form
  vanishes (upstream defines `curvatureFormAt` but states no vanishing for it).
* `euclidean_alias_curvature_zero_third` — the same vanishing in the last slot,
  routed through the **adapter alias** `UpstreamAdapters.Adapters.DoCarmo.curvature_zero_right`,
  showing the renamed layer is consumable downstream.
* `euclideanLine_isGeodesic` — the constructed affine line
  `t ↦ p + t • v` is a geodesic of the Euclidean metric, obtained from the
  upstream Euclidean geodesic theorem.
* `euclideanLine_hasGeodesicEquationAt` — the projected moving-foot geodesic
  equation at every time.
* `euclideanLine_expMapIntrinsic` / `_smul` / `_add` — the intrinsic
  exponential of the constructed model is the affine line, and the flow
  identities `exp_p(tv) = γ(t)`, `exp_{γ(s)}(tv) = γ(s+t)`.
* `euclideanLine_parallelTransport_preserves` — parallel transport along the
  constructed affine line preserves the Euclidean inner product, via the
  upstream parallel-transport isometry theorem.

**General** (model-independent) U1 consumers are also proved here, for any
affine connection on any manifold of the DoCarmo development:

* `curvatureOperatorAt_antisymm_left` — the pointwise curvature operator is
  antisymmetric in its first two arguments (upstream states this only for
  vector fields, `curvature_antisymm_left`);
* `curvatureOperatorAt_bianchi` — the pointwise first Bianchi identity for a
  symmetric connection, `R(u,v)w + R(v,w)u + R(w,u)v = 0` (upstream states the
  field-level `curvature_bianchi` only).

The corresponding pointwise statements for the metric-lowered `(0,4)` form are
**not** reproved here: `MorganTianLib.curvatureFormAt_antisymm_left/_right` and
`MorganTianLib.curvatureFormAt_bianchi` already exist at the pointwise level and
are exposed to downstream lanes through the adapter aliases in
`UpstreamAdapters.Adapters.MorganTian`.  The operator-level versions above are
the genuinely new ones (no upstream pointwise operator statement exists, and
they need no metric).

None of these names occurs upstream; each proof term applies upstream
declarations to constructed data.  Semantic class: `proved` for the
unconditional general consequences; `model` for the statements that hold only
for the concrete flat Euclidean plane (they are recorded as model-level, so
they do not by themselves close U1/U3).  No hypothesis is assumed that is
equivalent to the conclusion.
-/

namespace UpstreamAdapters.DownstreamGeometry

open Riemannian
open scoped Manifold ContDiff

noncomputable section

/-- **Math.** Constructed input manifold: the Euclidean plane, a finite-dimensional real
inner-product space viewed as a manifold over itself. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-! ## U1: pointwise curvature of the constructed flat connection -/

/-- **Math.** **U1 constructed-input consumer.** The pointwise curvature operator of the
Euclidean connection on the plane vanishes on every triple of tangent vectors.

This is the pointwise `(1,3)`-tensor form of the upstream field-level identity
`euclideanConnection_curvature : R(X,Y)Z = 0`; the passage from fields to
tangent vectors is the upstream tensoriality theorem `curvatureOperatorAt_eq`,
applied to the upstream `extendField` sections. -/
theorem euclidean_curvatureOperatorAt_eq_zero (p : Plane)
    (u v w : TangentSpace 𝓘(ℝ, Plane) p) :
    (euclideanConnection (F := Plane)).curvatureOperatorAt p u v w = 0 := by
  rw [AffineConnection.curvatureOperatorAt_eq
    (nabla := euclideanConnection (F := Plane)) p
    (AffineConnection.extendField_apply p u)
    (AffineConnection.extendField_apply p v)
    (AffineConnection.extendField_apply p w)]
  simp [euclideanConnection_curvature]

/-- **Math.** **U1 constructed-input consumer.** The pointwise curvature `(0,4)` form of
the Euclidean plane vanishes identically, for the constructed metric
`DCEuclideanMetric` and the constructed connection `euclideanConnection`. -/
theorem euclidean_curvatureFormAt_eq_zero (p : Plane)
    (x y z t : TangentSpace 𝓘(ℝ, Plane) p) :
    (euclideanConnection (F := Plane)).curvatureFormAt
      (DCEuclideanMetric (F := Plane)) p x y z t = 0 := by
  rw [AffineConnection.curvatureFormAt, euclidean_curvatureOperatorAt_eq_zero]
  simp

/-- **Math.** **U1 adapter-alias consumer.** The third slot vanishing for the constructed
Euclidean connection, routed through the adapter alias
`UpstreamAdapters.Adapters.DoCarmo.curvature_zero_right` rather than the
original upstream name: downstream lanes can consume the renamed layer. -/
theorem euclidean_alias_curvature_zero_third
    (X Y : SmoothVectorField 𝓘(ℝ, Plane) Plane) (p : Plane) :
    ((euclideanConnection (F := Plane)).curvature X Y 0) p = 0 :=
  UpstreamAdapters.Adapters.DoCarmo.curvature_zero_right
    (euclideanConnection (F := Plane)) X Y p

/-! ## U3: constructed geodesics, exponential and parallel transport -/

/-- **Math.** Constructed input curve: the affine line through `p` with velocity `v`. -/
def euclideanLine (p v : Plane) : ℝ → Plane := fun t => p + t • v

@[simp]
theorem euclideanLine_zero (p v : Plane) : euclideanLine p v 0 = p := by
  simp [euclideanLine]

/-- **Math.** **U3 constructed-input consumer.** The affine line is a geodesic of the
Euclidean metric; this is the upstream Euclidean geodesic theorem consumed at
the locally constructed curve `euclideanLine`. -/
theorem euclideanLine_isGeodesic (p v : Plane) :
    Geodesic.IsGeodesic (I := 𝓘(ℝ, Plane)) (DCEuclideanMetric (F := Plane))
      (euclideanLine p v) :=
  isGeodesic_euclideanGeodesic p v

/-- **Math.** **U3 constructed-input consumer.** Projection of the geodesic predicate to
the moving-foot geodesic equation at every time. -/
theorem euclideanLine_hasGeodesicEquationAt (p v : Plane) (t : ℝ) :
    Geodesic.HasGeodesicEquationAt (I := 𝓘(ℝ, Plane))
      (DCEuclideanMetric (F := Plane)) (euclideanLine p v) t :=
  Geodesic.IsGeodesic.hasGeodesicEquationAt (euclideanLine_isGeodesic p v) t

/-- **Math.** The constructed affine line is smooth (needed as the regularity input of
the parallel-transport isometry theorem). -/
theorem euclideanLine_contMDiff (p v : Plane) :
    ContMDiff (modelWithCornersSelf ℝ ℝ) 𝓘(ℝ, Plane) 1 (euclideanLine p v) :=
  (contMDiff_const (c := p)).add (contMDiff_id.smul contMDiff_const)

/-- **Math.** **U3 constructed-input consumer (exponential API).** The intrinsic
exponential of the constructed Euclidean model is the affine line evaluated at
time `1`: `exp_p(v) = γ(1)`. -/
theorem euclideanLine_expMapIntrinsic (p v : Plane) :
    Exponential.expMapIntrinsic (I := 𝓘(ℝ, Plane)) (DCEuclideanMetric (F := Plane))
      p v = euclideanLine p v 1 := by
  rw [expMapIntrinsic_euclidean]
  simp [euclideanLine]

/-- **Math.** **U3 constructed-input consumer (exponential flow, scalar).** The
exponential of a scaled velocity is the affine line at the corresponding time:
`exp_p(tv) = γ(t)`. -/
theorem euclideanLine_expMapIntrinsic_smul (p v : Plane) (t : ℝ) :
    Exponential.expMapIntrinsic (I := 𝓘(ℝ, Plane)) (DCEuclideanMetric (F := Plane))
      p (t • v) = euclideanLine p v t := by
  rw [expMapIntrinsic_euclidean]
  simp [euclideanLine]

/-- **Math.** **U3 constructed-input consumer (exponential flow, basepoint).** Starting
the exponential at a point of the same geodesic: `exp_{γ(s)}(tv) = γ(s+t)`. -/
theorem euclideanLine_expMapIntrinsic_add (p v : Plane) (s t : ℝ) :
    Exponential.expMapIntrinsic (I := 𝓘(ℝ, Plane)) (DCEuclideanMetric (F := Plane))
      (euclideanLine p v s) (t • v) = euclideanLine p v (s + t) := by
  rw [expMapIntrinsic_euclidean]
  simp only [euclideanLine, add_smul]
  module

/-- **Math.** **U3 constructed-input consumer (parallel transport).** Parallel transport
along the constructed affine line preserves the Euclidean inner product. -/
theorem euclideanLine_parallelTransport_preserves (p v : Plane) {a b : ℝ} (hab : a < b)
    (x y : TangentSpace 𝓘(ℝ, Plane) (euclideanLine p v a)) :
    (DCEuclideanMetric (F := Plane)).metricInner (euclideanLine p v b)
        ((parallelTransportTangentEquiv (I := 𝓘(ℝ, Plane))
          (DCEuclideanMetric (F := Plane)) hab (euclideanLine_contMDiff p v)) x)
        ((parallelTransportTangentEquiv (I := 𝓘(ℝ, Plane))
          (DCEuclideanMetric (F := Plane)) hab (euclideanLine_contMDiff p v)) y)
      = (DCEuclideanMetric (F := Plane)).metricInner (euclideanLine p v a) x y :=
  metricInner_parallelTransportTangentEquiv (I := 𝓘(ℝ, Plane))
    (DCEuclideanMetric (F := Plane)) hab (euclideanLine_contMDiff p v) x y

/-! ## General (model-independent) pointwise curvature consumers

The two theorems below hold for **any** affine connection on **any** smooth
manifold of the DoCarmo development, not just for the flat plane.  Upstream
states the corresponding symmetries only at the level of vector fields
(`curvature_antisymm_left`, `curvature_bianchi`); the pointwise `(1,3)`-operator
versions are new consequences obtained through the audited tensoriality bridge
`curvatureOperatorAt_eq`.
-/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **U1 general consumer.** The pointwise curvature operator of an
arbitrary affine connection is antisymmetric in its first two arguments. -/
theorem curvatureOperatorAt_antisymm_left (nabla : AffineConnection I M) (p : M)
    (u v w : TangentSpace I p) :
    nabla.curvatureOperatorAt p u v w = - nabla.curvatureOperatorAt p v u w := by
  rw [nabla.curvatureOperatorAt_eq p (X := AffineConnection.extendField p u) (Y := AffineConnection.extendField p v)
      (Z := AffineConnection.extendField p w) (AffineConnection.extendField_apply p u)
      (AffineConnection.extendField_apply p v) (AffineConnection.extendField_apply p w),
    nabla.curvatureOperatorAt_eq p (X := AffineConnection.extendField p v) (Y := AffineConnection.extendField p u)
      (Z := AffineConnection.extendField p w) (AffineConnection.extendField_apply p v)
      (AffineConnection.extendField_apply p u) (AffineConnection.extendField_apply p w)]
  exact nabla.curvature_antisymm_left _ _ _ p

/-- **Math.** **U1 general consumer.** The pointwise first Bianchi identity for
a symmetric affine connection: `R(u,v)w + R(v,w)u + R(w,u)v = 0` on tangent
vectors. -/
theorem curvatureOperatorAt_bianchi (nabla : AffineConnection I M)
    (hsym : nabla.IsSymmetric) (p : M) (u v w : TangentSpace I p) :
    nabla.curvatureOperatorAt p u v w + nabla.curvatureOperatorAt p v w u
      + nabla.curvatureOperatorAt p w u v = 0 := by
  rw [nabla.curvatureOperatorAt_eq p (X := AffineConnection.extendField p u) (Y := AffineConnection.extendField p v)
      (Z := AffineConnection.extendField p w) (AffineConnection.extendField_apply p u)
      (AffineConnection.extendField_apply p v) (AffineConnection.extendField_apply p w),
    nabla.curvatureOperatorAt_eq p (X := AffineConnection.extendField p v) (Y := AffineConnection.extendField p w)
      (Z := AffineConnection.extendField p u) (AffineConnection.extendField_apply p v)
      (AffineConnection.extendField_apply p w) (AffineConnection.extendField_apply p u),
    nabla.curvatureOperatorAt_eq p (X := AffineConnection.extendField p w) (Y := AffineConnection.extendField p u)
      (Z := AffineConnection.extendField p v) (AffineConnection.extendField_apply p w)
      (AffineConnection.extendField_apply p u) (AffineConnection.extendField_apply p v)]
  exact nabla.curvature_bianchi hsym _ _ _ p

/-- **Math.** **U1 general consumer through the adapter alias layer.** The
pointwise curvature operator of any affine connection vanishes when its first
argument is zero; the proof routes through the adapter alias
`UpstreamAdapters.Adapters.DoCarmo.curvature_zero_left` (the renamed upstream
field-level theorem), so the alias layer is exercised at full generality, not
only on the Euclidean plane. -/
theorem curvatureOperatorAt_zero_first (nabla : AffineConnection I M) (p : M)
    (v w : TangentSpace I p) :
    nabla.curvatureOperatorAt p 0 v w = 0 := by
  rw [nabla.curvatureOperatorAt_eq p (X := 0) (Y := AffineConnection.extendField p v)
      (Z := AffineConnection.extendField p w) (by simp)
      (AffineConnection.extendField_apply p v) (AffineConnection.extendField_apply p w)]
  exact UpstreamAdapters.Adapters.DoCarmo.curvature_zero_left nabla _ _ p

/-- **Math.** **U1 general consumer through the adapter alias layer.** The same
for a zero third argument, routed through the adapter alias
`UpstreamAdapters.Adapters.DoCarmo.curvature_zero_right`. -/
theorem curvatureOperatorAt_zero_third (nabla : AffineConnection I M) (p : M)
    (u v : TangentSpace I p) :
    nabla.curvatureOperatorAt p u v 0 = 0 := by
  rw [nabla.curvatureOperatorAt_eq p (X := AffineConnection.extendField p u)
      (Y := AffineConnection.extendField p v) (Z := 0)
      (AffineConnection.extendField_apply p u) (AffineConnection.extendField_apply p v)
      (by simp)]
  exact UpstreamAdapters.Adapters.DoCarmo.curvature_zero_right nabla _ _ p

end General

end

end UpstreamAdapters.DownstreamGeometry
