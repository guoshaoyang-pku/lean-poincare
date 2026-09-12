/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (Riemannian metric bridge)

# The chart Gram matrix of a genuine Riemannian metric at the release pin

`ManifoldIBP.GlobalMeasure` builds the Riemannian measure of an overlapping atlas from the
chart Gram matrices `gᵢⱼ`, but it takes the `(0,2)`-tensor transformation law of the metric as
a **hypothesis** (`OverlapAtlas.metric_transform`). This module discharges that hypothesis for
a genuine Riemannian metric: it connects the release pin's Riemannian bundle structure
(`Bundle.RiemannianBundle`, `IsContMDiffRiemannianBundle`, i.e. mathlib's replacement for the
upstream `Bundle.ContMDiffRiemannianMetric`) to the chart Gram matrix, and *proves* the
transformation law

`G^β(x) = Aᵀ · G^α(x) · A`,  `A = tangentCoordChange I β α x`,

the determinant form `det G^β = (det A)² · det G^α`, and the density form
`√(det G^β) = |det A| · √(det G^α)`. This is the release-pin port of the upstream Frenzymath
development (`third_party/frenzymath/Poincare-Conjecture @ bb91a091`,
`DoCarmoLib/Riemannian/Geodesic/HopfRinow/MetricBridge.lean`: `chartGramMatrix_change`,
`chartGramMatrix_det_change`, `chartGramMatrix_det_pos`; consumed by
`MorganTianLib/Ch01/RiemannianMeasure.lean`), re-based on the pin's `RiemannianBundle` API
instead of the upstream `Bundle.ContMDiffRiemannianMetric` structure (which does not exist at
the pin).

## What is proved here

* `trivializationAt_symm_eq_tangentCoordChange` — the inverse tangent trivialization at `α`
  over a foot `b` is the tangent coordinate change `tangentCoordChange I α b b` (the pin's
  version of the upstream readback bridge, from `TangentBundle.symmL_trivializationAt_eq_core`);
* `trivializationAt_symm_eq_sum` — readback expansion in the chart frame;
* `chartGramMatrix` — the Gram matrix of the chart coordinate frame,
  `G^α_{ij}(x) = ⟪(trivializationAt α).symm x eᵢ, (trivializationAt α).symm x eⱼ⟫`;
* **`chartGramMatrix_change_apply` / `chartGramMatrix_change`** — the `(0,2)`-tensor
  transformation law, entrywise and in matrix form;
* `chartGramMatrix_det_change` / `chartGramMatrix_sqrt_det_change` — the determinant and
  density forms which are exactly the Jacobian factor of mathlib's change-of-variables formula;
* `chartGramMatrix_posDef` / `chartGramMatrix_det_pos` — positive definiteness of the chart
  Gram matrix (so `√(det G)` is a genuine positive density).

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file. The
metric is an *explicit data* argument of the statements (`Bundle.RiemannianBundle` instance),
never a hypothesis equivalent to a conclusion.
-/
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Analysis.Matrix.PosDef

open Bundle Set
open scoped Manifold ContDiff Topology Bundle Matrix BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace Poincare.D13.Riemannian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The chart coordinate functionals -/

/-- The `i`-th coordinate of a model vector in the model basis `B`. -/
def chartCoord (B : Module.Basis ι ℝ E) (i : ι) (v : E) : ℝ :=
  (B).repr v i

@[simp]
lemma chartCoord_def (B : Module.Basis ι ℝ E) (i : ι) (v : E) :
    chartCoord B i v = (B).repr v i := rfl

/-! ## Readback of model vectors into the tangent fibre -/

/-- **The readback bridge.** Over a foot `b` in the source of the chart at `α`, the inverse
tangent trivialization at `α` is the tangent coordinate change `tangentCoordChange I α b b`.
This is the release-pin port of the upstream
`Riemannian.trivializationAt_symm_eq_tangentCoordChange`. -/
theorem trivializationAt_symm_eq_tangentCoordChange (α : M) {b : M}
    (hb : b ∈ (chartAt H α).source) (a : E) :
    (trivializationAt E (TangentSpace I) α).symm b a = tangentCoordChange I α b b a := by
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hb a]
  exact congrArg (fun f => f a) (TangentBundle.symmL_trivializationAt_eq_core (I := I) hb)

/-- **Readback expansion.** The inverse trivialization at `α` applied at a foot `b` to a model
vector `a` is the linear combination of chart-frame vectors with the coordinates of `a`. This
is the release-pin port of the upstream
`Riemannian.trivializationAt_symm_eq_sum_chartBasisVecFiber`. -/
theorem trivializationAt_symm_eq_sum (B : Module.Basis ι ℝ E) (α : M) (x : M) (a : E)
    (hx : x ∈ (chartAt H α).source) :
    (trivializationAt E (TangentSpace I) α).symm x a
      = ∑ i, chartCoord B i a •
          (trivializationAt E (TangentSpace I) α).symm x (B i) := by
  rw [← Bundle.Trivialization.coe_symmₗ (R := ℝ)
    (trivializationAt E (TangentSpace I) α) hx]
  conv_lhs => rw [← Module.Basis.sum_repr (B) a]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  rfl

/-! ## The chart Gram matrix -/

section Metric

variable [RiemannianBundle (TangentSpace I : M → Type _)]

/-- **The chart Gram matrix** of a Riemannian metric in the chart at `α`: the Gram matrix of
the chart coordinate frame in the fibre inner product registered by the
`Bundle.RiemannianBundle` instance. -/
def chartGramMatrix (B : Module.Basis ι ℝ E) (α : M) (x : M) :
    Matrix (ι) (ι) ℝ :=
  Matrix.of fun i j =>
    inner ℝ ((trivializationAt E (TangentSpace I) α).symm x (B i))
      ((trivializationAt E (TangentSpace I) α).symm x (B j))

@[simp]
lemma chartGramMatrix_apply (B : Module.Basis ι ℝ E) (α : M) (x : M) (i j : ι) :
    chartGramMatrix (I := I) B α x i j =
      inner ℝ ((trivializationAt E (TangentSpace I) α).symm x (B i))
        ((trivializationAt E (TangentSpace I) α).symm x (B j)) := rfl

/-- The chart-frame vector at `α` and `x`. -/
def chartFrameVec (B : Module.Basis ι ℝ E) (α : M) (i : ι) (x : M) : TangentSpace I x :=
  (trivializationAt E (TangentSpace I) α).symm x (B i)

/-- **The Gram pairing is the intrinsic inner product of the frame readbacks.** -/
lemma chartGramMatrix_eq_inner (B : Module.Basis ι ℝ E) (α : M) (x : M) (i j : ι) :
    chartGramMatrix (I := I) B α x i j
      = inner ℝ (chartFrameVec (I := I) B α i x) (chartFrameVec (I := I) B α j x) := rfl

/-- In the chart source, the `β`-chart frame vector is the `α`-chart readback of the tangent
coordinate change: the two chart frames of `T_xM` differ by the derivative of the chart
transition map. Port of the upstream `chartBasisVecFiber_eq_symm_tangentCoordChange`. -/
theorem chartFrameVec_eq_symm_tangentCoordChange (B : Module.Basis ι ℝ E) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (i : ι) :
    chartFrameVec (I := I) B β i x =
      (trivializationAt E (TangentSpace I) α).symm x
        (tangentCoordChange I β α x (B i)) := by
  have hxα' : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hxβ' : x ∈ (extChartAt I β).source := by rwa [extChartAt_source]
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  rw [chartFrameVec, trivializationAt_symm_eq_tangentCoordChange β hxβ,
    trivializationAt_symm_eq_tangentCoordChange α hxα]
  exact (tangentCoordChange_comp (I := I) ⟨⟨hxβ', hxα'⟩, hx⟩).symm

/-- **The Gram pairing expands in the chart frame.** The intrinsic pairing of two readbacks at
`α` is the double sum of the chart Gram matrix against the coordinates of the two model
vectors. Port of the upstream `metricInner_trivializationAt_symm`. -/
lemma chartGramMatrix_inner_eq_sum (B : Module.Basis ι ℝ E) (α : M) (x : M) (u v : E)
    (hx : x ∈ (chartAt H α).source) :
    inner ℝ ((trivializationAt E (TangentSpace I) α).symm x u)
        ((trivializationAt E (TangentSpace I) α).symm x v)
      = ∑ a, ∑ b, chartGramMatrix (I := I) B α x a b
          * chartCoord B a u * chartCoord B b v := by
  rw [trivializationAt_symm_eq_sum B α x u hx, trivializationAt_symm_eq_sum B α x v hx]
  rw [sum_inner]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [real_inner_smul_right, chartGramMatrix_apply]
  ring

/-- **The `(0,2)`-tensor transformation law, entrywise.** At a common foot `x` in both chart
sources, the `β`-chart Gram entry is the `α`-chart Gram pairing of the tangent coordinate
changes of the model basis vectors. -/
theorem chartGramMatrix_change_apply (B : Module.Basis ι ℝ E) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (i j : ι) :
    chartGramMatrix (I := I) B β x i j
      = ∑ a, ∑ b, chartGramMatrix (I := I) B α x a b
          * chartCoord B a (tangentCoordChange I β α x (B i))
          * chartCoord B b (tangentCoordChange I β α x (B j)) := by
  rw [show chartGramMatrix (I := I) B β x i j
      = inner ℝ (chartFrameVec (I := I) B β i x) (chartFrameVec (I := I) B β j x) from rfl,
    chartFrameVec_eq_symm_tangentCoordChange (I := I) B α β hxα hxβ i,
    chartFrameVec_eq_symm_tangentCoordChange (I := I) B α β hxα hxβ j]
  exact chartGramMatrix_inner_eq_sum (I := I) B α x _ _ hxα

/-- **The `(0,2)`-tensor transformation law, matrix form.** The `β`-chart Gram matrix is the
congruence of the `α`-chart Gram matrix by the matrix of `tangentCoordChange I β α x` in the
model basis. This is the release-pin port of the upstream `Riemannian.chartGramMatrix_change`
/ `chartGramMatrix_eq_conjTranspose_mul`, and it is exactly the equation that
`ManifoldIBP.OverlapAtlas.metric_transform` assumes. -/
theorem chartGramMatrix_change (B : Module.Basis ι ℝ E) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    chartGramMatrix (I := I) B β x
      = (LinearMap.toMatrix (B) (B)
            (tangentCoordChange I β α x).toLinearMap).transpose
          * chartGramMatrix (I := I) B α x
          * LinearMap.toMatrix (B) (B)
            (tangentCoordChange I β α x).toLinearMap := by
  ext i j
  rw [chartGramMatrix_change_apply (I := I) B α β hxα hxβ i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, chartCoord]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The determinant transformation law**: `det G^β(x) = (det A)² · det G^α(x)` with
`A = tangentCoordChange I β α x`. Port of the upstream `chartGramMatrix_det_change`. -/
theorem chartGramMatrix_det_change (B : Module.Basis ι ℝ E) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    (chartGramMatrix (I := I) B β x).det
      = (LinearMap.det (tangentCoordChange I β α x).toLinearMap) ^ 2
          * (chartGramMatrix (I := I) B α x).det := by
  rw [chartGramMatrix_change (I := I) B α β hxα hxβ, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, ← LinearMap.det_toMatrix (B)]
  ring

/-- **The density transformation law**: `√(det G^β(x)) = |det A| · √(det G^α(x))`. This is the
exact Jacobian factor that mathlib's change-of-variables formula produces, so the two cancel in
the well-definedness of the Riemannian measure. Port of the upstream
`sqrt_chartGramMatrix_det_change`. -/
theorem chartGramMatrix_sqrt_det_change (B : Module.Basis ι ℝ E) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    Real.sqrt (chartGramMatrix (I := I) B β x).det
      = |LinearMap.det (tangentCoordChange I β α x).toLinearMap|
          * Real.sqrt (chartGramMatrix (I := I) B α x).det := by
  rw [chartGramMatrix_det_change (I := I) B α β hxα hxβ, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs]

/-! ## The transition map and the atlas-shaped form of the law -/

/-- **The chart transition map** in coordinates: from the chart at `β` to the chart at `α`,
`y ↦ (extChartAt I α) ((extChartAt I β).symm y)`. This is the `transition` field of the
overlapping-atlas structure when the atlas is the genuine chart atlas. -/
def chartTransition (α β : M) : E → E :=
  fun y => (extChartAt I α) ((extChartAt I β).symm y)

@[simp]
lemma chartTransition_def (α β : M) :
    chartTransition (I := I) α β
      = fun y => (extChartAt I α) ((extChartAt I β).symm y) := rfl

/-- The tangent coordinate change *is* the derivative of the chart transition:
`tangentCoordChange I β α x = d(τ_{αβ})(extChartAt I β x)` within `range I`. -/
theorem tangentCoordChange_eq_fderivWithin_chartTransition (α β : M) (x : M) :
    tangentCoordChange I β α x
      = fderivWithin ℝ (chartTransition (I := I) α β) (range I) (extChartAt I β x) := by
  rw [tangentCoordChange_def]
  rfl

/-- **The chart-Gram transformation law in atlas shape.** The `β`-chart Gram matrix is the
congruence of the `α`-chart Gram matrix by the Jacobian of the chart transition, evaluated at
`extChartAt I β x`. This is *exactly* the equation postulated by
`ManifoldIBP.OverlapAtlas.metric_transform` with `transition = chartTransition`,
`metric = chartGramMatrix`; here it is a **theorem** of the Riemannian metric. -/
theorem chartGramMatrix_change_chartTransition (B : Module.Basis ι ℝ E) (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) :
    chartGramMatrix (I := I) B β x
      = (LinearMap.toMatrix (B) (B)
            (fderivWithin ℝ (chartTransition (I := I) α β) (range I)
              (extChartAt I β x)).toLinearMap).transpose
          * chartGramMatrix (I := I) B α x
          * LinearMap.toMatrix (B) (B)
            (fderivWithin ℝ (chartTransition (I := I) α β) (range I)
              (extChartAt I β x)).toLinearMap := by
  rw [← tangentCoordChange_eq_fderivWithin_chartTransition (I := I) α β x]
  exact chartGramMatrix_change (I := I) B α β hxα hxβ

/-! ## Positive definiteness -/

/-- The chart Gram matrix is Hermitian (symmetric, real entries). -/
theorem chartGramMatrix_isHermitian (B : Module.Basis ι ℝ E) (α : M) (x : M) :
    (chartGramMatrix (I := I) B α x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  rw [chartGramMatrix_apply, chartGramMatrix_apply, star_trivial]
  exact real_inner_comm _ _

/-- The chart frame is linearly independent in the chart source: the readback of a vanishing
linear combination vanishes only if all coefficients do. -/
lemma chartFrameVec_linearIndependent (B : Module.Basis ι ℝ E) (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    LinearIndependent ℝ (chartFrameVec (I := I) B α · x) := by
  have hframe : (chartFrameVec (I := I) B α · x)
      = fun i => (Bundle.Trivialization.continuousLinearEquivAt ℝ
          (trivializationAt E (TangentSpace I) α) x hx).symm (B i) := by
    funext i
    rw [chartFrameVec, ← Bundle.Trivialization.continuousLinearEquivAt_symm_apply (R := ℝ)
      (trivializationAt E (TangentSpace I) α) x hx]
  rw [hframe]
  exact (B).linearIndependent.map'
    ((Bundle.Trivialization.continuousLinearEquivAt ℝ
      (trivializationAt E (TangentSpace I) α) x hx).symm : E →ₗ[ℝ] TangentSpace I x)
    (LinearMap.ker_eq_bot.mpr (Bundle.Trivialization.continuousLinearEquivAt ℝ
      (trivializationAt E (TangentSpace I) α) x hx).symm.injective)

/-- **The chart Gram matrix is positive definite** on the chart source: the Gram matrix of a
frame in an inner product space is positive definite. Port of the upstream
`chartGramMatrix_posDef`. -/
theorem chartGramMatrix_posDef (B : Module.Basis ι ℝ E) (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    (chartGramMatrix (I := I) B α x).PosDef := by
  refine ⟨chartGramMatrix_isHermitian (I := I) B α x, ?_⟩
  intro u hu
  have h1 : u.sum (fun i xi => u.sum fun j xj =>
        star xi * chartGramMatrix (I := I) B α x i j * xj)
      = ∑ i, ∑ j, u i * chartGramMatrix (I := I) B α x i j * u j := by
    rw [Finsupp.sum_fintype]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [star_trivial]
      · intro j; simp
    · intro i; simp
  rw [h1]
  have hinner : (∑ i, ∑ j, u i * chartGramMatrix (I := I) B α x i j * u j)
      = inner ℝ (∑ i, u i • chartFrameVec (I := I) B α i x)
          (∑ j, u j • chartFrameVec (I := I) B α j x) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right, chartGramMatrix_eq_inner]
    ring
  rw [hinner]
  rw [real_inner_self_pos]
  intro hzero
  have h2 : ∀ i, (Bundle.Trivialization.continuousLinearEquivAt ℝ
        (trivializationAt E (TangentSpace I) α) x hx) (chartFrameVec (I := I) B α i x)
      = B i := by
    intro i
    have hcv : chartFrameVec (I := I) B α i x = (Bundle.Trivialization.continuousLinearEquivAt ℝ
        (trivializationAt E (TangentSpace I) α) x hx).symm (B i) := by
      rw [chartFrameVec, ← Bundle.Trivialization.continuousLinearEquivAt_symm_apply (R := ℝ)
        (trivializationAt E (TangentSpace I) α) x hx]
    rw [hcv]
    exact ContinuousLinearEquiv.apply_symm_apply _ _
  have hcomb : (∑ i, u i • B i) = 0 := by
    have h := congrArg (Bundle.Trivialization.continuousLinearEquivAt ℝ
      (trivializationAt E (TangentSpace I) α) x hx) hzero
    simpa only [map_sum, map_smul, map_zero, h2] using h
  have hzero' : ∀ i, u i = 0 := by
    have hli := (B).linearIndependent
    rw [Fintype.linearIndependent_iff] at hli
    exact hli u hcomb
  exact hu (Finsupp.ext fun i => by simpa using hzero' i)

/-- **The determinant of the chart Gram matrix is strictly positive** on the chart source, so
`√(det G)` is a genuine positive Riemannian density. Port of the upstream
`chartGramMatrix_det_pos`. -/
theorem chartGramMatrix_det_pos (B : Module.Basis ι ℝ E) (α : M) {x : M} (hx : x ∈ (chartAt H α).source) :
    0 < (chartGramMatrix (I := I) B α x).det :=
  Matrix.PosDef.det_pos (chartGramMatrix_posDef (I := I) B α hx)

end Metric

end Poincare.D13.Riemannian

/-! ## Axiom audit -/

#print axioms Poincare.D13.Riemannian.trivializationAt_symm_eq_tangentCoordChange
#print axioms Poincare.D13.Riemannian.trivializationAt_symm_eq_sum
#print axioms Poincare.D13.Riemannian.chartGramMatrix_change_apply
#print axioms Poincare.D13.Riemannian.chartGramMatrix_change
#print axioms Poincare.D13.Riemannian.chartGramMatrix_det_change
#print axioms Poincare.D13.Riemannian.chartGramMatrix_sqrt_det_change
#print axioms Poincare.D13.Riemannian.chartGramMatrix_isHermitian
#print axioms Poincare.D13.Riemannian.chartFrameVec_linearIndependent
#print axioms Poincare.D13.Riemannian.chartGramMatrix_posDef
#print axioms Poincare.D13.Riemannian.chartGramMatrix_det_pos
#print axioms Poincare.D13.Riemannian.chartTransition
#print axioms Poincare.D13.Riemannian.tangentCoordChange_eq_fderivWithin_chartTransition
#print axioms Poincare.D13.Riemannian.chartGramMatrix_change_chartTransition
