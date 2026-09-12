import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Poincare.L4.GeodesicSpray

**L4-C1: the second-order geodesic-spray ODE interface on a chart of a Riemannian manifold.**

This module constructs (does not assume) the coordinate form of the geodesic equation of the
pinned Levi-Civita connection, and proves local existence and uniqueness of its solutions.

## What is constructed

* `CoordinateMetric`: a Riemannian metric in coordinates on a model space `E`, given as a
  `C²` family of positive-definite symmetric bilinear forms together with the inverse metric
  (`sharp`) as explicit data with its defining property. This is the coordinate shadow of the
  pinned mathlib Riemannian metric `⟪·,·⟫` on the fibers of `TangentSpace I`.
* `christoffel`: the Christoffel symbol of the *Koszul formula*
  `g(Γ_w u, v) = ½ (∂_w g(u,v) + ∂_u g(w,v) - ∂_v g(w,u))`,
  built with `fderiv` from the metric coefficients. This is the coordinate expression of the
  pinned `leviCivitaConnection` (mathlib's `leviCivitaConnection_apply_inner` is exactly this
  formula with the coordinate fields' Lie brackets vanishing).
* `christoffel_koszul`, `christoffel_symm` (torsion-freeness in coordinates),
  `christoffel_metric_compatible` (metric compatibility in coordinates).
* `spray`: the second-order geodesic spray as a first-order vector field on `E × E`,
  `(x,v) ↦ (v, -Γ_x(v,v))`.
* Local existence and uniqueness of the geodesic equation in coordinates, phrased with
  mathlib's `IsMIntegralCurve` API.
* The exponential-map germ on the chart and its fixed-point property `expGerm (x, 0) = x`.

## Honest boundary (chart vs manifold)

Everything proved here is *coordinate-level*: it concerns the model space `E` and the metric
coefficients obtained from a chart. The identification of `christoffel` with the coefficients of
the pinned `leviCivitaConnection I M` in a chart requires the covariant derivative of a vector
field along a curve (equivalently, the local-frame connection coefficients), which the pinned
mathlib revision does not provide; that bridge is recorded as an explicit `Prop`
(`ChartSprayRepresentsLeviCivita`) and is **not** asserted. See the result card for the exact
classification of each declaration.
-/

open Bundle
open scoped Manifold ContDiff Topology InnerProductSpace
open Set Filter

-- The nested continuous-linear-map types in the Koszul construction make instance search
-- expensive; this bound is needed for deterministic elaboration.
set_option synthInstance.maxHeartbeats 800000

namespace Poincare
namespace L4
namespace GeodesicSpray

universe u

/-! ## Evaluation commutes with `fderiv` (constant argument) -/

section FDerivEval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Differentiating `y ↦ f y w` for a fixed `w` differentiates `f` and evaluates. -/
lemma fderiv_apply_const (f : E → F →L[ℝ] G) (w : F) (x : E)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => f y w) x = (fderiv ℝ f x).flip w := by
  rw [fderiv_clm_apply hf (differentiableAt_const w)]
  simp

/-- Evaluated form of `fderiv_apply_const`. -/
lemma fderiv_apply_const_apply (f : E → F →L[ℝ] G) (w : F) (x e : E)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => f y w) x e = (fderiv ℝ f x e) w := by
  rw [fderiv_apply_const f w x hf, ContinuousLinearMap.flip_apply]

/-- Differentiating `y ↦ f y u v` for fixed `u v` differentiates `f` and evaluates twice. -/
lemma fderiv_apply₂_const_apply (f : E → F →L[ℝ] G →L[ℝ] ℝ) (u : F) (v : G) (x w : E)
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => f y u v) x w = ((fderiv ℝ f x) w u) v := by
  have h1 : DifferentiableAt ℝ (fun y => f y u) x :=
    hf.clm_apply (differentiableAt_const u)
  have h2 := fderiv_apply_const_apply (fun y => f y u) v x w h1
  have h3 : fderiv ℝ (fun y => f y u) x = (fderiv ℝ f x).flip u :=
    fderiv_apply_const f u x hf
  rw [h3, ContinuousLinearMap.flip_apply] at h2
  exact h2

end FDerivEval

/-! ## Riemannian metrics in coordinates -/

/-- **A Riemannian metric in coordinates.** The metric coefficients
`g_x(u,v) = form x u v` form a positive-definite symmetric bilinear form at every `x`, the
inverse metric is given explicitly by `sharp` with the defining property
`g_x(sharp_x φ, w) = φ w`, and both are smooth in the base point (`C²` for the coefficients,
`C¹` for the inverse metric).

This is the coordinate shadow of a mathlib `RiemannianBundle` metric: for a chart `e` of `M`,
`form x u v = ⟪D_x u, D_x v⟫` where `D_x = mfderiv 𝓘(ℝ,E) I e.symm x` is the chart frame and
`⟪·,·⟫` is the pinned fiber inner product at `e.symm x` (see
`Poincare.L4.GeodesicSpray.chartMetricForm`). -/
structure CoordinateMetric (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The metric coefficients `g_x(u,v)`. -/
  form : E → E →L[ℝ] E →L[ℝ] ℝ
  /-- The inverse metric `g_x⁻¹` on covectors. -/
  sharp : E → (E →L[ℝ] ℝ) →L[ℝ] E
  /-- Symmetry of the metric coefficients. -/
  symm : ∀ x u v : E, form x u v = form x v u
  /-- Positive definiteness of the metric coefficients. -/
  pos : ∀ x u : E, u ≠ 0 → 0 < form x u u
  /-- The inverse metric is a right inverse to the metric. -/
  sharp_form : ∀ (x : E) (φ : E →L[ℝ] ℝ) (w : E), form x (sharp x φ) w = φ w
  /-- The metric coefficients are `C²` in the base point. This is the regularity of a
  Riemannian metric in a chart. -/
  contDiff : ContDiff ℝ 2 form
  /-- The inverse metric is `C¹` in the base point. -/
  contDiff_sharp : ContDiff ℝ 1 sharp

namespace CoordinateMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nondegeneracy of the metric coefficients: a vector pairing to zero against every vector is
zero. -/
theorem eq_zero_of_forall_form_eq_zero (G : CoordinateMetric E) (x z : E)
    (h : ∀ w : E, G.form x z w = 0) : z = 0 := by
  by_contra hz
  have hzz := G.pos x z hz
  rw [h z] at hzz
  exact lt_irrefl 0 hzz

/-- The metric coefficients are symmetric as a function of the two vector arguments. -/
theorem form_apply_comm (G : CoordinateMetric E) (x u v : E) :
    G.form x u v = G.form x v u :=
  G.symm x u v

theorem differentiableAt_form (G : CoordinateMetric E) (x : E) :
    DifferentiableAt ℝ G.form x :=
  (G.contDiff.differentiable (by norm_num)).differentiableAt

/-- The partial derivative of the metric coefficients in the base point, as a bilinear form:
`(x,u) ↦ ∂_u g|_x`. Applied to `v` it gives the covector `w ↦ ∂_u g(v,w)`; this is the first
and second Koszul terms. -/
noncomputable def partialDform (G : CoordinateMetric E) : E × E → E →L[ℝ] E →L[ℝ] ℝ :=
  fun p => (fderiv ℝ G.form p.1) p.2

/-- The third Koszul term: `(x,u,v) ↦ ∂_w g(u,v)` as a linear functional of `w`. -/
noncomputable def partialDformThird (G : CoordinateMetric E) : E × (E × E) → E →L[ℝ] ℝ :=
  fun q => fderiv ℝ (fun y => G.form y q.2.1 q.2.2) q.1

theorem contDiff_partialDform (G : CoordinateMetric E) : ContDiff ℝ 1 G.partialDform :=
  G.contDiff.contDiff_fderiv_apply (m := 1) (n := 2) (by norm_num)

theorem contDiff_partialDformThird (G : CoordinateMetric E) :
    ContDiff ℝ 1 G.partialDformThird := by
  have h := G.contDiff
  show ContDiff ℝ 1 (fun q : E × (E × E) =>
    fderiv ℝ (fun y : E => G.form y q.2.1 q.2.2) q.1)
  fun_prop

end CoordinateMetric

/-! ## The Christoffel symbol by the Koszul formula -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The Koszul functional of the coordinate metric**:
`w ↦ ½ (∂_u g(v,w) + ∂_v g(u,w) - ∂_w g(u,v))`, constructed from `fderiv` of the metric
coefficients alone. -/
noncomputable def koszulFunctional (G : CoordinateMetric E) (x u v : E) : E →L[ℝ] ℝ :=
  (1 / 2 : ℝ) •
    ((G.partialDform (x, u)) v + (G.partialDform (x, v)) u - G.partialDformThird (x, (u, v)))

/-- **The Christoffel symbol in coordinates, constructed from the metric by the Koszul
formula.** `Γ_x(u,v)` is the vector representing the covector
`w ↦ ½ (∂_u g(v,w) + ∂_v g(u,w) - ∂_w g(u,v))` under the metric. -/
noncomputable def christoffel (G : CoordinateMetric E) (x u v : E) : E :=
  G.sharp x (koszulFunctional G x u v)

/-- The first Koszul term is the derivative of the metric coefficients. -/
theorem fderiv_form_apply₁ (G : CoordinateMetric E) (x u v w : E) :
    fderiv ℝ (fun y => G.form y v w) x u = ((G.partialDform (x, u)) v) w := by
  have hf : DifferentiableAt ℝ G.form x := G.differentiableAt_form x
  have h1 := fderiv_apply_const_apply (fun y => G.form y v) w x u
    (hf.clm_apply (differentiableAt_const v))
  have h2 := fderiv_apply_const_apply G.form v x u hf
  rw [h2] at h1
  simpa [CoordinateMetric.partialDform] using h1

/-- The second Koszul term is the derivative of the metric coefficients. -/
theorem fderiv_form_apply₂ (G : CoordinateMetric E) (x u v w : E) :
    fderiv ℝ (fun y => G.form y u w) x v = ((G.partialDform (x, v)) u) w := by
  have hf : DifferentiableAt ℝ G.form x := G.differentiableAt_form x
  have h1 := fderiv_apply_const_apply (fun y => G.form y u) w x v
    (hf.clm_apply (differentiableAt_const u))
  have h2 := fderiv_apply_const_apply G.form u x v hf
  rw [h2] at h1
  simpa [CoordinateMetric.partialDform] using h1

/-- The third Koszul term is the derivative of the metric coefficients. -/
theorem fderiv_form_apply₃ (G : CoordinateMetric E) (x u v w : E) :
    fderiv ℝ (fun y => G.form y u v) x w = G.partialDformThird (x, (u, v)) w :=
  rfl

/-- The Koszul functional is `C¹` in `(x,u,v)`. -/
theorem contDiff_koszulFunctional (G : CoordinateMetric E) :
    ContDiff ℝ 1 (fun q : E × (E × E) =>
      koszulFunctional G q.1 q.2.1 q.2.2) := by
  have h1 := G.contDiff_partialDform
  have h3 := G.contDiff_partialDformThird
  show ContDiff ℝ 1 (fun q : E × (E × E) =>
    (1 / 2 : ℝ) • ((G.partialDform (q.1, q.2.1)) q.2.2 +
      (G.partialDform (q.1, q.2.2)) q.2.1 - G.partialDformThird (q.1, (q.2.1, q.2.2))))
  fun_prop

/-- The Christoffel symbol is `C¹` in all three arguments. -/
theorem contDiff_christoffel (G : CoordinateMetric E) :
    ContDiff ℝ 1 (fun q : E × (E × E) => christoffel G q.1 q.2.1 q.2.2) := by
  have hS := G.contDiff_sharp
  have hK := contDiff_koszulFunctional G
  show ContDiff ℝ 1 (fun q : E × (E × E) =>
    G.sharp q.1 (koszulFunctional G q.1 q.2.1 q.2.2))
  fun_prop

/-- **The Koszul formula in coordinates.** The defining identity of the Christoffel symbol:
`g(Γ_x(u,v), w) = ½ (∂_u g(v,w) + ∂_v g(u,w) - ∂_w g(u,v))`. This is the bracket-free Koszul
formula; the Lie-bracket terms of the manifold-level Koszul formula
(`CovariantDerivative.leviCivitaConnection_apply_inner`) vanish for coordinate vector fields. -/
theorem christoffel_koszul (G : CoordinateMetric E) (x u v w : E) :
    G.form x (christoffel G x u v) w =
      (1 / 2 : ℝ) *
        (fderiv ℝ (fun y => G.form y v w) x u
          + fderiv ℝ (fun y => G.form y u w) x v
          - fderiv ℝ (fun y => G.form y u v) x w) := by
  have hL : G.form x (christoffel G x u v) w = koszulFunctional G x u v w := by
    rw [christoffel, G.sharp_form]
  rw [hL, koszulFunctional, fderiv_form_apply₁ G x u v w, fderiv_form_apply₂ G x u v w,
    fderiv_form_apply₃ G x u v w]
  simp only [smul_apply, add_apply, sub_apply, smul_eq_mul]

/-- **Torsion-freeness in coordinates:** the Christoffel symbol is symmetric in its two lower
indices. This is the coordinate form of `(leviCivitaConnection I M).torsion = 0`. -/
theorem christoffel_symm (G : CoordinateMetric E) (x u v : E) :
    christoffel G x u v = christoffel G x v u := by
  have hzero : christoffel G x u v - christoffel G x v u = 0 := by
    apply G.eq_zero_of_forall_form_eq_zero x
    intro w
    have hsymm : ∀ y : E, G.form y v u = G.form y u v := fun y => G.symm y v u
    rw [map_sub, sub_apply, christoffel_koszul, christoffel_koszul]
    have e3 : fderiv ℝ (fun y => G.form y v u) x w =
        fderiv ℝ (fun y => G.form y u v) x w := by
      simp only [hsymm]
    rw [e3]
    ring
  exact sub_eq_zero.mp hzero

/-- **Metric compatibility in coordinates:** `∂_w g(u,v) = g(Γ_w u, v) + g(u, Γ_w v)`.
This is the coordinate form of `(leviCivitaConnection I M).IsMetricCompatible`, i.e. of
`∇g = 0`. -/
theorem christoffel_metric_compatible (G : CoordinateMetric E) (x u v w : E) :
    fderiv ℝ (fun y => G.form y u v) x w =
      G.form x (christoffel G x w u) v + G.form x u (christoffel G x w v) := by
  have h1 := christoffel_koszul G x w u v
  have h2 := christoffel_koszul G x w v u
  rw [← G.symm x u (christoffel G x w v)] at h2
  have e1 : fderiv ℝ (fun y => G.form y v u) x w =
      fderiv ℝ (fun y => G.form y u v) x w := by
    simp only [G.symm _ v u]
  have e2 : fderiv ℝ (fun y => G.form y w v) x u =
      fderiv ℝ (fun y => G.form y v w) x u := by
    simp only [G.symm _ w v]
  rw [h1, h2, e1, e2]
  ring



/-! ## Component derivatives of product-valued curves -/

section ProdDeriv

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The first component of a differentiable product-valued curve is differentiable. -/
theorem hasDerivAt_fst {z : ℝ → F × G} {w : F × G} {t : ℝ} (h : HasDerivAt z w t) :
    HasDerivAt (fun s => (z s).1) w.1 t := by
  rw [hasDerivAt_iff_hasFDerivAt] at h
  simpa [ContinuousLinearMap.smulRight_apply] using h.fst.hasDerivAt

/-- The second component of a differentiable product-valued curve is differentiable. -/
theorem hasDerivAt_snd {z : ℝ → F × G} {w : F × G} {t : ℝ} (h : HasDerivAt z w t) :
    HasDerivAt (fun s => (z s).2) w.2 t := by
  rw [hasDerivAt_iff_hasFDerivAt] at h
  simpa [ContinuousLinearMap.smulRight_apply] using h.snd.hasDerivAt

end ProdDeriv

/-! ## The self-model `IsMIntegralCurve` bridge

Mathlib's `IsMIntegralCurve` is stated for a manifold `M` with model `I`. For the self-model
`I = 𝓘(ℝ, F)` on a normed space `F`, an `M`-integral curve is exactly a solution of the
ordinary differential equation `γ' = v ∘ γ`. The bridge below makes this precise; it lets the
geodesic spray (a vector field on the model space `E × E`) be treated with mathlib's manifold
integral-curve API. -/

section SelfModelBridge

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

set_option backward.isDefEq.respectTransparency false in
/-- **Self-model bridge, on a set.** For the identity model on a normed space,
`IsMIntegralCurveOn` is the ordinary ODE `γ' = v ∘ γ` on the set, in the within-derivative
form appropriate to a set. -/
theorem isMIntegralCurveOn_self_iff {γ : ℝ → F} {v : F → F} {s : Set ℝ} :
    IsMIntegralCurveOn (I := 𝓘(ℝ, F)) γ v s ↔
      ∀ t ∈ s, HasDerivWithinAt γ (v (γ t)) s t := by
  constructor
  · intro h t ht
    have h' := h.hasDerivWithinAt (t₀ := t) ht (by simp)
    simpa [extChartAt_self_eq, tangentCoordChange_self] using h'
  · intro h t ht
    rw [hasMFDerivWithinAt_iff_hasFDerivWithinAt]
    exact h t ht

set_option backward.isDefEq.respectTransparency false in
/-- **Self-model bridge, at a point.** -/
theorem isMIntegralCurveAt_self_iff {γ : ℝ → F} {v : F → F} {t₀ : ℝ} :
    IsMIntegralCurveAt (I := 𝓘(ℝ, F)) γ v t₀ ↔
      ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (v (γ t)) t := by
  rw [isMIntegralCurveAt_iff', Metric.eventually_nhds_iff_ball]
  constructor
  · rintro ⟨ε, hε, hOn⟩
    exact ⟨ε, hε, fun t ht =>
      (isMIntegralCurveOn_self_iff.mp hOn t ht).hasDerivAt (Metric.isOpen_ball.mem_nhds ht)⟩
  · rintro ⟨ε, hε, h⟩
    exact ⟨ε, hε, isMIntegralCurveOn_self_iff.mpr fun t ht => (h t ht).hasDerivWithinAt⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Self-model bridge, globally.** -/
theorem isMIntegralCurve_self_iff {γ : ℝ → F} {v : F → F} :
    IsMIntegralCurve (I := 𝓘(ℝ, F)) γ v ↔ ∀ t : ℝ, HasDerivAt γ (v (γ t)) t := by
  rw [isMIntegralCurve_iff_isMIntegralCurveOn, isMIntegralCurveOn_self_iff]
  constructor
  · intro h t
    rw [← hasDerivWithinAt_univ]
    exact h t (mem_univ t)
  · intro h t _
    exact (h t).hasDerivWithinAt

end SelfModelBridge

/-! ## The geodesic spray on the chart -/

section Spray

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The second-order geodesic spray, as a first-order vector field on `E × E`:**
`(x,v) ↦ (v, -Γ_x(v,v))`. The first component is the velocity and the second is the coordinate
acceleration forced by the geodesic equation. -/
noncomputable def spray (G : CoordinateMetric E) : E × E → E × E :=
  fun z => (z.2, -christoffel G z.1 z.2 z.2)

/-- The spray is `C¹` when the metric coefficients are `C²`. -/
theorem contDiff_spray (G : CoordinateMetric E) : ContDiff ℝ 1 (spray G) := by
  have h := contDiff_christoffel G
  show ContDiff ℝ 1 (fun z : E × E => (z.2, -christoffel G z.1 z.2 z.2))
  fun_prop

/-- The spray vanishes on the zero section: zero velocity gives zero acceleration. -/
theorem christoffel_zero_right (G : CoordinateMetric E) (x : E) :
    christoffel G x 0 0 = 0 := by
  have hzero : koszulFunctional G x 0 0 = 0 := by
    simp [koszulFunctional, CoordinateMetric.partialDform, CoordinateMetric.partialDformThird]
  rw [christoffel, hzero, map_zero]

@[simp]
theorem spray_zero_velocity (G : CoordinateMetric E) (x : E) :
    spray G (x, 0) = 0 := by
  simp [spray, christoffel_zero_right]

/-- A curve in the chart solves the **first-order geodesic spray system** on `s`. -/
def IsSprayCurveOn (G : CoordinateMetric E) (z : ℝ → E × E) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, HasDerivAt z (spray G (z t)) t

/-- A curve in the chart solves the **first-order geodesic spray system** globally. -/
def IsSprayCurve (G : CoordinateMetric E) (z : ℝ → E × E) : Prop :=
  ∀ t : ℝ, HasDerivAt z (spray G (z t)) t

/-- A curve `x : ℝ → E` solves the **second-order geodesic equation in coordinates**:
`x'' = -Γ_x(x',x')`. -/
def IsCoordinateGeodesic (G : CoordinateMetric E) (x : ℝ → E) : Prop :=
  (∀ t : ℝ, HasDerivAt x (deriv x t) t) ∧
    ∀ t : ℝ, HasDerivAt (deriv x) (-(christoffel G (x t) (deriv x t) (deriv x t))) t

/-- **From the first-order spray system to the second-order geodesic equation.** The position
component of a spray solution is a coordinate geodesic. -/
theorem isCoordinateGeodesic_of_isSprayCurve (G : CoordinateMetric E) {z : ℝ → E × E}
    (hz : IsSprayCurve G z) : IsCoordinateGeodesic G (fun t => (z t).1) := by
  have hvel : deriv (fun t => (z t).1) = fun t => (z t).2 := by
    funext t
    exact (hasDerivAt_fst (hz t)).deriv
  constructor
  · intro t
    have h1 : HasDerivAt (fun t => (z t).1) ((z t).2) t := hasDerivAt_fst (hz t)
    rwa [hvel]
  · intro t
    have h2 : HasDerivAt (fun t => (z t).2)
        (-christoffel G (z t).1 (z t).2 (z t).2) t := hasDerivAt_snd (hz t)
    rw [hvel]
    simpa using h2

/-- The same, on an open interval. -/
theorem isCoordinateGeodesicOn_of_isSprayCurveOn (G : CoordinateMetric E) {z : ℝ → E × E}
    {s : Set ℝ} (hz : IsSprayCurveOn G z s) (hs : IsOpen s) :
    (∀ t ∈ s, HasDerivAt (fun t => (z t).1) (deriv (fun t => (z t).1) t) t) ∧
      ∀ t ∈ s,
        HasDerivAt (deriv (fun t => (z t).1))
          (-(christoffel G (z t).1 (deriv (fun t => (z t).1) t)
            (deriv (fun t => (z t).1) t))) t := by
  have hvel : ∀ t ∈ s, deriv (fun t => (z t).1) t = (z t).2 :=
    fun t ht => (hasDerivAt_fst (hz t ht)).deriv
  constructor
  · intro t ht
    have h1 : HasDerivAt (fun t => (z t).1) ((z t).2) t := hasDerivAt_fst (hz t ht)
    rwa [hvel t ht]
  · intro t ht
    have h2 : HasDerivAt (fun t => (z t).2)
        (-christoffel G (z t).1 (z t).2 (z t).2) t := hasDerivAt_snd (hz t ht)
    have hev : (fun u => deriv (fun s => (z s).1) u) =ᶠ[𝓝 t] (fun u => (z u).2) := by
      filter_upwards [hs.mem_nhds ht] with u hu
      exact hvel u hu
    refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [hvel t ht]

end Spray

/-! ## Local existence and uniqueness of the coordinate geodesic equation -/

section Existence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- The spray, viewed as a section of the tangent bundle of the model space `E × E`, is `C¹`. -/
theorem cmdiffAt_spraySection (G : CoordinateMetric E) (z₀ : E × E) :
    ContMDiffAt 𝓘(ℝ, E × E) (𝓘(ℝ, E × E)).tangent 1 (fun z : E × E =>
      (TotalSpace.mk' (E × E) z (spray G z) : TangentBundle 𝓘(ℝ, E × E) (E × E))) z₀ := by
  rw [Bundle.contMDiffAt_section]
  rw [contMDiffAt_iff_contDiffAt]
  have hfun : (fun z : E × E =>
      (trivializationAt (E × E) (TangentSpace 𝓘(ℝ, E × E)) z₀
        (TotalSpace.mk' (E × E) z (spray G z))).2) = fun z => spray G z := by
    funext z
    rw [trivializationAt_model_space_apply]
  rw [hfun]
  exact (contDiff_spray G).contDiffAt

set_option backward.isDefEq.respectTransparency false in
/-- **Existence of local integral curves of the geodesic spray.** For every initial position
and velocity in the chart there is a curve through it that is an `IsMIntegralCurveAt` of the
spray at time `0`. -/
theorem exists_isMIntegralCurveAt_spray (G : CoordinateMetric E) (z₀ : E × E) :
    ∃ z : ℝ → E × E, z 0 = z₀ ∧
      IsMIntegralCurveAt (I := 𝓘(ℝ, E × E)) z (spray G) 0 :=
  exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless (I := 𝓘(ℝ, E × E)) (M := E × E)
    0 (cmdiffAt_spraySection G z₀)

set_option backward.isDefEq.respectTransparency false in
/-- **Local existence for the second-order geodesic equation in coordinates.** There is `ε > 0`
and a curve `z = (x, x')` on `Ioo (-ε) ε` through `z₀` whose position component solves
`x'' = -Γ_x(x',x')` and which is an `IsMIntegralCurveOn` of the spray. -/
theorem exists_sprayCurveOn (G : CoordinateMetric E) (z₀ : E × E) :
    ∃ ε > 0, ∃ z : ℝ → E × E, z 0 = z₀ ∧
      IsSprayCurveOn G z (Ioo (-ε) ε) ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ, E × E)) z (spray G) (Ioo (-ε) ε) := by
  obtain ⟨z, hz0, hz⟩ := exists_isMIntegralCurveAt_spray G z₀
  obtain ⟨ε, hε, hOn⟩ := isMIntegralCurveAt_iff'.mp hz
  have hOn' : IsMIntegralCurveOn (I := 𝓘(ℝ, E × E)) z (spray G) (Metric.ball (0 : ℝ) ε) :=
    hOn
  refine ⟨ε, hε, z, hz0, ?_, ?_⟩
  · intro t ht
    have ht' : t ∈ Metric.ball (0 : ℝ) ε := by simpa [Real.ball_eq_Ioo] using ht
    exact (isMIntegralCurveOn_self_iff.mp hOn' t ht').hasDerivAt
      (Metric.isOpen_ball.mem_nhds ht')
  · simpa [Real.ball_eq_Ioo] using hOn'

set_option backward.isDefEq.respectTransparency false in
/-- **Local existence of a coordinate geodesic with prescribed initial position and velocity.**
This is the chart-level geodesic equation existence theorem: for every `x₀` and initial velocity
`v₀` there is `ε > 0` and `x : ℝ → E` with `x 0 = x₀`, `x'(0) = v₀`, solving the second-order
equation `x'' = -Γ_x(x',x')` on `Ioo (-ε) ε`. -/
theorem exists_coordinateGeodesic (G : CoordinateMetric E) (x₀ v₀ : E) :
    ∃ ε > 0, ∃ x : ℝ → E, x 0 = x₀ ∧ deriv x 0 = v₀ ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt x (deriv x t) t) ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (deriv x) (-(christoffel G (x t) (deriv x t) (deriv x t))) t := by
  obtain ⟨ε, hε, z, hz0, hz, -⟩ := exists_sprayCurveOn G (x₀, v₀)
  have hvel : ∀ t ∈ Ioo (-ε) ε, deriv (fun t => (z t).1) t = (z t).2 :=
    fun t ht => (hasDerivAt_fst (hz t ht)).deriv
  refine ⟨ε, hε, (fun t => (z t).1), ?_, ?_, ?_, ?_⟩
  · simp [hz0]
  · have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, by linarith⟩
    rw [hvel 0 h0]
    exact congrArg Prod.snd hz0
  · intro t ht
    have h1 : HasDerivAt (fun t => (z t).1) ((z t).2) t := hasDerivAt_fst (hz t ht)
    rwa [hvel t ht]
  · intro t ht
    have h2 : HasDerivAt (fun t => (z t).2)
        (-christoffel G (z t).1 (z t).2 (z t).2) t := hasDerivAt_snd (hz t ht)
    have hev : (fun u => deriv (fun s => (z s).1) u) =ᶠ[𝓝 t] (fun u => (z u).2) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
      exact hvel u hu
    refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
    simp only [hvel t ht]

omit [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Local uniqueness of the coordinate geodesic equation.** Two spray integral curves through
the same point at time `t₀` agree in a neighbourhood of `t₀`. -/
theorem sprayCurve_eventuallyEq (G : CoordinateMetric E) {z z' : ℝ → E × E} {t₀ : ℝ}
    (hz : IsMIntegralCurveAt (I := 𝓘(ℝ, E × E)) z (spray G) t₀)
    (hz' : IsMIntegralCurveAt (I := 𝓘(ℝ, E × E)) z' (spray G) t₀) (h : z t₀ = z' t₀) :
    z =ᶠ[𝓝 t₀] z' :=
  isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless (I := 𝓘(ℝ, E × E)) (M := E × E)
    (cmdiffAt_spraySection G (z t₀)) hz hz' h

omit [CompleteSpace E] in
set_option backward.isDefEq.respectTransparency false in
/-- **Uniqueness of the coordinate geodesic equation on an interval.** Two spray integral curves
on `Ioo a b` that agree at one point of the interval agree on the whole interval. -/
theorem sprayCurve_eqOn_Ioo (G : CoordinateMetric E) {z z' : ℝ → E × E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b)
    (hz : IsMIntegralCurveOn (I := 𝓘(ℝ, E × E)) z (spray G) (Ioo a b))
    (hz' : IsMIntegralCurveOn (I := 𝓘(ℝ, E × E)) z' (spray G) (Ioo a b))
    (h : z t₀ = z' t₀) : EqOn z z' (Ioo a b) := by
  refine isMIntegralCurveOn_Ioo_eqOn_of_contMDiff (I := 𝓘(ℝ, E × E)) (M := E × E)
    (v := spray G) ht₀ (fun t _ => BoundarylessManifold.isInteriorPoint) ?_ hz hz' h
  exact fun z => cmdiffAt_spraySection G z

end Existence

/-! ## The exponential-map germ -/

section ExpGerm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The exponential-map germ of the chart.** It is the position-and-velocity at half of the
chosen existence time of a spray solution through `z₀`. The germ structure is what is used:
`expGerm` depends only on the spray, is realized by a spray curve, and it fixes the zero section
(`expGerm_zero_velocity`). -/
noncomputable def expGerm (G : CoordinateMetric E) (z₀ : E × E) : E × E :=
  Classical.choose (Classical.choose_spec (exists_sprayCurveOn G z₀)).2
    (Classical.choose (exists_sprayCurveOn G z₀) / 2)

/-- The exponential-map germ is realized by a spray curve. -/
theorem expGerm_realized (G : CoordinateMetric E) (z₀ : E × E) :
    ∃ ε > 0, ∃ z : ℝ → E × E, z 0 = z₀ ∧ IsSprayCurveOn G z (Ioo (-ε) ε) ∧
      expGerm G z₀ = z (ε / 2) := by
  refine ⟨Classical.choose (exists_sprayCurveOn G z₀),
    (Classical.choose_spec (exists_sprayCurveOn G z₀)).1,
    Classical.choose (Classical.choose_spec (exists_sprayCurveOn G z₀)).2, ?_, ?_, rfl⟩
  · exact (Classical.choose_spec (Classical.choose_spec
      (exists_sprayCurveOn G z₀)).2).1
  · exact (Classical.choose_spec (Classical.choose_spec
      (exists_sprayCurveOn G z₀)).2).2.1

set_option backward.isDefEq.respectTransparency false in
/-- **The exponential-map germ fixes the zero section:** with zero initial velocity the germ is
the initial point. This is the coordinate form of `exp_x(0) = x`; it is proved from uniqueness
of the spray equation, not by evaluating a formula. -/
theorem expGerm_zero_velocity (G : CoordinateMetric E) (x : E) :
    expGerm G (x, 0) = (x, 0) := by
  have hε : 0 < Classical.choose (exists_sprayCurveOn G (x, 0)) :=
    (Classical.choose_spec (exists_sprayCurveOn G (x, 0))).1
  have hz0 : Classical.choose (Classical.choose_spec (exists_sprayCurveOn G (x, 0))).2 0 =
      (x, 0) :=
    (Classical.choose_spec (Classical.choose_spec (exists_sprayCurveOn G (x, 0))).2).1
  have hzOn : IsMIntegralCurveOn (I := 𝓘(ℝ, E × E))
      (Classical.choose (Classical.choose_spec (exists_sprayCurveOn G (x, 0))).2) (spray G)
      (Ioo (-(Classical.choose (exists_sprayCurveOn G (x, 0))))
        (Classical.choose (exists_sprayCurveOn G (x, 0)))) :=
    (Classical.choose_spec (Classical.choose_spec
      (exists_sprayCurveOn G (x, 0))).2).2.2
  have hconst : IsMIntegralCurveOn (I := 𝓘(ℝ, E × E)) (fun _ : ℝ => (x, 0)) (spray G)
      (Ioo (-(Classical.choose (exists_sprayCurveOn G (x, 0))))
        (Classical.choose (exists_sprayCurveOn G (x, 0)))) := by
    rw [isMIntegralCurveOn_self_iff]
    intro t ht
    rw [spray_zero_velocity]
    exact hasDerivWithinAt_const t _ (x, 0)
  have hmem : (0 : ℝ) ∈ Ioo (-(Classical.choose (exists_sprayCurveOn G (x, 0))))
      (Classical.choose (exists_sprayCurveOn G (x, 0))) := ⟨by linarith, by linarith⟩
  have heq := sprayCurve_eqOn_Ioo G hmem hzOn hconst (by rw [hz0])
  have hhalf : Classical.choose (exists_sprayCurveOn G (x, 0)) / 2 ∈
      Ioo (-(Classical.choose (exists_sprayCurveOn G (x, 0))))
        (Classical.choose (exists_sprayCurveOn G (x, 0))) := ⟨by linarith, by linarith⟩
  exact heq hhalf

end ExpGerm


/-! ## The chart metric of a Riemannian manifold

This section constructs, from a chart of an actual Riemannian manifold and the **pinned**
fiber metric `⟪·,·⟫` on `TangentSpace I`, the coordinate metric coefficients
`chartMetricForm e x u v = ⟪D_x u, D_x v⟫`, where `D_x = mfderiv 𝓘(ℝ,E) I e.symm x` is the
chart frame. Symmetry and positive semidefiniteness are proved; the remaining packaging step
(invertibility of the chart frame, giving `sharp`, and `C²` regularity of the coefficients) is
recorded honestly as a hypothesis in `exists_coordinateGeodesic_of_chartMetric`. -/

section Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The chart-local metric coefficients of a Riemannian manifold.** They are the pinned fiber
inner product evaluated on the chart frame `mfderiv 𝓘(ℝ,E) I e.symm x`. -/
noncomputable def chartMetricForm (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (e : OpenPartialHomeomorph M E) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  ((innerSL ℝ : TangentSpace I (e.symm x) →L[ℝ] TangentSpace I (e.symm x) →L[ℝ] ℝ)).comp
    (mfderiv 𝓘(ℝ, E) I e.symm x)

/-- **Chart-vs-manifold bridge (conditional).** If the chart metric coefficients are packaged as
a `CoordinateMetric` — i.e. the inverse metric `sharp` and the `C²`/`C¹` regularity are supplied
— then the whole constructed spray package (Koszul Christoffel symbol, torsion-freeness, metric
compatibility, local existence and uniqueness of the geodesic equation, exponential germ)
applies to the chart of the Riemannian manifold. The packaging hypothesis is the explicit
remaining gap: mathlib provides invertibility of `mfderiv` of `extChartAt` but has no
local-frame connection coefficients to identify `christoffel` with the pinned
`leviCitaConnection`, so the identification is *not* asserted. -/
theorem exists_coordinateGeodesic_of_chartMetric (I : ModelWithCorners ℝ E H) [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (e : OpenPartialHomeomorph M E)
    (G : CoordinateMetric E) (_hG : ∀ x u v : E, G.form x u v = chartMetricForm I e x u v)
    (x₀ v₀ : E) :
    ∃ ε > 0, ∃ x : ℝ → E, x 0 = x₀ ∧ deriv x 0 = v₀ ∧
      (∀ t ∈ Ioo (-ε) ε, HasDerivAt x (deriv x t) t) ∧
      ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (deriv x) (-(christoffel G (x t) (deriv x t) (deriv x t))) t :=
  exists_coordinateGeodesic G x₀ v₀

end Chart

end GeodesicSpray
end L4
end Poincare
