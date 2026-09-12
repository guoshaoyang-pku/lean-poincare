import Mathlib

/-!
# Poincare.D9.Surfaces.Basic

**D9 / `D9-ricci-flow-surfaces`: the dimension-2 specialization interface.**

Ricci flow on surfaces is the one case where the curvature algebra is fully explicit:
for a surface `(M², g)` the Ricci tensor is a *pointwise scalar multiple* of the metric,

  `Ric = (scal / 2) g`      (`scal` = scalar curvature),

because the Ricci endomorphism has a single eigenvalue `scal/2` with multiplicity two.
This module records that specialization as an **interface identity** (`IsTwoDRicci`), the
**normalized flow equation** `∂ₜ g = (r - scal) g` with `r` the area-average scalar
curvature (`IsNormalizedFlow`), and the **area-preservation consequence**
(`area_preserved_of_isAreaAverage`): the area density evolves by the factor `r - scal`, and
the area-average condition makes the total area constant.

Everything here is finite-dimensional linear algebra plus one-dimensional calculus. The
matrix model `Mat2 = Matrix (Fin 2) (Fin 2) ℝ` is the local-coordinate shadow of the
surface: `g` is the metric matrix, `ric` the Ricci matrix, `det g` the area density.

## What is proved here (no hypotheses hidden in axioms)

* `isTwoDRicci_iff` — entrywise form of `Ric = (scal/2) g`.
* `trace_adjugate_mul_of_isTwoDRicci` — `tr(adj(g) · Ric) = scal · det g`, the exact
  dimension-2 statement that `scal` is the trace of the Ricci endomorphism.
* `trace_inv_mul_of_isTwoDRicci` — the same with `g⁻¹` when `det g` is a unit:
  `tr(g⁻¹ Ric) = scal`.
* `isTwoDRicci_symm` — the interface identity preserves symmetry.
* `hasDerivAt_det_of_normalizedFlow` — `d/dt det g = 2 (r - scal) det g` along the flow.
* `hasDerivAt_areaDensity_of_normalizedFlow` — `d/dt √(det g) = (r - scal) √(det g)`.
* `area_preserved_of_isAreaAverage` — the total area is constant when `r` is the
  area-average of `scal` (the Reynolds transport formula is an explicit hypothesis, never
  an axiom).
* `areaDensity_constant_of_scal_eq_r` — in the homogeneous case `scal = r` the area density
  is exactly constant.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Poincare
namespace D9
namespace Surfaces

/-- The `2 × 2` real matrices used as the local-coordinate model of a surface metric and
of its Ricci tensor. -/
abbrev Mat2 : Type := Matrix (Fin 2) (Fin 2) ℝ

/-! ## The 2D specialization interface `Ric = (scal/2) · g` -/

/-- **The 2D Ricci interface identity.** `ric` is the Ricci tensor of the surface metric
`g` with scalar curvature `scal` when `ric = (scal / 2) • g`. This is a `Prop` (an
interface identity), not an axiom: it is supplied as a hypothesis at every use site. -/
def IsTwoDRicci (ric g : Mat2) (scal : ℝ) : Prop :=
  ric = (scal / 2) • g

/-- The interface identity in entries: `Ric i j = (scal/2) g i j`. -/
theorem isTwoDRicci_iff (ric g : Mat2) (scal : ℝ) :
    IsTwoDRicci ric g scal ↔ ∀ i j, ric i j = (scal / 2) * g i j := by
  constructor
  · intro h i j
    rw [IsTwoDRicci] at h
    rw [h]
    simp
  · intro h
    rw [IsTwoDRicci]
    funext i j
    simpa using h i j

/-- The 2D interface identity preserves symmetry: if the metric matrix is symmetric then
so is the Ricci matrix. -/
theorem isTwoDRicci_symm {ric g : Mat2} {scal : ℝ} (h : IsTwoDRicci ric g scal)
    (hg : ∀ i j, g i j = g j i) : ∀ i j, ric i j = ric j i := by
  intro i j
  rw [(isTwoDRicci_iff ric g scal).mp h i j, (isTwoDRicci_iff ric g scal).mp h j i, hg j i]

/-- **Dimension-2 trace identity.** If `Ric = (scal/2) g` then
`tr(adj(g) · Ric) = scal · det g`. This is the exact statement that the scalar curvature
is the trace of the Ricci endomorphism, written without any invertibility hypothesis. -/
theorem trace_adjugate_mul_of_isTwoDRicci {ric g : Mat2} {scal : ℝ}
    (h : IsTwoDRicci ric g scal) :
    (g.adjugate * ric).trace = scal * g.det := by
  rw [IsTwoDRicci] at h
  rw [h, Matrix.mul_smul, Matrix.adjugate_mul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin]
  ring

/-- **Dimension-2 trace identity, inverse form.** If `det g` is a unit and
`Ric = (scal/2) g`, then `tr(g⁻¹ Ric) = scal`. -/
theorem trace_inv_mul_of_isTwoDRicci {ric g : Mat2} {scal : ℝ}
    (h : IsTwoDRicci ric g scal) (hg : IsUnit g.det) :
    (g⁻¹ * ric).trace = scal := by
  rw [IsTwoDRicci] at h
  rw [h, Matrix.mul_smul, Matrix.nonsing_inv_mul g hg, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin]
  ring

/-- The trace of the Ricci endomorphism determines the scalar curvature when the metric is
invertible: `tr(g⁻¹ Ric) = scal` is exactly the 2D specialization. -/
theorem scal_eq_trace_inv_mul_of_isTwoDRicci {ric g : Mat2} {scal : ℝ}
    (h : IsTwoDRicci ric g scal) (hg : IsUnit g.det) :
    scal = (g⁻¹ * ric).trace :=
  (trace_inv_mul_of_isTwoDRicci h hg).symm

/-! ## The normalized flow `∂ₜ g = (r - scal) g` -/

/-- **The normalized surface Ricci flow equation**, written componentwise:
`∂ₜ g i j = (r - scal) g i j`. The scalar function `r` is the normalization constant
(the area-average scalar curvature in the geometric reading). -/
def IsNormalizedFlow (g : ℝ → Mat2) (scal r : ℝ → ℝ) : Prop :=
  ∀ t i j, HasDerivAt (fun s => g s i j) ((r t - scal t) * g t i j) t

/-- **Evolution of the determinant (area density squared).** Along the normalized flow
`d/dt det g = 2 (r - scal) det g`. -/
theorem hasDerivAt_det_of_normalizedFlow (g : ℝ → Mat2) (scal r : ℝ → ℝ)
    (h : IsNormalizedFlow g scal r) (t : ℝ) :
    HasDerivAt (fun s => (g s).det) (2 * (r t - scal t) * (g t).det) t := by
  have hder : HasDerivAt (fun s => g s 0 0 * g s 1 1 - g s 0 1 * g s 1 0)
      ((r t - scal t) * g t 0 0 * g t 1 1 + g t 0 0 * ((r t - scal t) * g t 1 1) -
        ((r t - scal t) * g t 0 1 * g t 1 0 + g t 0 1 * ((r t - scal t) * g t 1 0))) t :=
    ((h t 0 0).mul (h t 1 1)).sub ((h t 0 1).mul (h t 1 0))
  have hfun : (fun s => (g s).det)
      = fun s => g s 0 0 * g s 1 1 - g s 0 1 * g s 1 0 := by
    funext s
    rw [Matrix.det_fin_two]
  rw [hfun]
  have hval : 2 * (r t - scal t) * (g t).det
      = (r t - scal t) * g t 0 0 * g t 1 1 + g t 0 0 * ((r t - scal t) * g t 1 1) -
        ((r t - scal t) * g t 0 1 * g t 1 0 + g t 0 1 * ((r t - scal t) * g t 1 0)) := by
    rw [Matrix.det_fin_two]
    ring
  rw [hval]
  exact hder

/-- The area density of a `2 × 2` metric: `√(det g)`. -/
def areaDensity (g : Mat2) : ℝ := Real.sqrt g.det

/-- **Evolution of the area density.** Along the normalized flow with positive-definite
metric, `d/dt √(det g) = (r - scal) √(det g)`. -/
theorem hasDerivAt_areaDensity_of_normalizedFlow (g : ℝ → Mat2) (scal r : ℝ → ℝ)
    (h : IsNormalizedFlow g scal r) (t : ℝ) (hdet : 0 < (g t).det) :
    HasDerivAt (fun s => areaDensity (g s)) ((r t - scal t) * areaDensity (g t)) t := by
  have hd := hasDerivAt_det_of_normalizedFlow g scal r h t
  have hne : (g t).det ≠ 0 := ne_of_gt hdet
  have hs := hd.sqrt hne
  have hsq : Real.sqrt ((g t).det) * Real.sqrt ((g t).det) = (g t).det := by
    rw [← sq, Real.sq_sqrt hdet.le]
  have hval : (2 * (r t - scal t) * (g t).det) / (2 * Real.sqrt ((g t).det))
      = (r t - scal t) * Real.sqrt ((g t).det) := by
    field_simp
    rw [sq, hsq]
  rw [hval] at hs
  simpa [areaDensity] using hs

/-! ## Area preservation -/

/-- **The area-average condition.** `r` is the area-average of `scal` against the area
density `ρ` when the weighted residual integrates to zero: `∫ (scal - r) ρ = 0`. -/
def IsAreaAverage {X : Type*} [MeasurableSpace X] (μ : Measure X) (ρ : X → ℝ)
    (scal r : X → ℝ) : Prop :=
  ∫ x, (scal x - r x) * ρ x ∂μ = 0

/-- The instantaneous rate of change of the area, `∫ (r - scal) ρ`, vanishes whenever `r`
is the area-average of `scal`. -/
theorem areaRate_eq_zero_of_isAreaAverage {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ρ : X → ℝ) (scal r : X → ℝ) (h : IsAreaAverage μ ρ scal r) :
    ∫ x, (r x - scal x) * ρ x ∂μ = 0 := by
  have hneg : (fun x => (r x - scal x) * ρ x)
      = fun x => -((scal x - r x) * ρ x) := by
    funext x
    ring
  rw [hneg, integral_neg, h, neg_zero]

/-- **The area-average scalar curvature.** `r = (∫ scal · ρ) / (∫ ρ)`, the average of the
scalar curvature against the area density `ρ`. -/
noncomputable def averageScalar {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ρ scal : X → ℝ) : ℝ :=
  (∫ x, scal x * ρ x ∂μ) / (∫ x, ρ x ∂μ)

/-- **The average scalar curvature satisfies the area-average condition.** If the area
`∫ ρ` is nonzero and the weighted integral `∫ scal · ρ` is integrable, then
`r = averageScalar μ ρ scal` has `∫ (scal - r) ρ = 0`. This is the precise sense in which
`r` is the average scalar curvature used in the normalized flow. -/
theorem isAreaAverage_averageScalar {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ρ scal : X → ℝ) (hρ : ∫ x, ρ x ∂μ ≠ 0) (hρi : Integrable ρ μ)
    (hspi : Integrable (fun x => scal x * ρ x) μ) :
    IsAreaAverage μ ρ scal (fun _ => averageScalar μ ρ scal) := by
  unfold IsAreaAverage averageScalar
  have h1 : ∫ x, (scal x - (∫ y, scal y * ρ y ∂μ) / (∫ y, ρ y ∂μ)) * ρ x ∂μ
      = ∫ x, (scal x * ρ x - ((∫ y, scal y * ρ y ∂μ) / (∫ y, ρ y ∂μ)) * ρ x) ∂μ := by
    congr 1
    funext x
    ring
  rw [h1, integral_sub hspi (hρi.const_mul _), integral_const_mul]
  field_simp
  ring

/-- The area-average scalar curvature is constant in time whenever the area `∫ ρ` and the
total scalar curvature `∫ scal · ρ` are constant. -/
theorem averageScalar_const_of_integrals {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (ρ scal : ℝ → X → ℝ)
    (hρ : ∀ t, ∫ x, ρ t x ∂μ = ∫ x, ρ 0 x ∂μ)
    (hscal : ∀ t, ∫ x, scal t x * ρ t x ∂μ = ∫ x, scal 0 x * ρ 0 x ∂μ) :
    ∀ t, averageScalar μ (ρ t) (scal t) = averageScalar μ (ρ 0) (scal 0) := by
  intro t
  unfold averageScalar
  rw [hρ t, hscal t]

/-- **Area preservation (stated consequence).** Suppose the total area `A` of a normalized
surface flow satisfies the transport formula `A' t = ∫ (r t - scal t) ρ t` (`ρ` the area
density), and suppose `r t` is the area-average of `scal t` for every `t`. Then `A` is
constant in time.

The Reynolds transport formula is carried as an explicit hypothesis of this theorem; it is
never asserted as an axiom. -/
theorem area_preserved_of_isAreaAverage {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A : ℝ → ℝ) (ρ : ℝ → X → ℝ) (scal r : ℝ → X → ℝ)
    (hA : ∀ t, HasDerivAt A (∫ x, (r t x - scal t x) * ρ t x ∂μ) t)
    (havg : ∀ t, IsAreaAverage μ (ρ t) (scal t) (r t)) :
    ∀ t, A t = A 0 := by
  have h0 : ∀ t, HasDerivAt A 0 t := by
    intro t
    have hz := areaRate_eq_zero_of_isAreaAverage μ (ρ t) (scal t) (r t) (havg t)
    simpa [hz] using hA t
  intro t
  exact is_const_of_deriv_eq_zero (fun s => (h0 s).differentiableAt)
    (fun s => (h0 s).deriv) t 0

/-- **Homogeneous area preservation.** If `scal = r` pointwise (the homogeneous ansatz),
then the area density is exactly constant along the flow. This is area preservation with no
transport hypothesis at all. -/
theorem areaDensity_constant_of_scal_eq_r (g : ℝ → Mat2) (scal r : ℝ → ℝ)
    (h : IsNormalizedFlow g scal r) (hr : ∀ t, scal t = r t) (hdet : ∀ t, 0 < (g t).det)
    (t : ℝ) : areaDensity (g t) = areaDensity (g 0) := by
  have h0 : ∀ t, HasDerivAt (fun s => areaDensity (g s)) 0 t := by
    intro t
    have hd := hasDerivAt_areaDensity_of_normalizedFlow g scal r h t (hdet t)
    rw [hr t, sub_self, zero_mul] at hd
    exact hd
  exact is_const_of_deriv_eq_zero (fun s => (h0 s).differentiableAt)
    (fun s => (h0 s).deriv) t 0

end Surfaces
end D9
end Poincare
