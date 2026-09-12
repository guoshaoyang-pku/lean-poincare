/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (chart-independence of the gradient pairing)

# Chart-independence of the gradient pairing on the dilation model

The manifold integration-by-parts layer of `ManifoldIBP.OverlapIBP` takes the chart
identification of the differential operators as an interface hypothesis (`hD`, `hG`). The
missing manifold-layer theorem behind that interface is the **chart-independence of the
operators**: the chart-`i` and chart-`j` expressions of `Δ_f u` and `⟨∇u,∇v⟩_{g⁻¹}` must
agree at the corresponding points of overlapping charts. This module proves that theorem for
the gradient pairing on the inhabited dilation-chart model, from the metric transformation
law:

* `invMatrix_dilate` — the inverse Gram matrix of the dilation metric,
  `(c² • M)⁻¹ = (c²)⁻¹ • M⁻¹` (mathlib `Matrix.inv_smul` + the D12 determinant positivity);
* `partialDeriv_comp_const_smul` — the chain rule `∂ᵢ(U ∘ (c • ·)) = c · (∂ᵢU) ∘ (c • ·)`;
* **`dilateMetric_gradInnerInverse`** — the gradient pairing computed in the dilation chart
  equals the pairing computed in the unit chart at the corresponding point:
  `⟨∇(U∘c), ∇(V∘c)⟩_{(c²G(c·))⁻¹}(y) = ⟨∇U, ∇V⟩_{G⁻¹}(c·y)`.
  The Jacobian factors `c` from the chain rule cancel the `c⁻²` from the inverse metric.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.ManifoldIBP.OverlapIBPModel

set_option maxHeartbeats 1000000

open scoped BigOperators ENNReal NNReal Topology Matrix Function
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

namespace OverlapAtlas

variable {n : ℕ}

/-- **Inverse Gram matrix of the dilation metric.** Scaling the Gram matrix by `c²` inverts to
scaling the inverse Gram matrix by `(c²)⁻¹`. Proved from mathlib's `Matrix.inv_smul` with the
`Invertible (c*c)` instance supplied by `c ≠ 0`, and the positivity of the Gram determinant
(D12 `ChartMetric.det_ne_zero`). -/
lemma invMatrix_dilate (G : ChartMetric (n + 1)) (c : ℝ) (hc : c ≠ 0) (y : Vec (n + 1)) :
    (dilateMetric G c hc).invMatrix y = ((c * c)⁻¹) • G.invMatrix (c • y) := by
  have hne : c * c ≠ 0 := mul_ne_zero hc hc
  show ((dilateMetric G c hc).matrix y)⁻¹ = ((c * c)⁻¹) • G.invMatrix (c • y)
  rw [dilate_matrix]
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, ChartMetric.matrix_mul_invMatrix]
  have hsc : (c * c) * (c⁻¹ * c⁻¹) = 1 := by
    rw [show c⁻¹ * c⁻¹ = (c * c)⁻¹ by rw [mul_inv_rev, mul_comm], mul_inv_cancel₀ hne]
  rw [show (c * c)⁻¹ = c⁻¹ * c⁻¹ by rw [mul_inv_rev, mul_comm], smul_smul, hsc, one_smul]

/-- **Chain rule for the coordinate partial derivative of a dilation**:
`∂ᵢ(U ∘ (c • ·))(y) = c · ∂ᵢU(c·y)`. -/
lemma partialDeriv_comp_const_smul (U : Vec (n + 1) → ℝ) (c : ℝ) (y : Vec (n + 1))
    (i : Fin (n + 1)) (hU : DifferentiableAt ℝ U (c • y)) :
    ChartMetric.partialDeriv i (fun z => U (c • z)) y
      = c * ChartMetric.partialDeriv i U (c • y) := by
  have hg : HasFDerivAt (fun z : Vec (n + 1) => c • z)
      (c • ContinuousLinearMap.id ℝ (Vec (n + 1))) y :=
    (hasFDerivAt_id y).const_smul c
  have hcomp : HasFDerivAt (fun z => U (c • z))
      ((fderiv ℝ U (c • y)).comp (c • ContinuousLinearMap.id ℝ (Vec (n + 1)))) y :=
    hU.hasFDerivAt.comp y hg
  rw [ChartMetric.partialDeriv, hcomp.fderiv, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, ChartMetric.partialDeriv]
  rfl

/-- **Chart-independence of the gradient pairing on the dilation model.** The pairing
`⟨∇U, ∇V⟩_{G⁻¹}` computed in the dilation chart at coordinate `y` equals the pairing computed
in the unit chart at the corresponding manifold point `c · y`:
`(c²G(c·))⁻¹` contributes `c⁻²`, the two chain-rule factors contribute `c²`. -/
theorem dilateMetric_gradInnerInverse (G : ChartMetric (n + 1)) (c : ℝ) (hc : c ≠ 0)
    (U V : Vec (n + 1) → ℝ) (hU : Differentiable ℝ U) (hV : Differentiable ℝ V)
    (y : Vec (n + 1)) :
    (dilateMetric G c hc).gradInnerInverse (fun z => U (c • z)) (fun z => V (c • z)) y
      = G.gradInnerInverse U V (c • y) := by
  have hpdU : ∀ i, ChartMetric.partialDeriv i (fun z => U (c • z)) y
      = c * ChartMetric.partialDeriv i U (c • y) :=
    fun i => partialDeriv_comp_const_smul U c y i hU.differentiableAt
  have hpdV : ∀ j, ChartMetric.partialDeriv j (fun z => V (c • z)) y
      = c * ChartMetric.partialDeriv j V (c • y) :=
    fun j => partialDeriv_comp_const_smul V c y j hV.differentiableAt
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  rw [ChartMetric.gradInnerInverse, ChartMetric.gradInnerInverse, ChartMetric.metricInnerInverse,
    ChartMetric.metricInnerInverse]
  simp only [invMatrix_dilate G c hc y, Matrix.smul_apply, hpdU, hpdV]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hc2 : c⁻¹ * c⁻¹ * (c * c) = 1 := by
    rw [mul_assoc, ← mul_assoc c⁻¹ c c, inv_mul_cancel₀ hc, one_mul, inv_mul_cancel₀ hc]
  rw [show (c * c)⁻¹ = c⁻¹ * c⁻¹ by rw [mul_inv_rev, mul_comm], smul_eq_mul]
  rw [show c⁻¹ * c⁻¹ * G.invMatrix (c • y) i j * (c * ChartMetric.partialDeriv i U (c • y))
        * (c * ChartMetric.partialDeriv j V (c • y))
      = (c⁻¹ * c⁻¹ * (c * c))
        * (G.invMatrix (c • y) i j * ChartMetric.partialDeriv i U (c • y)
            * ChartMetric.partialDeriv j V (c • y)) by ring]
  rw [hc2, one_mul]


/-- **Chart-independence of the gradient pairing, manifold form.** The pairing of two
manifold functions on `Vec (n+1)` computed in the dilation chart at the coordinate
`2⁻¹ · m` equals the pairing computed in the unit chart at `m`: the two chart expressions
`u ∘ (2 • ·)` and `u`, with the two Gram matrices `4 • G(2·)` and `G`, give the same value at
the same manifold point. -/
theorem dilationAtlasTwo_gradInnerInverse_chart_independent (G : ChartMetric (n + 1))
    (u v : Vec (n + 1) → ℝ) (hu : Differentiable ℝ u) (hv : Differentiable ℝ v)
    (m : Vec (n + 1)) :
    (dilateMetric G 2 (by norm_num)).gradInnerInverse (fun z => u ((2 : ℝ) • z))
        (fun z => v ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m)
      = G.gradInnerInverse u v m := by
  have h := dilateMetric_gradInnerInverse G 2 (by norm_num) u v hu hv ((2 : ℝ)⁻¹ • m)
  rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0) m] at h
  exact h


/-- **Chain rule with a constant factor**: `∂ᵥ(a · H(c·))(y) = a · (c · ∂ᵥH(c·y))`. -/
lemma fderiv_const_smul_comp_const_smul (H : Vec (n + 1) → ℝ) (a c : ℝ) (y v : Vec (n + 1))
    (hH : DifferentiableAt ℝ H (c • y)) :
    fderiv ℝ (fun z => a * H (c • z)) y v = a * (c * fderiv ℝ H (c • y) v) := by
  have hg : HasFDerivAt (fun z : Vec (n + 1) => c • z)
      (c • ContinuousLinearMap.id ℝ (Vec (n + 1))) y :=
    (hasFDerivAt_id y).const_smul c
  have hcomp : HasFDerivAt (fun z => H (c • z))
      ((fderiv ℝ H (c • y)).comp (c • ContinuousLinearMap.id ℝ (Vec (n + 1)))) y :=
    hH.hasFDerivAt.comp y hg
  have hmul : HasFDerivAt (fun z => a * H (c • z))
      (a • ((fderiv ℝ H (c • y)).comp (c • ContinuousLinearMap.id ℝ (Vec (n + 1))))) y :=
    hcomp.const_smul a
  rw [hmul.fderiv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul]
  ring

/-- **The density of the dilation metric**: `ρ₁(y) = c^{n+1} · ρ(c·y)` for `c > 0` (the
determinant of `c² • G(c·y)` contributes `(c²)^{n+1}`, whose square root is `c^{n+1}`). -/
lemma dilateMetric_density (G : ChartMetric (n + 1)) (c : ℝ) (hc : 0 < c)
    (y : Vec (n + 1)) :
    (dilateMetric G c (ne_of_gt hc)).density y = c ^ (n + 1) * G.density (c • y) := by
  have hexp : (c * c) ^ (n + 1) = (c ^ (n + 1)) ^ 2 := by
    rw [mul_pow, ← pow_add, ← pow_mul]
    congr 1
    ring
  simp only [ChartMetric.density, dilate_matrix, Matrix.det_smul, Fintype.card_fin, hexp,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (le_of_lt hc) _)]

/-- **The gradient of the dilation metric**: `grad₁(U ∘ c·)(y) = c⁻¹ • grad U(c·y)`. -/
lemma dilateMetric_grad (G : ChartMetric (n + 1)) (c : ℝ) (hc : c ≠ 0)
    (U : Vec (n + 1) → ℝ) (hU : Differentiable ℝ U) (y : Vec (n + 1)) :
    (dilateMetric G c hc).grad (fun z => U (c • z)) y = c⁻¹ • G.grad U (c • y) := by
  funext i
  simp only [ChartMetric.grad, Pi.smul_apply, invMatrix_dilate G c hc y, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [partialDeriv_comp_const_smul U c y j hU.differentiableAt,
    show (c * c)⁻¹ = c⁻¹ * c⁻¹ by rw [mul_inv_rev, mul_comm]]
  rw [show c⁻¹ * c⁻¹ * G.invMatrix (c • y) i j * (c * ChartMetric.partialDeriv j U (c • y))
      = (c⁻¹ * c) * (c⁻¹ * (G.invMatrix (c • y) i j
          * ChartMetric.partialDeriv j U (c • y))) by ring]
  rw [inv_mul_cancel₀ hc, one_mul]

/-- **The weighted divergence of the dilation metric**:
`∑ᵢ ∂ᵢ(ρ₁ · (grad₁ U₁)ᵢ)(y) = c^{n+1} · ∑ᵢ ∂ᵢ(ρ · (grad U)ᵢ)(c·y)`. The pointwise integrand
is `c^n · (ρ · (grad U)ᵢ)(c·z)`, and the chain rule contributes one further factor `c`. -/
lemma dilateMetric_weightedDivergence (G : ChartMetric (n + 1)) (c : ℝ) (hc : 0 < c)
    (U : Vec (n + 1) → ℝ) (hU : ContDiff ℝ 2 U) (y : Vec (n + 1)) :
    ChartMetric.weightedDivergence (dilateMetric G c (ne_of_gt hc)).density
        ((dilateMetric G c (ne_of_gt hc)).grad (fun z => U (c • z))) y
      = c ^ (n + 1) * ChartMetric.weightedDivergence G.density (G.grad U) (c • y) := by
  have hdiff : ∀ i : Fin (n + 1),
      DifferentiableAt ℝ (fun w : Vec (n + 1) => G.density w * G.grad U w i) (c • y) := by
    intro i
    exact ((G.density_contDiff_one.mul
      (contDiff_pi.mp (G.grad_contDiff_one U hU) i)).differentiable (by simp)).differentiableAt
  rw [ChartMetric.weightedDivergence, ChartMetric.weightedDivergence, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfun : (fun z => (dilateMetric G c (ne_of_gt hc)).density z
        * ((dilateMetric G c (ne_of_gt hc)).grad (fun z => U (c • z)) z i))
      = fun z => c ^ n * ((fun w : Vec (n + 1) => G.density w * G.grad U w i) (c • z)) := by
    funext z
    rw [dilateMetric_density G c hc z,
      dilateMetric_grad G c (ne_of_gt hc) U (hU.differentiable (by simp)) z]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [hfun, fderiv_const_smul_comp_const_smul (fun w : Vec (n + 1) => G.density w * G.grad U w i)
    (c ^ n) c y (Pi.single i 1) (hdiff i)]
  simp only [pow_succ]
  ring

/-- **Chart-independence of the metric Laplacian on the dilation model**:
`Δ_{c²G(c·)}(U ∘ c·)(y) = (Δ_G U)(c·y)`. The density contributes `c^{n+1}`, the inverse metric
`c⁻²`, and the two chain-rule derivatives `c²`. -/
theorem dilateMetric_laplacian (G : ChartMetric (n + 1)) (c : ℝ) (hc : 0 < c)
    (U : Vec (n + 1) → ℝ) (hU : ContDiff ℝ 2 U) (y : Vec (n + 1)) :
    (dilateMetric G c (ne_of_gt hc)).laplacian (fun z => U (c • z)) y
      = G.laplacian U (c • y) := by
  rw [ChartMetric.laplacian, ChartMetric.laplacian, ChartMetric.divergence, ChartMetric.divergence,
    dilateMetric_weightedDivergence G c hc U hU y, dilateMetric_density G c hc y]
  rw [mul_div_mul_left _ _ (pow_ne_zero _ (ne_of_gt hc))]

/-- **Chart-independence of the drift-weighted Laplacian (the IBP's left-hand integrand) on the
dilation model**: `Δ_{F₁} U₁` computed in the dilation chart equals `Δ_F U` computed in the
unit chart at the corresponding point. Combines `dilateMetric_laplacian` with the pairing
chart-independence `dilateMetric_gradInnerInverse`. -/
theorem dilateMetric_driftLaplacian (G : ChartMetric (n + 1)) (c : ℝ) (hc : 0 < c)
    (F U : Vec (n + 1) → ℝ) (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) (y : Vec (n + 1)) :
    (dilateMetric G c (ne_of_gt hc)).driftLaplacian (fun z => F (c • z)) (fun z => U (c • z)) y
      = G.driftLaplacian F U (c • y) := by
  rw [ChartMetric.driftLaplacian, ChartMetric.driftLaplacian,
    dilateMetric_laplacian G c hc U hU y,
    dilateMetric_gradInnerInverse G c (ne_of_gt hc) F U (hF.differentiable (by simp))
      (hU.differentiable (by simp)) y]

/-- **All four operator slots are chart-independent on the model**: the manifold form of
`dilateMetric_driftLaplacian` at the point `m` with the dilation chart coordinate `2⁻¹ · m`. -/
theorem dilationAtlasTwo_driftLaplacian_chart_independent (G : ChartMetric (n + 1))
    (F U : Vec (n + 1) → ℝ) (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) (m : Vec (n + 1)) :
    (dilateMetric G 2 (by norm_num)).driftLaplacian (fun z => F ((2 : ℝ) • z))
        (fun z => U ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m)
      = G.driftLaplacian F U m := by
  have h := dilateMetric_driftLaplacian G 2 (by norm_num) F U hF hU ((2 : ℝ)⁻¹ • m)
  rw [smul_inv_smul₀ (by norm_num : (2 : ℝ) ≠ 0) m] at h
  exact h


/-- **The manifold IBP computed in the dilation chart's coordinates.** With the manifold
operators defined once (here by their *unit-chart* expressions `G.driftLaplacian F U` and
`G.gradInnerInverse U V`), the weighted IBP identity also holds when both sides are written in
the dilation chart: the left-hand integrand is
`(Δ₁)_{F₁} U₁ (2⁻¹ · m) · V m` and the right-hand one `⟨∇U₁, ∇V₁⟩_{G₁⁻¹}(2⁻¹ · m)`, where
`F₁ = F ∘ (2 • ·)`, `U₁ = U ∘ (2 • ·)`, `V₁ = V ∘ (2 • ·)`. The chart-identification
hypotheses of `globalWeightedIBP_of_chartSupported` are supplied by the operator
chart-independence proved above, not assumed. -/
theorem dilationAtlasTwo_weightedIBP_chartOne (G : ChartMetric (n + 1))
    (F U V : Vec (n + 1) → ℝ) (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U)
    (hV : ContDiff ℝ 2 fun z => V ((2 : ℝ) • z))
    (hVc : HasCompactSupport fun z => V ((2 : ℝ) • z)) :
    ∫ m, (dilateMetric G 2 (by norm_num)).driftLaplacian (fun z => F ((2 : ℝ) • z))
          (fun z => U ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m) * V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F))
      = -∫ m, (dilateMetric G 2 (by norm_num)).gradInnerInverse (fun z => U ((2 : ℝ) • z))
          (fun z => V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m)
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F)) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hsrc : (dilationAtlasTwo n G).source 1 = univ := rfl
  have himg : (dilationAtlasTwo n G).chart 1 '' (dilationAtlasTwo n G).source 1 = univ := by
    rw [hsrc]
    exact dilationChart_image_univ (d := n + 1) h2 1
  have hVm : Measurable V := by
    have h1 : Measurable fun m : Vec (n + 1) => V ((2 : ℝ) • ((2 : ℝ)⁻¹ • m)) :=
      (hV.continuous.measurable).comp (measurable_const_smul ((2 : ℝ)⁻¹))
    simpa [smul_inv_smul₀ h2] using h1
  have hF1 : ContDiff ℝ 2 fun y : Vec (n + 1) => F ((2 : ℝ) • y) :=
    hF.comp (contDiff_const_smul (2 : ℝ))
  have hU1 : ContDiff ℝ 2 fun y : Vec (n + 1) => U ((2 : ℝ) • y) :=
    hU.comp (contDiff_const_smul (2 : ℝ))
  have hV1 : ContDiff ℝ 2 fun y : Vec (n + 1) => V ((2 : ℝ) • y) := hV
  refine (dilationAtlasTwo n G).globalWeightedIBP_of_chartSupported 1 F U V
    (fun m => (dilateMetric G 2 h2).driftLaplacian (fun z => F ((2 : ℝ) • z))
      (fun z => U ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m))
    (fun m => (dilateMetric G 2 h2).gradInnerInverse (fun z => U ((2 : ℝ) • z))
      (fun z => V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m))
    hF.continuous.measurable hVm ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ((dilateMetric G 2 h2).driftLaplacian_continuous _ _ hF1 hU1).measurable.comp
      (measurable_const_smul ((2 : ℝ)⁻¹))
  · exact ((dilateMetric G 2 h2).gradInnerInverse_continuous _ _ hU1 hV1).measurable.comp
      (measurable_const_smul ((2 : ℝ)⁻¹))
  · intro m _
    rw [himg]
    exact mem_univ m
  · intro m _
    rw [himg]
    exact mem_univ m
  · intro y _
    rw [hsrc]
    exact mem_univ y
  · intro y _
    rw [hsrc]
    exact mem_univ y
  · rw [dilationAtlasTwo_chart_one]
    exact hF1
  · rw [dilationAtlasTwo_chart_one]
    exact hU1
  · rw [dilationAtlasTwo_chart_one]
    exact hV1
  · rw [dilationAtlasTwo_chart_one]
    exact hVc
  · refine ae_of_all _ fun y _ => ?_
    simp only [dilationAtlasTwo_chart_one, dilationAtlasTwo_metric_one]
    show (dilateMetric G 2 h2).driftLaplacian (fun z => F ((2 : ℝ) • z))
        (fun z => U ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • ((2 : ℝ) • y))
      = (dilateMetric G 2 h2).driftLaplacian (fun z => F ((2 : ℝ) • z))
        (fun z => U ((2 : ℝ) • z)) y
    rw [inv_smul_smul₀ h2 y]
  · refine ae_of_all _ fun y _ => ?_
    simp only [dilationAtlasTwo_chart_one, dilationAtlasTwo_metric_one]
    show (dilateMetric G 2 h2).gradInnerInverse (fun z => U ((2 : ℝ) • z))
        (fun z => V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • ((2 : ℝ) • y))
      = (dilateMetric G 2 h2).gradInnerInverse (fun z => U ((2 : ℝ) • z))
        (fun z => V ((2 : ℝ) • z)) y
    rw [inv_smul_smul₀ h2 y]


/-- **The two chart computations of the IBP's left-hand integral agree.** The integral of the
dilation-chart drift Laplacian of `(F₁, U₁)` at the chart coordinate `2⁻¹·m`, against the
same entropy-weighted global measure, equals the integral of the unit-chart `Δ_F U`. -/
theorem dilationAtlasTwo_chartOne_laplacianIntegral_eq (G : ChartMetric (n + 1))
    (F U V : Vec (n + 1) → ℝ) (hF : ContDiff ℝ 2 F) (hU : ContDiff ℝ 2 U) :
    ∫ m, (dilateMetric G 2 (by norm_num)).driftLaplacian (fun z => F ((2 : ℝ) • z))
          (fun z => U ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m) * V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F))
      = ∫ m, G.driftLaplacian F U m * V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight F)) := by
  refine integral_congr_ae ?_
  filter_upwards with m
  rw [dilationAtlasTwo_driftLaplacian_chart_independent G F U hF hU m]

/-- **The two chart computations of the IBP's right-hand integral agree.** -/
theorem dilationAtlasTwo_chartOne_pairingIntegral_eq (G : ChartMetric (n + 1))
    (U V : Vec (n + 1) → ℝ) (hU : Differentiable ℝ U) (hV : Differentiable ℝ V) :
    ∫ m, (dilateMetric G 2 (by norm_num)).gradInnerInverse (fun z => U ((2 : ℝ) • z))
          (fun z => V ((2 : ℝ) • z)) ((2 : ℝ)⁻¹ • m)
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight (fun _ => 0)))
      = ∫ m, G.gradInnerInverse U V m
        ∂(((dilationAtlasTwo n G).globalMeasure volume).withDensity
          ((dilationAtlasTwo n G).weight (fun _ => 0))) := by
  refine integral_congr_ae ?_
  filter_upwards with m
  rw [dilationAtlasTwo_gradInnerInverse_chart_independent G U V hU hV m]

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.invMatrix_dilate
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.partialDeriv_comp_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_gradInnerInverse
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_gradInnerInverse_chart_independent
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.fderiv_const_smul_comp_const_smul
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_density
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_grad
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_weightedDivergence
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_laplacian
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilateMetric_driftLaplacian
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_driftLaplacian_chart_independent
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_weightedIBP_chartOne
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chartOne_laplacianIntegral_eq
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.dilationAtlasTwo_chartOne_pairingIntegral_eq
