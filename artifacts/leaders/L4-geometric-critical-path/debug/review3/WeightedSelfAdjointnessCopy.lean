/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# L4 — positivity and self-adjointness for the D13 manifold-IBP layer

Status note (corrected after independent adversarial review of the first version): the D13
`ManifoldIBP` layer already proves the model-level Green identity
`OverlapAtlas.halfSpaceAtlas_greenIdentity`, which is consumed *inside* the D13 tree by
`halfSpaceAtlas_dirichletEnergy`.  The self-adjointness statement below is therefore a
**packaged corollary** of existing in-tree mathematics, not a new theorem; it is retained as
an L4-facing interface with an accurate label.

What is new in this file:

* `metricInnerInverse_self_nonneg` / `gradInnerInverse_self_nonneg` — **general** (proved):
  the inverse-metric pairing `∑ i j, g⁻¹ i j pᵢ pⱼ` is nonnegative on the diagonal, from the
  positive definiteness of the metric matrix (`ChartMetric.posDef`, `Matrix.PosDef.inv`).
  No such lemma existed in D12/D13 (checked by grep).
* `halfSpaceAtlas_dirichletEnergy_nonneg` — **model** (proved): the weighted Dirichlet
  energy `∫ |∇V|²_{g⁻¹} e^{-F} dμ` of the partial half-space atlas is nonnegative, and the
  integrand is integrable (the latter half is D13's
  `halfSpaceAtlas_integrable_dirichlet`).  D13 proves the Dirichlet *identity* and the
  integrability but not the *sign*; this is a constructed estimate on the glued measure.
* `halfSpaceAtlas_weightedLaplacian_selfAdjoint` — **model, packaged corollary** (proved,
  from `halfSpaceAtlas_greenIdentity`): the drift Laplacian is self-adjoint on the weighted
  measure `e^{-F} dμ`.

Independent verification of the D13 headline layer (axiom cones re-derived from outside the
D13 tree) is in `Poincare/L4/ManifoldIBP/D13HeadlineAudit.lean`.
-/
import Poincare.D13.ManifoldIBP.PartialChartModelPOU

open scoped BigOperators ENNReal NNReal Topology Matrix Function ContDiff
open MeasureTheory Set Filter Metric Function

namespace Poincare.L4.ManifoldIBP

open Poincare.D12.VolumeIBP Poincare.D13.ManifoldIBP

/-! ## 1. Positive semidefiniteness of the inverse-metric pairing -/

/-- **The inverse metric pairing is nonnegative on the diagonal.**  `∑ i j, g⁻¹ i j pᵢ pⱼ ≥ 0`
because `g⁻¹` is positive definite: the metric matrix is positive definite
(`ChartMetric.posDef`) and the inverse of a positive definite matrix is positive definite
(`Matrix.PosDef.inv`). -/
theorem metricInnerInverse_self_nonneg {n : ℕ} (G : ChartMetric (n + 1)) (x : Vec (n + 1))
    (p : Vec (n + 1)) : 0 ≤ G.metricInnerInverse x p p := by
  have hpd : (G.invMatrix x).PosDef := by
    have hmat : (G.matrix x).PosDef := by simpa [ChartMetric.matrix] using G.posDef x
    simpa [ChartMetric.invMatrix] using hmat.inv
  have hsum : G.metricInnerInverse x p p = p ⬝ᵥ ((G.invMatrix x).mulVec p) := by
    unfold ChartMetric.metricInnerInverse
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum]
  simpa using hpd.posSemidef.dotProduct_mulVec_nonneg p

/-- **The gradient pairing is nonnegative on the diagonal:**
`|∇u|²_{g⁻¹} = ⟨∇u, ∇u⟩_{g⁻¹} ≥ 0` pointwise. -/
theorem gradInnerInverse_self_nonneg {n : ℕ} (G : ChartMetric (n + 1)) (u : Vec (n + 1) → ℝ)
    (x : Vec (n + 1)) : 0 ≤ G.gradInnerInverse u u x := by
  unfold ChartMetric.gradInnerInverse
  exact metricInnerInverse_self_nonneg G x _

/-! ## 2. Nonnegativity of the weighted Dirichlet energy -/

/-- **The weighted Dirichlet energy is nonnegative and integrable.**  On the glued global
measure of the concrete partial half-space atlas, `∫ |∇V|²_{g⁻¹} e^{-F} dμ ≥ 0`; the
integrand is integrable by D13's `halfSpaceAtlas_integrable_dirichlet`.  This is the sign
statement missing from the D13 layer (which proves the identity `∫ (Δ_F V)·V = −∫ |∇V|²`
and integrability). -/
theorem halfSpaceAtlas_dirichletEnergy_nonneg {n : ℕ} (G : ChartMetric (n + 1))
    (F V : Vec (n + 1) → ℝ) (hF : ContDiff ℝ 2 F) (hV : ContDiff ℝ 2 V)
    (hVc : HasCompactSupport V) (hVsupp : tsupport V ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    Integrable (fun m => G.gradInnerInverse V V m)
        (((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F)) ∧
      0 ≤ ∫ m, G.gradInnerInverse V V m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F)) :=
  ⟨(OverlapAtlas.halfSpaceAtlas_integrable_dirichlet G F V hF hV hVc hVsupp).2,
    integral_nonneg (fun m => gradInnerInverse_self_nonneg G V m)⟩

/-! ## 3. Self-adjointness of the drift Laplacian (packaged corollary) -/

/-- **Self-adjointness of the drift Laplacian on the half-space atlas measure.**  For `C²`
data and compactly supported `u`, `v` with topological supports in the base chart source,
`∫ (Δ_F u) v e^{-F} dμ = ∫ (Δ_F v) u e^{-F} dμ`.

This is the self-adjointness form of the pre-existing D13 Green identity
`OverlapAtlas.halfSpaceAtlas_greenIdentity` (only the commutative rearrangement
`u · Δ_F v = Δ_F v · u` of the right-hand side is added); it is recorded as an L4 interface,
not claimed as new mathematical content. -/
theorem halfSpaceAtlas_weightedLaplacian_selfAdjoint {n : ℕ} (G : ChartMetric (n + 1))
    (F u v : Vec (n + 1) → ℝ)
    (hF : ContDiff ℝ 2 F) (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v)
    (huc : HasCompactSupport u) (husupp : tsupport u ⊆ {y : Vec (n + 1) | y 0 < 1})
    (hvc : HasCompactSupport v) (hvsupp : tsupport v ⊆ {y : Vec (n + 1) | y 0 < 1}) :
    ∫ m, G.driftLaplacian F u m * v m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F))
      = ∫ m, G.driftLaplacian F v m * u m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F)) := by
  have h := OverlapAtlas.halfSpaceAtlas_greenIdentity (n := n) G F u v hF hu hv huc hvc husupp hvsupp
  rwa [show (∫ m, u m * G.driftLaplacian F v m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F)))
      = ∫ m, G.driftLaplacian F v m * u m
        ∂(((OverlapAtlas.hsAtlas G).globalMeasure volume).withDensity
          ((OverlapAtlas.hsAtlas G).weight F)) from
    integral_congr_ae (ae_of_all _ fun m => mul_comm _ _)] at h

end Poincare.L4.ManifoldIBP
