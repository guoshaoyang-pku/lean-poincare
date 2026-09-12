/-
Copyright (c) 2026 D13-manifold-ibp-volume-form. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D13-manifold-ibp-volume-form track (chart-independence of the gradient pairing)

# The gradient pairing is chart-independent on an overlapping atlas

`Riemannian.PullbackPairing` proves the chart-level invariance of the inverse-metric gradient
pairing under a congruence of the metric matrix by an invertible Jacobian. This module consumes
that theorem at the exact shape of the `(0,2)`-tensor law `OverlapAtlas.metric_transform` and
proves **chart-independence of `⟨∇u,∇v⟩_{g⁻¹}` on the overlap of two atlas charts**:

`⟨∇(u∘τ), ∇(v∘τ)⟩_{(g_j)⁻¹}(y) = ⟨∇u, ∇v⟩_{(g_i)⁻¹}(τ y)`,  `τ = transition i j`.

This is the first-order companion of the well-definedness of the Riemannian measure
(`ManifoldIBP.GlobalMeasure.chartMeasure_apply_eq`) and the missing analytic ingredient for
reassembling the pairings in the partition-of-unity decomposition of a global test function:
each chart-supported piece may compute `⟨∇u,∇v_j⟩` in its own chart, and the atlas law identifies
the results.

The Jacobian used by the atlas (`jacobianOf`, defined with `fderivWithin` on the overlap) is
identified with the chart-model Jacobian (`ChartMetric.jacobianMatrix`, defined with `fderiv`)
via `jacobianOf_eq_jacobianMatrix`, using openness of the overlap; the invertibility of the
Jacobian is *derived* from the tensor law and the positive definiteness of the two charts'
metrics.

There is no `sorry`, `axiom`, `unsafe`, `native_decide` or `proof_wanted` in this file.
-/
import Poincare.D13.Riemannian.PullbackPairing
import Poincare.D13.ManifoldIBP.GlobalMeasure

open scoped BigOperators Matrix Topology
open MeasureTheory Set Filter

noncomputable section

namespace Poincare.D13.ManifoldIBP

open Poincare.D12.VolumeIBP

variable {M : Type*} [MeasurableSpace M] {n : ℕ}

/-- **The atlas Jacobian is the chart-model Jacobian.** The atlas layer defines the Jacobian of a
transition with `fderivWithin` on the overlap; on a set that is a neighbourhood of the point this
is the ordinary derivative, hence the matrix used by `ChartMetric`. -/
lemma jacobianOf_eq_jacobianMatrix (τ : Vec (n + 1) → Vec (n + 1)) {W : Set (Vec (n + 1))}
    {y : Vec (n + 1)} (hW : W ∈ 𝓝 y) :
    jacobianOf τ W y = ChartMetric.jacobianMatrix τ y := by
  ext i j
  simp only [jacobianOf, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    fderivWithin_of_mem_nhds hW, ChartMetric.jacobianMatrix, Matrix.of_apply]
  rfl

namespace OverlapAtlas

/-- **Chart-independence of the inverse-metric gradient pairing.** On the overlap of the `i`-th
and `j`-th charts of an atlas whose overlaps are open, the pairing computed in the `j`-chart
coordinates via the transition `τ = transition i j` equals the pairing computed in the
`i`-chart coordinates at `τ y`. -/
theorem gradInnerInverse_chartTransition (A : OverlapAtlas M (n + 1))
    (hopen : ∀ i j, IsOpen (overlapOf A.chart A.source i j))
    (i j : ℕ) (y : Vec (n + 1)) (hy : y ∈ overlapOf A.chart A.source i j)
    (u v : Vec (n + 1) → ℝ)
    (hu : DifferentiableAt ℝ u (A.transition i j y))
    (hv : DifferentiableAt ℝ v (A.transition i j y)) :
    (A.metric j).gradInnerInverse (fun z => u (A.transition i j z))
        (fun z => v (A.transition i j z)) y
      = (A.metric i).gradInnerInverse u v (A.transition i j y) := by
  have hW : overlapOf A.chart A.source i j ∈ 𝓝 y := (hopen i j).mem_nhds hy
  have hτ : DifferentiableAt ℝ (A.transition i j) y :=
    (A.transition_diff i j y hy).differentiableAt hW
  have hlaw := A.metric_transform i j y hy
  rw [jacobianOf_eq_jacobianMatrix (A.transition i j) hW] at hlaw
  have hdet : (ChartMetric.jacobianMatrix (A.transition i j) y).det ≠ 0 := by
    intro h
    have hdet_eq : ((A.metric j).matrix y).det
        = (ChartMetric.jacobianMatrix (A.transition i j) y).det ^ 2
            * ((A.metric i).matrix (A.transition i j y)).det := by
      rw [hlaw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring
    have hpos := (A.metric j).det_ne_zero y
    rw [hdet_eq, h] at hpos
    norm_num at hpos
  exact Poincare.D13.Riemannian.gradInnerInverse_congruence (A.metric i) (A.metric j)
    (A.transition i j) y u v hτ hu hv hdet hlaw

/-- **Chart-independence with a coordinate multiplier.** The form used for a
partition-of-unity piece: multiplying the second function by a coordinate function `ψ` (the
partition-of-unity factor) preserves the identification of the pairing across charts. -/
theorem gradInnerInverse_chartTransition_mul (A : OverlapAtlas M (n + 1))
    (hopen : ∀ i j, IsOpen (overlapOf A.chart A.source i j))
    (i j : ℕ) (y : Vec (n + 1)) (hy : y ∈ overlapOf A.chart A.source i j)
    (u v : Vec (n + 1) → ℝ) (ψ : Vec (n + 1) → ℝ)
    (hu : DifferentiableAt ℝ u (A.transition i j y))
    (hψv : DifferentiableAt ℝ (fun z => ψ z * v z) (A.transition i j y)) :
    (A.metric j).gradInnerInverse (fun z => u (A.transition i j z))
        (fun z => ψ (A.transition i j z) * v (A.transition i j z)) y
      = (A.metric i).gradInnerInverse u (fun z => ψ z * v z) (A.transition i j y) :=
  A.gradInnerInverse_chartTransition hopen i j y hy u (fun z => ψ z * v z) hu hψv

end OverlapAtlas

end Poincare.D13.ManifoldIBP

/-! ## Axiom audit -/

#print axioms Poincare.D13.ManifoldIBP.jacobianOf_eq_jacobianMatrix
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.gradInnerInverse_chartTransition
#print axioms Poincare.D13.ManifoldIBP.OverlapAtlas.gradInnerInverse_chartTransition_mul
