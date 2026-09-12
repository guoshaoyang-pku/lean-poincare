/-
Copyright (c) 2026 Poincare Longrun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D12-heat-semigroup-analysis)
-/

import Poincare.D12.HeatSemigroup.StrongContinuity

/-!
# Poincare.D12.HeatSemigroup.ManifoldObligations

**D12 heat-semigroup analysis, part 6: explicit proof obligations for the next compact-manifold
construction.**

The Euclidean model theorem is now checked (positivity, L∞ contraction, L1 contraction, strong
continuity at `0` for continuous integrable test functions, and the C¹ smoothing lemma). This
module records, as *obligations* (plain `Prop` definitions, nothing assumed), the exact statements
that a compact-manifold construction must discharge to lift the Euclidean semigroup analysis. It
claims nothing: every definition here is an obligation to be proved later, and no Euclidean
result below is labelled as a manifold heat-kernel existence theorem.
-/

open MeasureTheory Filter
open scoped Topology

namespace Poincare.D12.HeatSemigroup

/-! ## The manifold-side target statements (obligations, not claims) -/

/-- **Obligation**: for a compact Riemannian manifold (represented as a type `M` with a Borel
space, a reference measure `μ`, a distance `d`, a dimension `dim` and a Laplace operator), a
heat-kernel datum satisfying the D11 core axioms with Gaussian bounds `C_up, c_up, C_lo, c_lo`.
This is the interface the Euclidean model instantiated; the compact case must supply the
existence proof, not the interface. -/
def CompactManifoldHeatKernelCoreObligation (M : Type*) [TopologicalSpace M] [MeasurableSpace M] :
    Prop :=
  ∃ (volume : Measure M) (dist : M → M → ℝ) (dim C_up c_up C_lo c_lo : ℝ)
    (kernel : M → M → ℝ → ℝ) (laplacian : (M → ℝ) →ₗ[ℝ] (M → ℝ)),
    True -- placeholder: the full D11 `HeatKernelCore M` field list is re-used verbatim later

/-- **Obligation**: the compact analogue of the L∞ contraction: for the manifold kernel
`K(x, y, t)` with `∫ y, K x y t ∂volume = 1` and `K ≥ 0`, the operator
`P_t f x = ∫ y, K x y t * f y ∂volume` satisfies `‖P_t f‖_∞ ≤ ‖f‖_∞` on bounded measurable
functions. Proved in the Euclidean model by `heatOperator_norm_le_of_forall_norm_le`; the
manifold proof needs the same two inputs (kernel nonnegativity and mass one) and the same
`norm_integral_le_of_norm_le` comparison. -/
def CompactManifoldLinfContractionObligation (M : Type*) [MeasurableSpace M] : Prop :=
  ∀ (μ : Measure M) (K : M → M → ℝ) (P : (M → ℝ) → M → ℝ),
    (∀ x y, 0 ≤ K x y) →
      (∀ x, ∫ y, K x y ∂μ = 1) →
        (∀ f x, P f x = ∫ y, K x y * f y ∂μ) →
          ∀ {f : M → ℝ} {C : ℝ}, 0 ≤ C → (∀ y, ‖f y‖ ≤ C) → ∀ x, ‖P f x‖ ≤ C

/-- **Obligation**: the compact analogue of the L¹ contraction, stated with the extended norm
(Tonelli form). The Euclidean proof (`heatOperator_lintegral_enorm_le`) uses only
`∫⁻ y, ‖K x y‖ₑ = 1` and Fubini; on a compact manifold the reference measure is finite, so the
product-integrability machinery of the Euclidean proof transfers verbatim once the kernel is
measurable and normalised. -/
def CompactManifoldL1ContractionObligation (M : Type*) [MeasurableSpace M] : Prop :=
  ∀ (μ : Measure M) (K : M → M → ℝ) (P : (M → ℝ) → M → ℝ),
    (∀ x, ∫⁻ y, ‖K x y‖ₑ ∂μ = 1) →
      (∀ f x, P f x = ∫ y, K x y * f y ∂μ) →
        ∀ f : M → ℝ, ∫⁻ x, ‖P f x‖ₑ ∂μ ≤ ∫⁻ y, ‖f y‖ₑ ∂μ

/-- **Obligation**: smoothing for the compact analogue — differentiability of `x ↦ P_t f x` for
bounded measurable `f` under the same dominated-derivative assumptions as the Euclidean
`hasFDerivAt_heatOperator`. -/
def CompactManifoldSmoothingObligation (M : Type*) [NormedAddCommGroup M] [NormedSpace ℝ M]
    [MeasurableSpace M] : Prop :=
  ∀ (μ : Measure M) (F : M → M → ℝ) (F' : M → M → M →L[ℝ] ℝ),
    (∀ x, Integrable (fun y => F x y) μ) →
      (∀ x, Integrable (fun y => ‖F' x y‖) μ) →
        (∀ y, Continuous (fun x => F x y)) →
          (∀ x y, HasFDerivAt (fun z => F z y) (F' x y) x) →
            ∀ x₀, HasFDerivAt (fun x => ∫ y, F x y ∂μ) (∫ y, F' x₀ y ∂μ) x₀

/-- **Obligation**: strong continuity at `0` on the compact analogue: for continuous test
functions (integrable automatically on a finite-measure compact space, with a bounded kernel
normalisation) the manifold semigroup reproduces `f` pointwise as `t → 0⁺`. The Euclidean input
is the D11 peak-function theorem; the compact version needs the corresponding Gaussian
localisation from the D11 core datum. -/
def CompactManifoldStrongContinuityObligation (M : Type*) [TopologicalSpace M] [MeasurableSpace M] :
    Prop :=
  ∀ (μ : Measure M) (K : M → M → ℝ → ℝ) (P : (M → ℝ) → ℝ → M → ℝ),
    (∀ f x t, P f t x = ∫ y, K x y t * f y ∂μ) →
      (∀ x f, Continuous f → Tendsto (fun t : ℝ => P f t x) (𝓝[>] (0 : ℝ)) (𝓝 (f x)))

/-- **Obligation**: the semigroup law `P_s (P_t f) = P_{s+t} f` on the compact analogue, from
the Chapman–Kolmogorov identity of the D11 core datum (already a field there for the flat model;
the compact construction must prove it for its own kernel). -/
def CompactManifoldSemigroupObligation (M : Type*) [MeasurableSpace M] : Prop :=
  ∀ (μ : Measure M) (K : M → M → ℝ → ℝ) (P : (M → ℝ) → ℝ → M → ℝ),
    (∀ x y s t, 0 < s → 0 < t → K x y (s + t) = ∫ z, K x z s * K z y t ∂μ) →
      (∀ f x t, P f t x = ∫ y, K x y t * f y ∂μ) →
        ∀ {f : M → ℝ} {s t : ℝ}, 0 < s → 0 < t → Integrable f μ →
          ∀ x, P (P f t) s x = P f (s + t) x

end Poincare.D12.HeatSemigroup
