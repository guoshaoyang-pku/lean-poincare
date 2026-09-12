/-
Task `D3-entropy-interface`: a measure/metric-flow-compatible interface for F/W-style
entropy functionals.

**Scope and honesty boundary.** This file does *not* prove Perelman's entropy
monotonicity, and nothing in this directory is a proof of the Poincaré
conjecture.  It defines an abstract measure/metric-flow-compatible interface for
F/W-style functionals and proves only the algebraic/measure-theoretic identities
that do not need the missing manifold analysis.  The integration-by-parts and
regularity theorems that would connect this interface to a genuine Ricci flow are
recorded, unproved, in `Poincare.Longrun.Entropy.Bridge`.

The weight `ρ` is the density of the entropy measure with respect to the
background measure `μ`: `dm = ρ dμ`.  For the geometric case `ρ` is meant to be
`(4πτ)^(-n/2) exp(-f)` (the conjugate weight); the predicate
`HasConjugateWeight` records the exponential part.  Both functionals are defined
with the *same* weight, so the identity `W = τ F + ∫ (f - n) dm` below is an
algebraic decomposition, not a claim about Perelman's normalization.

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or
`proof_wanted`.
-/
import Mathlib

open MeasureTheory
open scoped BigOperators

namespace Poincare.Longrun.Entropy

universe u

/-- **Measure/metric-flow-compatible entropy datum.**

`X` is the state space with a background measure `μ`; `ρ` is the density of the
entropy measure with respect to `μ` (`dm = ρ dμ`).  The fields record, in order:
the scalar-curvature density `R`, the gradient-squared density `|∇f|²`, the
potential `f`, the weight `ρ`, the coupling parameter `τ > 0`, the (real)
dimension `n`, the pointwise dissipation density `|Ric + ∇²f|²` (abstract, so no
manifold structure is assumed), nonnegativity of the weight, and the
integrability of the two functional integrands. -/
structure EntropyData (X : Type u) [MeasurableSpace X] (μ : Measure X) where
  /-- Scalar-curvature density `R`. -/
  R : X → ℝ
  /-- Gradient-squared density `|∇f|²`. -/
  gradSq : X → ℝ
  /-- The potential `f`. -/
  f : X → ℝ
  /-- Density of the entropy measure `dm = ρ dμ`. -/
  ρ : X → ℝ
  /-- Coupling parameter `τ`. -/
  τ : ℝ
  /-- Positivity of the coupling parameter. -/
  τ_pos : 0 < τ
  /-- The (real) dimension parameter `n`. -/
  n : ℝ
  /-- Pointwise dissipation density `|Ric + ∇²f|²` (abstract datum). -/
  riccHess : X → ℝ
  /-- The weight is nonnegative. -/
  ρ_nonneg : ∀ x : X, 0 ≤ ρ x
  /-- The `F`-integrand is integrable. -/
  integrable_F : Integrable (fun x : X => (R x + gradSq x) * ρ x) μ
  /-- The `W`-integrand is integrable. -/
  integrable_W : Integrable (fun x : X => (τ * (gradSq x + R x) + (f x - n)) * ρ x) μ

namespace EntropyData

variable {X : Type u} [MeasurableSpace X] {μ : Measure X}

/-- The `F`-functional `∫ (R + |∇f|²) dm` with `dm = ρ dμ`. -/
noncomputable def F (D : EntropyData X μ) : ℝ :=
  ∫ x : X, (D.R x + D.gradSq x) * D.ρ x ∂μ

/-- The potential term `∫ (f - n) dm` appearing in the decomposition of `W`. -/
noncomputable def extra (D : EntropyData X μ) : ℝ :=
  ∫ x : X, (D.f x - D.n) * D.ρ x ∂μ

/-- The `W`-functional `∫ (τ (|∇f|² + R) + f - n) dm`. -/
noncomputable def W (D : EntropyData X μ) : ℝ :=
  ∫ x : X, (D.τ * (D.gradSq x + D.R x) + (D.f x - D.n)) * D.ρ x ∂μ

/-- The `F`-dissipation `2 ∫ |Ric + ∇²f|² dm`.  Its nonnegativity is purely
algebraic (`FDissipation_nonneg`); the missing analytic theorem is that the time
derivative of `F` equals this quantity (see `Poincare.Longrun.Entropy.Bridge`). -/
noncomputable def FDissipation (D : EntropyData X μ) : ℝ :=
  ∫ x : X, 2 * (D.riccHess x) ^ 2 * D.ρ x ∂μ

/-- The exponential-weight predicate: the density is `exp(-f)` up to the
`(4πτ)^(-n/2)` normalization factor, which is absorbed into `μ` or `ρ`. -/
def HasConjugateWeight (D : EntropyData X μ) : Prop :=
  ∀ x : X, D.ρ x = Real.exp (-(D.f x))

/-- A conjugate weight is strictly positive. -/
theorem conjugateWeight_pos (D : EntropyData X μ) (h : HasConjugateWeight D) (x : X) :
    0 < D.ρ x := by
  rw [h x]
  exact Real.exp_pos _

/-- Integrability of the potential term, derived from the integrability of the
`F`- and `W`-integrands. -/
theorem integrable_extra (D : EntropyData X μ) :
    Integrable (fun x : X => (D.f x - D.n) * D.ρ x) μ := by
  have h₁ : Integrable (fun x : X => D.τ * ((D.R x + D.gradSq x) * D.ρ x)) μ :=
    D.integrable_F.const_mul D.τ
  have h₂ : Integrable (fun x : X =>
      (D.τ * (D.gradSq x + D.R x) + (D.f x - D.n)) * D.ρ x
        - D.τ * ((D.R x + D.gradSq x) * D.ρ x)) μ :=
    D.integrable_W.sub h₁
  refine h₂.congr ?_
  filter_upwards with x
  ring

/-- **Algebraic decomposition of `W`.**  With both functionals defined against
the same weight `dm = ρ dμ`,
`W = τ F + ∫ (f - n) dm`. -/
theorem W_eq (D : EntropyData X μ) : D.W = D.τ * D.F + D.extra := by
  have hpt : ∀ x : X, (D.τ * (D.gradSq x + D.R x) + (D.f x - D.n)) * D.ρ x
      = D.τ * ((D.R x + D.gradSq x) * D.ρ x) + (D.f x - D.n) * D.ρ x := by
    intro x
    ring
  unfold W F extra
  simp only [hpt]
  rw [MeasureTheory.integral_add (D.integrable_F.const_mul D.τ) D.integrable_extra,
    MeasureTheory.integral_const_mul]

/-- **The dissipation is nonnegative.**  Purely algebraic: a square times a
nonnegative weight. -/
theorem FDissipation_nonneg (D : EntropyData X μ) : 0 ≤ D.FDissipation := by
  unfold FDissipation
  apply MeasureTheory.integral_nonneg
  intro x
  have hρ : 0 ≤ D.ρ x := D.ρ_nonneg x
  have hsq : 0 ≤ (D.riccHess x) ^ 2 := sq_nonneg _
  change 0 ≤ 2 * (D.riccHess x) ^ 2 * D.ρ x
  nlinarith

/-- The `F`-functional is monotone in the curvature term for fixed nonnegative
weight: pointwise domination of the curvature integrands gives domination of the
functionals.  This is a checked algebraic consequence of the interface, used to
demonstrate that `F` is not an opaque constant. -/
theorem F_mono_integrand (D₁ D₂ : EntropyData X μ)
    (h : ∀ x : X, (D₁.R x + D₁.gradSq x) * D₁.ρ x ≤ (D₂.R x + D₂.gradSq x) * D₂.ρ x) :
    D₁.F ≤ D₂.F := by
  unfold F
  exact MeasureTheory.integral_mono D₁.integrable_F D₂.integrable_F h

end EntropyData

/-! ## Axiom audit -/

#print axioms EntropyData
#print axioms EntropyData.F
#print axioms EntropyData.extra
#print axioms EntropyData.W
#print axioms EntropyData.FDissipation
#print axioms EntropyData.HasConjugateWeight
#print axioms EntropyData.conjugateWeight_pos
#print axioms EntropyData.integrable_extra
#print axioms EntropyData.W_eq
#print axioms EntropyData.FDissipation_nonneg
#print axioms EntropyData.F_mono_integrand

end Poincare.Longrun.Entropy
