import Mathlib
import Poincare.D9.Surfaces.Basic

/-!
# Poincare.D9.Surfaces.Statements

**D9 / `D9-ricci-flow-surfaces`: state-only interfaces for the surface theorems.**

This module records the two analytic theorems of Ricci flow on surfaces that are *not*
proved here, as `def : Prop` interfaces. They are neither theorems nor axioms: they are
hypotheses/interfaces that later work can consume, and every declaration that would need
them takes them as an explicit argument.

* `HamiltonSurfaceTheoremStatement` — Hamilton's theorem: for any smooth initial metric on
  `S²`, the normalized flow exists for all time and the scalar curvature converges to the
  constant `r` (constant curvature in the limit).
* `BernsteinBandoShiSurfaceStatement` — the Bernstein–Bando–Shi smoothing estimates
  specialized to surfaces: uniform curvature bounds and scale-invariant derivative bounds
  `t^{k/2} |∂ₜ^k scal| ≤ C_k` for the normalized flow, and `t^{1 + k/2} |∇^k Rm| ≤ C_k`
  for the unnormalized flow.

Only the trivial logical projections of the statements are proved
(`hamiltonStatement_existsAllTime`, `hamiltonStatement_converges`), so the interfaces are
kernel-checked to be coherent. All proofs are complete: no `sorry`, `axiom`, `unsafe`,
`native_decide`, or `proof_wanted`.
-/

noncomputable section

open MeasureTheory
open Filter
open scoped Topology

namespace Poincare
namespace D9
namespace Surfaces

/-- Local-coordinate data of a time-dependent surface flow: a metric family
`g t x ∈ Mat2`, a scalar-curvature family `scal t x`, and the normalization constant `r`. -/
structure SurfaceFlow (M : Type*) where
  g : ℝ → M → Mat2
  scal : ℝ → M → ℝ
  r : ℝ

namespace SurfaceFlow

variable {M : Type*}

/-- **The normalized flow conditions.** The flow equation `∂ₜ g = (r - scal) g` holds
pointwise, and `r` is the area-average of `scal` at every time. -/
def IsNormalized {M : Type*} [MeasurableSpace M] (μ : Measure M) (F : SurfaceFlow M) : Prop :=
  (∀ t x i j, HasDerivAt (fun s => F.g s x i j) ((F.r - F.scal t x) * F.g t x i j) t) ∧
  (∀ t, ∫ x, (F.scal t x - F.r) * areaDensity (F.g t x) ∂μ = 0)

/-- **The unnormalized flow equation** `∂ₜ g = -scal g` (the surface form of
`∂ₜ g = -2 Ric`). -/
def IsUnnormalized (F : SurfaceFlow M) : Prop :=
  ∀ t x i j, HasDerivAt (fun s => F.g s x i j) (-(F.scal t x) * F.g t x i j) t

/-- Smoothness of the metric and curvature families in the time variable. -/
def IsSmooth (F : SurfaceFlow M) : Prop :=
  (∀ x i j, ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F.g t x i j)) ∧
  (∀ x, ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => F.scal t x))

/-- The flow starts at the prescribed initial datum. -/
def HasInitialDatum (F : SurfaceFlow M) (g₀ : M → Mat2) (scal₀ : M → ℝ) : Prop :=
  F.g 0 = g₀ ∧ F.scal 0 = scal₀

/-- The flow exists for all nonnegative times with positive-definite metric. -/
def ExistsAllTime (F : SurfaceFlow M) : Prop :=
  ∀ t, 0 ≤ t → ∀ x, 0 < (F.g t x).det

/-- The scalar curvature converges pointwise to the constant `r`. -/
def ConvergesToConstantCurvature (F : SurfaceFlow M) : Prop :=
  Tendsto (fun t => F.scal t) atTop (𝓝 (fun _ => F.r))

end SurfaceFlow

/-- **A smooth initial datum on `S²`.** Positive area, positive-definite metric matrix at
every point, and Gauss–Bonnet normalization `∫ scal₀ = r · area` for the prescribed
average scalar curvature `r`. -/
def IsSphereInitialDatum {M : Type*} [MeasurableSpace M] (μ : Measure M)
    (g₀ : M → Mat2) (scal₀ : M → ℝ) (r : ℝ) : Prop :=
  0 < (μ Set.univ).toReal ∧
  (∀ x, 0 < (g₀ x).det) ∧
  ∫ x, scal₀ x ∂μ = r * (μ Set.univ).toReal

/-- **Hamilton's surface theorem (statement only).** For every smooth initial metric on
`S²` with normalization constant `r`, there is a normalized Ricci flow defined for all
nonnegative times, starting at that metric, whose scalar curvature converges to the
constant `r`.

This is a `def : Prop`, not a theorem and not an axiom. It records the precise statement of
the unproved Hamilton convergence theorem as a state-only interface. -/
def HamiltonSurfaceTheoremStatement {M : Type*} [MeasurableSpace M] (μ : Measure M)
    (r : ℝ) : Prop :=
  ∀ (g₀ : M → Mat2) (scal₀ : M → ℝ),
    IsSphereInitialDatum μ g₀ scal₀ r →
    ∃ F : SurfaceFlow M,
      F.r = r ∧ F.IsNormalized μ ∧ F.IsSmooth ∧ F.HasInitialDatum g₀ scal₀ ∧
      F.ExistsAllTime ∧ F.ConvergesToConstantCurvature

/-- Trivial projection of the Hamilton statement: existence for all time. -/
theorem hamiltonStatement_existsAllTime {M : Type*} [MeasurableSpace M] {μ : Measure M}
    {r : ℝ} (h : HamiltonSurfaceTheoremStatement μ r) {g₀ : M → Mat2} {scal₀ : M → ℝ}
    (hg : IsSphereInitialDatum μ g₀ scal₀ r) :
    ∃ F : SurfaceFlow M,
      F.r = r ∧ F.IsNormalized μ ∧ F.HasInitialDatum g₀ scal₀ ∧ F.ExistsAllTime := by
  obtain ⟨F, hF⟩ := h g₀ scal₀ hg
  exact ⟨F, hF.1, hF.2.1, hF.2.2.2.1, hF.2.2.2.2.1⟩

/-- Trivial projection of the Hamilton statement: convergence to constant curvature. -/
theorem hamiltonStatement_converges {M : Type*} [MeasurableSpace M] {μ : Measure M}
    {r : ℝ} (h : HamiltonSurfaceTheoremStatement μ r) {g₀ : M → Mat2} {scal₀ : M → ℝ}
    (hg : IsSphereInitialDatum μ g₀ scal₀ r) :
    ∃ F : SurfaceFlow M, F.r = r ∧ F.ConvergesToConstantCurvature := by
  obtain ⟨F, hF⟩ := h g₀ scal₀ hg
  exact ⟨F, hF.1, hF.2.2.2.2.2⟩

/-- **A covariant-derivative norm profile.** `gradNorm k t x` stands for `|∇^k Rm|(t,x)`,
the pointwise norm of the `k`-th covariant derivative of the curvature tensor. This is an
interface value: no manifold-level object is constructed here. -/
structure CovariantDerivativeProfile (M : Type*) where
  gradNorm : ℕ → ℝ → M → ℝ
  zero_le : ∀ k t x, 0 ≤ gradNorm k t x

/-- **Bernstein–Bando–Shi smoothing estimates, surface specialization (statement only).**
For a smooth normalized surface flow:

* the scalar curvature is uniformly bounded on `(0, ∞) × M`;
* every covariant derivative of the curvature obeys the scale-invariant bound
  `t^{1 + k/2} |∇^k Rm| ≤ C_k`;
* every time derivative of the scalar curvature obeys `t^{k/2} |∂ₜ^k scal| ≤ C_k`.

This is a `def : Prop`, not a theorem and not an axiom. -/
def BernsteinBandoShiSurfaceStatement {M : Type*} [MeasurableSpace M] (μ : Measure M) : Prop :=
  ∀ F : SurfaceFlow M, F.IsNormalized μ → F.IsSmooth →
    (∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t → ∀ x, |F.scal t x| ≤ C) ∧
    (∀ P : CovariantDerivativeProfile M,
      (∀ t x, P.gradNorm 0 t x = |F.scal t x|) →
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t → ∀ x,
        t ^ (1 + (k : ℝ) / 2) * P.gradNorm k t x ≤ C) ∧
    (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t → ∀ x,
      t ^ ((k : ℝ) / 2) * |(deriv^[k] (fun s => F.scal s x)) t| ≤ C)

/-- **Bernstein–Bando–Shi estimates, unnormalized surface flow (statement only).** For a
smooth unnormalized flow `∂ₜ g = -scal g`, the scale-invariant bound
`t^{1 + k/2} |∇^k Rm| ≤ C_k` holds on `(0, ∞) × M`. -/
def BernsteinBandoShiUnnormalizedStatement {M : Type*} (F : SurfaceFlow M) : Prop :=
  F.IsUnnormalized → F.IsSmooth →
    ∀ P : CovariantDerivativeProfile M,
      (∀ t x, P.gradNorm 0 t x = |F.scal t x|) →
      ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t, 0 < t → ∀ x,
        t ^ (1 + (k : ℝ) / 2) * P.gradNorm k t x ≤ C

end Surfaces
end D9
end Poincare
