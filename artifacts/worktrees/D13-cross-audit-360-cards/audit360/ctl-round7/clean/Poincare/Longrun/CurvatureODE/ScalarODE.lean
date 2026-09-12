import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall

/-!
# Poincare.Longrun.CurvatureODE.ScalarODE

**Stage 2 / curvature-ODE cluster: scalar sign-preservation lemmas.**

These are the analytic engine of the cluster. They are stated for real functions of one
variable and use only the pinned mathlib's mean-value theorem and Grönwall inequality
(`Mathlib.Analysis.Calculus.MeanValue`, `Mathlib.Analysis.ODE.Gronwall`); no ODE
existence/uniqueness theory and no manifold analysis is needed.

* `le_left_of_hasDerivWithinAt_nonpos`: if `f` is continuous on `[a,b]`, has right derivative
  `f'` on `[a,b)`, and `f' ≤ 0` there, then `f x ≤ f a` on `[a,b]` (fencing theorem with the
  constant boundary `f a`).
* `le_zero_of_hasDerivWithinAt_le_mul`: the linear-comparison **sign-preservation** theorem
  `f a ≤ 0` and `f' ≤ c * f` with `c ≥ 0` imply `f ≤ 0` on `[a,b]` (Grönwall with `δ = f a`,
  `ε = 0`; the bound is `f a * exp (c (x - a)) ≤ 0`).

All proofs are complete: no `sorry`, `axiom`, `unsafe`, `native_decide`, or `proof_wanted`.
-/

open Set

namespace Poincare
namespace Longrun
namespace CurvatureODE

/-- **Sign preservation, boundary form.** If `f` is continuous on `[a,b]`, has right
derivative `f'` on `[a,b)`, and `f' ≤ 0` there, then `f` is nonincreasing on `[a,b]`. -/
theorem le_left_of_hasDerivWithinAt_nonpos {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (hmono : ∀ x ∈ Ico a b, f' x ≤ 0) :
    ∀ x ∈ Icc a b, f x ≤ f a := by
  have hB : ContinuousOn (fun _ : ℝ => f a) (Icc a b) := continuousOn_const
  have hB' : ∀ x ∈ Ico a b, HasDerivWithinAt (fun _ : ℝ => f a) (0 : ℝ) (Ici x) x :=
    fun x _ => hasDerivWithinAt_const x (Ici x) (f a)
  exact image_le_of_deriv_right_le_deriv_boundary hf hf' (le_refl (f a)) hB hB'
    (fun x hx => hmono x hx)

/-- **Linear-comparison sign preservation.** If `f a ≤ 0` and the right derivative of `f`
satisfies `f' ≤ c * f` on `[a,b)`, then `f ≤ 0` on `[a,b]`. This is the Grönwall bound
`f x ≤ f a * exp (c (x - a)) ≤ 0`; no sign condition on the constant `c` is needed. -/
theorem le_zero_of_hasDerivWithinAt_le_mul {f f' : ℝ → ℝ} {c a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : f a ≤ 0)
    (hbound : ∀ x ∈ Ico a b, f' x ≤ c * f x) :
    ∀ x ∈ Icc a b, f x ≤ 0 := by
  have hmain : ∀ x ∈ Icc a b, f x ≤ gronwallBound (f a) c 0 (x - a) :=
    le_gronwallBound_of_liminf_deriv_right_le (f := f) (f' := f') (δ := f a) (K := c)
      (ε := 0) (a := a) (b := b) hf
      (fun x hx r hr => by
        simpa [slope, smul_eq_mul] using (hf' x hx).liminf_right_slope_le hr)
      (le_refl (f a)) (fun x hx => by simpa using hbound x hx)
  intro x hx
  have hx' := hmain x hx
  rw [gronwallBound_ε0] at hx'
  exact hx'.trans (mul_nonpos_of_nonpos_of_nonneg ha (Real.exp_nonneg _))

/-- **Nonnegative form.** If `f a ≥ 0` and `c * f ≤ f'` on `[a,b)`, then `f ≥ 0` on
`[a,b]` (apply the previous theorem to `-f`). -/
theorem ge_zero_of_hasDerivWithinAt_mul_le {f f' : ℝ → ℝ} {c a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hf' : ∀ x ∈ Ico a b, HasDerivWithinAt f (f' x) (Ici x) x)
    (ha : 0 ≤ f a)
    (hbound : ∀ x ∈ Ico a b, c * f x ≤ f' x) :
    ∀ x ∈ Icc a b, 0 ≤ f x := by
  have hf_neg : ContinuousOn (fun x => -f x) (Icc a b) := hf.neg
  have hf'_neg : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun y => -f y) (-(f' x)) (Ici x) x :=
    fun x hx => (hf' x hx).neg
  have hbound' : ∀ x ∈ Ico a b, -(f' x) ≤ c * (-f x) := by
    intro x hx
    have h := hbound x hx
    linarith
  have hmain := le_zero_of_hasDerivWithinAt_le_mul hf_neg hf'_neg (neg_nonpos.mpr ha) hbound'
  intro x hx
  have h := hmain x hx
  linarith

end CurvatureODE
end Longrun
end Poincare
