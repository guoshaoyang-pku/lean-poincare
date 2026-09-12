/-
Task `D9-sobolev-parabolic-estimates`: the Grönwall comparison lemma for the
parabolic energy estimate.

This file is part of the long-run Poincaré formalization.  It provides the
elementary real-analysis input used by the semi-discrete heat-equation model in
`Poincare.D9.ParabolicEstimates.MatrixModel`: if a nonnegative quantity `E`
satisfies the differential inequality `E'(s) ≤ C E(s) + g(s)` with `C ≥ 0` and
`g ≥ 0`, then `E(t) ≤ e^{C t} (E(0) + ∫₀ᵗ g)`.

The proof is the standard integrating-factor argument, completely checked:
`Y(s) = e^{-C s} E(s)` has `Y'(s) = e^{-C s} (E'(s) - C E(s)) ≤ e^{-C s} g(s) ≤ g(s)`,
so the fundamental theorem of calculus and monotonicity of the interval integral
give `Y(t) - Y(0) ≤ ∫₀ᵗ g`, which is the claimed bound.  No `sorry`, `axiom`,
`unsafe`, `native_decide` or `proof_wanted` is used.
-/
import Mathlib

open MeasureTheory intervalIntegral

namespace Poincare.D9.ParabolicEstimates

/-- **Grönwall energy bound.**

Let `E g e' : ℝ → ℝ`, let `C ≥ 0`, and suppose

* `E` has derivative `e' s` at every `s` (hypothesis `hE`),
* `e' s ≤ C * E s + g s` for every `s` (hypothesis `hineq`),
* `g` is nonnegative (hypothesis `hg`),
* the integrands `s ↦ e^{-C s} (e' s - C E s)` and `g` are interval-integrable on
  `[0, t]` (hypotheses `hintY`, `hintg`).

Then for `t ≥ 0`,

`E t ≤ e^{C t} (E 0 + ∫ s in 0..t, g s)`.

This is the sharp form of Grönwall's inequality used for the `L²` parabolic
energy estimate: the exponential factor carries the growth rate `C`, and the
forcing enters only through the time integral of `g`. -/
theorem gronwall_energy_bound {E g e' : ℝ → ℝ} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hE : ∀ s, HasDerivAt E (e' s) s)
    (hineq : ∀ s, e' s ≤ C * E s + g s)
    (hg : ∀ s, 0 ≤ g s)
    (hintY : IntervalIntegrable (fun s => Real.exp (-C * s) * (e' s - C * E s)) volume 0 t)
    (hintg : IntervalIntegrable g volume 0 t) :
    E t ≤ Real.exp (C * t) * (E 0 + ∫ s in 0..t, g s) := by
  -- The integrating factor `Y s = e^{-C s} E s` and its derivative.
  have hYderiv : ∀ s, HasDerivAt (fun s => Real.exp (-C * s) * E s)
      (Real.exp (-C * s) * (e' s - C * E s)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -C * s) (-C) s := by
      simpa using (hasDerivAt_id s).const_mul (-C)
    have h2 := h1.exp.mul (hE s)
    exact h2.congr_deriv (by ring)
  -- Fundamental theorem of calculus on `[0, t]`.
  have hFTC : (∫ s in 0..t, Real.exp (-C * s) * (e' s - C * E s))
      = Real.exp (-C * t) * E t - E 0 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hYderiv s) hintY
    simpa using this
  -- The integrand of `Y` is dominated by `g` on `[0, t]`.
  have hmono : (∫ s in 0..t, Real.exp (-C * s) * (e' s - C * E s)) ≤ ∫ s in 0..t, g s := by
    apply intervalIntegral.integral_mono_on ht hintY hintg
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hexp1 : Real.exp (-C * s) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith
    have hexp0 : 0 ≤ Real.exp (-C * s) := le_of_lt (Real.exp_pos _)
    have h1 : e' s - C * E s ≤ g s := by linarith [hineq s]
    calc Real.exp (-C * s) * (e' s - C * E s)
        ≤ Real.exp (-C * s) * g s := mul_le_mul_of_nonneg_left h1 hexp0
      _ ≤ 1 * g s := mul_le_mul_of_nonneg_right hexp1 (hg s)
      _ = g s := one_mul _
  have hkey : Real.exp (-C * t) * E t ≤ E 0 + ∫ s in 0..t, g s := by
    linarith [hFTC, hmono]
  -- Multiply by the positive factor `e^{C t}` and cancel.
  have hmul : Real.exp (C * t) * (Real.exp (-C * t) * E t)
      ≤ Real.exp (C * t) * (E 0 + ∫ s in 0..t, g s) :=
    mul_le_mul_of_nonneg_left hkey (le_of_lt (Real.exp_pos _))
  have hcancel : Real.exp (C * t) * (Real.exp (-C * t) * E t) = E t := by
    rw [← mul_assoc, ← Real.exp_add]
    have h0 : C * t + (-C * t) = 0 := by ring
    rw [h0, Real.exp_zero, one_mul]
  rwa [hcancel] at hmul

/-! ## Axiom audit -/

#print axioms gronwall_energy_bound

end Poincare.D9.ParabolicEstimates
