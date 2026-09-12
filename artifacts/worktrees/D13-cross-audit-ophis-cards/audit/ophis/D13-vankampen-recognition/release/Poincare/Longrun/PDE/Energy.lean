/-
Task `D2-pde-foundation`: energy monotonicity for the explicit heat scheme.

This file is part of the long-run Poincaré formalization.  It consumes the
accepted `D1-pde-api-map` probe (`longrun/results/D1-pde-api-map.md`) and builds
the energy-monotonicity toy theorem recommended there.
-/
import Poincare.Longrun.PDE.HeatGrid

/-!
# `Poincare.Longrun.PDE.Energy`

Monotonicity of the ℓ² energy for the explicit-Euler heat scheme on a finite
path with zero Dirichlet boundary.

## Assumptions and sign conventions (explicit)

* The scheme is `u (t+1) i = u t i + α * (u t (i-1) - 2 * u t i + u t (i+1))`,
  i.e. the heat equation is `∂ₜ u = + ∂ₓ² u` and the scheme is **forward** Euler.
* `0 ≤ α` is required so that the update is a convex combination; the sharper
  stability condition `α ≤ 1/2` is required for the energy estimate below.
* The boundary values `u t 0` and `u t (N+1)` are pinned to `0`.
* The energy is the sum of squares `E(u) = Σ_{i=0}^{N+1} (u i)^2`.  It is
  nonnegative, and `E (u (t+1)) ≤ E (u t)`: the explicit heat flow is
  dissipative in ℓ².

The proof is the elementary convexity argument
`(Σ wᵢ xᵢ)^2 ≤ Σ wᵢ xᵢ^2` for nonnegative weights `wᵢ` with `Σ wᵢ = 1`
(`convex_combo_sq_le`), applied at every grid point, followed by a reindexing of
the shifted sums (`sum_shift_pred`, `sum_shift_succ`).  No compactness, PDE
regularity, or limiting argument is involved.
-/

open scoped BigOperators

namespace Poincare.Longrun.PDE

/-- ℓ² energy of a grid configuration on the path `0, …, N+1`:
`Σ i ∈ range (N+2), (u i)^2`. -/
def energy (u : ℕ → ℝ) (N : ℕ) : ℝ := ∑ i ∈ Finset.range (N + 2), (u i) ^ 2

/-- **Three-point convex-combination inequality for the square.**
For weights `p, q, r ≥ 0` with `p + q + r = 1`,
`(p a + q b + r c)^2 ≤ p a^2 + q b^2 + r c^2`. -/
theorem convex_combo_sq_le {p q r a b c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hsum : p + q + r = 1) :
    (p * a + q * b + r * c) ^ 2 ≤ p * a ^ 2 + q * b ^ 2 + r * c ^ 2 := by
  have h1 : 0 ≤ p * q := mul_nonneg hp hq
  have h2 : 0 ≤ p * r := mul_nonneg hp hr
  have h3 : 0 ≤ q * r := mul_nonneg hq hr
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), h1, h2, h3, hsum]

/-- Pointwise energy estimate for one heat step: for `0 ≤ α ≤ 1/2` the square of
the new value is at most the convex combination of the squares of the three old
values. -/
theorem heatStep_sq_le (w : ℕ → ℝ) (i : ℕ) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) :
    (heatStep α w i) ^ 2
      ≤ α * (w (i - 1)) ^ 2 + (1 - 2 * α) * (w i) ^ 2 + α * (w (i + 1)) ^ 2 := by
  have hq : 0 ≤ 1 - 2 * α := by linarith
  have hsum : α + (1 - 2 * α) + α = 1 := by ring
  simpa only [heatStep] using
    convex_combo_sq_le (p := α) (q := 1 - 2 * α) (r := α) hα0 hq hα0 hsum
      (a := w (i - 1)) (b := w i) (c := w (i + 1))

/-- Reindexing of the backwards-shifted sum.  If `w 0 = 0` and `w (N+1) = 0`,
then `Σ_{i=0}^{N+1} (w (i-1))^2 = Σ_{i=0}^{N+1} (w i)^2` (the extra copy of the
`i = 0` term is killed by `w 0 = 0`). -/
theorem sum_shift_pred (w : ℕ → ℝ) (N : ℕ) (h0 : w 0 = 0) (hN : w (N + 1) = 0) :
    ∑ i ∈ Finset.range (N + 2), (w (i - 1)) ^ 2
      = ∑ i ∈ Finset.range (N + 2), (w i) ^ 2 := by
  have hL : ∑ i ∈ Finset.range (N + 2), (w (i - 1)) ^ 2
      = (∑ i ∈ Finset.range (N + 1), (w i) ^ 2) + (w 0) ^ 2 := by
    rw [Finset.sum_range_succ']
    simp
  have hR : ∑ i ∈ Finset.range (N + 2), (w i) ^ 2
      = (∑ i ∈ Finset.range (N + 1), (w i) ^ 2) + (w (N + 1)) ^ 2 := by
    rw [Finset.sum_range_succ]
  rw [hL, hR, h0, hN]

/-- Reindexing of the forwards-shifted sum.  If `w 0 = 0` and `w (N+2) = 0`, then
`Σ_{i=0}^{N+1} (w (i+1))^2 = Σ_{i=0}^{N+1} (w i)^2`. -/
theorem sum_shift_succ (w : ℕ → ℝ) (N : ℕ) (h0 : w 0 = 0) (hN : w (N + 2) = 0) :
    ∑ i ∈ Finset.range (N + 2), (w (i + 1)) ^ 2
      = ∑ i ∈ Finset.range (N + 2), (w i) ^ 2 := by
  have hL : ∑ i ∈ Finset.range (N + 2), (w (i + 1)) ^ 2
      = (∑ i ∈ Finset.range (N + 1), (w (i + 1)) ^ 2) + (w (N + 2)) ^ 2 := by
    rw [Finset.sum_range_succ]
  have hR : ∑ i ∈ Finset.range (N + 2), (w i) ^ 2
      = (∑ i ∈ Finset.range (N + 1), (w (i + 1)) ^ 2) + (w 0) ^ 2 := by
    rw [Finset.sum_range_succ']
  rw [hL, hR, h0, hN]

/-- **Energy estimate for one heat step.**  For `0 ≤ α ≤ 1/2` and a configuration
with zero Dirichlet boundary values, the energy of the zero-extended explicit
heat step is at most the energy of the configuration. -/
theorem energy_heatStep_le {N : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2)
    {u : ℕ → ℝ} (h0 : u 0 = 0) (hN : u (N + 1) = 0) :
    ∑ i ∈ Finset.range (N + 2), (heatStep α (zeroExtend u N) i) ^ 2
      ≤ ∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2 := by
  have hz0 : zeroExtend u N 0 = 0 := by simp [zeroExtend, h0]
  have hzN : zeroExtend u N (N + 1) = 0 := by simp [zeroExtend, hN]
  have hzN2 : zeroExtend u N (N + 2) = 0 := by
    simp only [zeroExtend]
    rw [ite_eq_right (by omega)]
  have hsum_le : ∑ i ∈ Finset.range (N + 2), (heatStep α (zeroExtend u N) i) ^ 2
      ≤ ∑ i ∈ Finset.range (N + 2),
          (α * (zeroExtend u N (i - 1)) ^ 2 + (1 - 2 * α) * (zeroExtend u N i) ^ 2
            + α * (zeroExtend u N (i + 1)) ^ 2) :=
    Finset.sum_le_sum (fun i _ => heatStep_sq_le (zeroExtend u N) i hα0 hα1)
  have hdist : ∑ i ∈ Finset.range (N + 2),
        (α * (zeroExtend u N (i - 1)) ^ 2 + (1 - 2 * α) * (zeroExtend u N i) ^ 2
          + α * (zeroExtend u N (i + 1)) ^ 2)
      = α * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N (i - 1)) ^ 2)
        + (1 - 2 * α) * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2)
        + α * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N (i + 1)) ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsp := sum_shift_pred (zeroExtend u N) N hz0 hzN
  have hsN := sum_shift_succ (zeroExtend u N) N hz0 hzN2
  calc ∑ i ∈ Finset.range (N + 2), (heatStep α (zeroExtend u N) i) ^ 2
      ≤ ∑ i ∈ Finset.range (N + 2),
          (α * (zeroExtend u N (i - 1)) ^ 2 + (1 - 2 * α) * (zeroExtend u N i) ^ 2
            + α * (zeroExtend u N (i + 1)) ^ 2) := hsum_le
    _ = α * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N (i - 1)) ^ 2)
        + (1 - 2 * α) * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2)
        + α * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N (i + 1)) ^ 2) := hdist
    _ = α * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2)
        + (1 - 2 * α) * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2)
        + α * (∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2) := by rw [hsp, hsN]
    _ = ∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2 := by ring

/-- The energy is nonnegative. -/
theorem energy_nonneg (u : ℕ → ℝ) (N : ℕ) : 0 ≤ energy u N := by
  unfold energy
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- **One-step energy monotonicity.**  For `0 ≤ α ≤ 1/2`, one explicit heat step
does not increase the ℓ² energy. -/
theorem energy_step_le {N : ℕ} {α : ℝ} {u v : ℕ → ℝ}
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (h0 : u 0 = 0) (hN : u (N + 1) = 0)
    (hstep : ∀ i ≤ N + 1, (v i) ^ 2 ≤ (heatStep α (zeroExtend u N) i) ^ 2) :
    energy v N ≤ energy u N := by
  have h1 : energy v N ≤ ∑ i ∈ Finset.range (N + 2), (heatStep α (zeroExtend u N) i) ^ 2 :=
    Finset.sum_le_sum (fun i hi => hstep i (by have := Finset.mem_range.mp hi; omega))
  have h2 : ∑ i ∈ Finset.range (N + 2), (heatStep α (zeroExtend u N) i) ^ 2
      ≤ ∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2 :=
    energy_heatStep_le hα0 hα1 h0 hN
  have h3 : ∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2 = energy u N := by
    unfold energy
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ N + 1 := by have := Finset.mem_range.mp hi; omega
    simp [zeroExtend, ite_eq_left hi']
  calc energy v N ≤ ∑ i ∈ Finset.range (N + 2), (heatStep α (zeroExtend u N) i) ^ 2 := h1
    _ ≤ ∑ i ∈ Finset.range (N + 2), (zeroExtend u N i) ^ 2 := h2
    _ = energy u N := h3

/-- **Energy monotonicity for the finite-grid heat evolution.**  Under
`0 ≤ α ≤ 1/2`, the energy of the slice at time `t+1` is at most the energy of the
slice at time `t`. -/
theorem HeatGridEvolution.energy_succ_le {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (t : ℕ) :
    energy (ev.u (t + 1)) N ≤ energy (ev.u t) N := by
  refine energy_step_le hα0 hα1 (ev.boundary_left t) (ev.boundary_right t) (fun i hi => ?_)
  by_cases hi0 : i = 0
  · rw [hi0, ev.boundary_left (t + 1)]
    simpa using sq_nonneg (heatStep α (zeroExtend (ev.u t) N) 0)
  by_cases hiN : i = N + 1
  · rw [hiN, ev.boundary_right (t + 1)]
    simpa using sq_nonneg (heatStep α (zeroExtend (ev.u t) N) (N + 1))
  · rw [ev.step_eq_heatStep (Nat.pos_of_ne_zero hi0) (lt_of_le_of_ne hi hiN)]

/-- **Global energy monotonicity.**  The energy at any time is at most the energy
of the initial slice. -/
theorem HeatGridEvolution.energy_nonincreasing {N : ℕ} {α : ℝ} (ev : HeatGridEvolution N α)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1 / 2) (t : ℕ) :
    energy (ev.u t) N ≤ energy (ev.u 0) N := by
  induction t with
  | zero => exact le_rfl
  | succ t ih => exact (ev.energy_succ_le hα0 hα1 t).trans ih

/-! ## Axiom audit -/

#print axioms energy
#print axioms convex_combo_sq_le
#print axioms heatStep_sq_le
#print axioms sum_shift_pred
#print axioms sum_shift_succ
#print axioms energy_heatStep_le
#print axioms energy_nonneg
#print axioms energy_step_le
#print axioms HeatGridEvolution.energy_succ_le
#print axioms HeatGridEvolution.energy_nonincreasing

end Poincare.Longrun.PDE
