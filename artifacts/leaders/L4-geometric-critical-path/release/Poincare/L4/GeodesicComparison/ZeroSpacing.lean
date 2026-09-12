/-
Copyright (c) 2026 Poincare formalization project. All rights reserved.
Released under Apache 2.0 license in the file LICENSE.

# L4 — zero spacing for the scalar Jacobi equation

`Poincare/L4/GeodesicComparison/SturmZeroCount.lean` (round 3) proves that a strict curvature
excess forces a zero before the model's first zero, and `SturmUniqueness.lean` (round 4) proves
the complementary sharp bound: under `k ≤ K` no nonzero solution vanishes before `π/√K`.
Combining the two turns the *location* results into a **spacing** result for consecutive zeros:

* `zero_spacing_lt_of_curvature_gt` — if `k ≥ K` on `[c₁, c₁+π/√K]` with a strict excess
  somewhere on `(c₁, c₁+π/√K)`, then two consecutive zeros `c₁ < c₂` of a Jacobi solution are
  spaced **strictly less** than `π/√K`: `c₂ < c₁ + π/√K`.
* `zero_spacing_ge_of_curvature_le` — if `k ≤ K` on `[c₁,c₂]` then consecutive zeros are spaced
  **at least** `π/√K`: `c₁ + π/√K ≤ c₂`.
* `sturmModel_zero_spacing` — the model's first zero sits exactly at `a + π/√K` and it is
  nonzero before that (periodicity gives every later zero by shift), so both inequalities are
  sharp: without the strict excess the strict inequality fails, and `k ≡ K` attains the lower
  bound.

Everything is scalar ODE data on a real interval.  No manifold, geodesic, exponential map or
curvature-tensor statement is constructed or claimed; the geometric reading ("consecutive
conjugate points along a geodesic") is the unformalized U3 bridge.  Consecutiveness is encoded
by the explicit hypothesis that `u` has no zero in `(c₁,c₂)`, so no zero-set topology or ODE
uniqueness is assumed beyond what the cited theorems provide.
-/
import Poincare.L4.GeodesicComparison.SturmUniqueness

noncomputable section

open Set Filter
open scoped Topology

namespace Poincare.L4.GeodesicComparison

open Poincare.D12.ComparisonGeodesics

/-! ## 1. Spacing under a curvature lower bound -/

/-- **A strict curvature excess makes consecutive zeros closer than `π/√K`.**  Let `K > 0`, let
`k ≥ K` on `[c₁, c₁+π/√K]` with `k > K` somewhere in the open interval, and let `u` be a Jacobi
solution on `[c₁,c₂]` with consecutive zeros at `c₁` and `c₂` (no zero in between).  Then
`c₂ < c₁ + π/√K`.  (The proof in fact only uses `u c₁ = 0` and the absence of interior zeros,
so the kernel-checked statement is *weaker* than what the argument establishes; `c₁ < c₂` and
`u c₂ = 0` are kept because they record that `c₂` is the next zero.)

Proof: round 3's `exists_jacobi_zero_of_curvature_gt` on `[c₁, c₁+π/√K]` produces a zero
strictly between the two consecutive zeros, a contradiction. -/
theorem zero_spacing_lt_of_curvature_gt {k : ℝ → ℝ} {K c₁ c₂ : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (_hc₁c₂ : c₁ < c₂)
    (h : JacobiSolutionOn k u du ddu c₁ c₂)
    (hu₁ : u c₁ = 0) (_hu₂ : u c₂ = 0)
    (hno : ∀ t ∈ Ioo c₁ c₂, u t ≠ 0)
    (hk : ∀ t ∈ Icc c₁ (c₁ + Real.pi / Real.sqrt K), K ≤ k t)
    (hstrict : ∃ t ∈ Ioo c₁ (c₁ + Real.pi / Real.sqrt K), K < k t) :
    c₂ < c₁ + Real.pi / Real.sqrt K := by
  by_contra hnot
  have hb_le : c₁ + Real.pi / Real.sqrt K ≤ c₂ := le_of_not_gt hnot
  have hspan : Real.sqrt K * (c₁ + Real.pi / Real.sqrt K - c₁) = Real.pi := by
    rw [add_sub_cancel_left, mul_div_cancel₀ Real.pi (Real.sqrt_pos_of_pos hK).ne']
  have hsub : JacobiSolutionOn k u du ddu c₁ (c₁ + Real.pi / Real.sqrt K) :=
    jacobiSolutionOn_mono_Icc h
      (by linarith [div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)]) hb_le
  obtain ⟨z, hz, hzu⟩ :=
    exists_jacobi_zero_of_curvature_gt (K := K) (a := c₁) (b := c₁ + Real.pi / Real.sqrt K)
      (by linarith [div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)]) hK hspan hk hsub hu₁
      hstrict
  exact hno z ⟨hz.1, lt_of_lt_of_le hz.2 hb_le⟩ hzu

/-! ## 2. Spacing under a curvature upper bound -/

/-- **`k ≤ K` makes consecutive zeros at least `π/√K` apart.**  Let `K > 0`, let `k ≤ K` on
`[c₁,c₂]`, and let `u` be a Jacobi solution on a larger interval `[c₁,b]` (`c₂ < b`) with
consecutive zeros at `c₁` and `c₂`.  Then `c₁ + π/√K ≤ c₂`.

Proof: otherwise `√K(c₂-c₁) < π` and round 4's `no_first_zero_of_curvature_le_of_lt_pi`
excludes the first zero at `c₂`. -/
theorem zero_spacing_ge_of_curvature_le {k : ℝ → ℝ} {K c₁ c₂ b : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K) (hc₁c₂ : c₁ < c₂) (hc₂b : c₂ < b)
    (h : JacobiSolutionOn k u du ddu c₁ b)
    (hu₁ : u c₁ = 0) (hu₂ : u c₂ = 0)
    (hfirst : ∀ t ∈ Ioo c₁ c₂, u t ≠ 0)
    (hk : ∀ t ∈ Icc c₁ c₂, k t ≤ K) :
    c₁ + Real.pi / Real.sqrt K ≤ c₂ := by
  by_contra hnot
  have hlt : c₂ < c₁ + Real.pi / Real.sqrt K := lt_of_not_ge hnot
  have hspan : Real.sqrt K * (c₂ - c₁) < Real.pi := by
    have hsqrt : 0 < Real.sqrt K := Real.sqrt_pos_of_pos hK
    have h1 : Real.sqrt K * (c₂ - c₁)
        < Real.sqrt K * (c₁ + Real.pi / Real.sqrt K - c₁) :=
      mul_lt_mul_of_pos_left (by linarith) hsqrt
    rwa [add_sub_cancel_left, mul_div_cancel₀ Real.pi hsqrt.ne'] at h1
  exact no_first_zero_of_curvature_le_of_lt_pi (a := c₁) (b := b) (c := c₂) hK hspan hk h
    ⟨hc₁c₂, hc₂b⟩ hu₁ hu₂ hfirst

/-! ## 3. Sharpness: the constant-curvature model -/

/-- **The model's first zero is at `a + π/√K` and there is none before it.**  For `K > 0` the
shifted model vanishes at `a + π/√K` and is strictly positive on the open interval before it;
by periodicity every subsequent zero is a shift of this one, so the model realizes the boundary
case of both spacing inequalities. -/
theorem sturmModel_zero_spacing {K a : ℝ} (hK : 0 < K) :
    sturmModel K a (a + Real.pi / Real.sqrt K) = 0 ∧
      ∀ t ∈ Ioo a (a + Real.pi / Real.sqrt K), sturmModel K a t ≠ 0 := by
  refine ⟨sturmModel_eq_zero_at_pi_sqrt hK, fun t ht => ?_⟩
  have hspan : Real.sqrt K * (a + Real.pi / Real.sqrt K - a) ≤ Real.pi := by
    rw [add_sub_cancel_left, mul_div_cancel₀ Real.pi (Real.sqrt_pos_of_pos hK).ne']
  exact ne_of_gt (sturmModel_pos_of_le hK hspan ht)

/-- **Sharpness of the strict-excess hypothesis.**  For `k ≡ K`, a consecutive zero `c₂` of the
model at exactly `a + π/√K` satisfies every hypothesis of `zero_spacing_lt_of_curvature_gt`
except the strict excess `hstrict`, and the strict conclusion `c₂ < a + π/√K` fails.  Hence the
strict-excess hypothesis cannot be dropped. -/
theorem sturmModel_spacing_boundary {K a c₂ : ℝ} (hK : 0 < K)
    (hc₂ : c₂ = a + Real.pi / Real.sqrt K) :
    JacobiSolutionOn (fun _ : ℝ => K) (sturmModel K a) (sturmModelDeriv K a)
        (sturmModelSecondDeriv K a) a c₂ ∧
      a < c₂ ∧ (∀ t ∈ Icc a c₂, K ≤ (fun _ : ℝ => K) t) ∧
      sturmModel K a a = 0 ∧ sturmModel K a c₂ = 0 ∧
      (∀ t ∈ Ioo a c₂, sturmModel K a t ≠ 0) ∧
      ¬ (c₂ < a + Real.pi / Real.sqrt K) := by
  subst hc₂
  refine ⟨sturmModel_jacobiSolutionOn (K := K) (a := a) (b := a + Real.pi / Real.sqrt K)
      hK.le, ?_, fun _ _ => le_rfl, by simp [sturmModel], (sturmModel_zero_spacing hK).1,
    (sturmModel_zero_spacing hK).2, lt_irrefl _⟩
  linarith [div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)]

end Poincare.L4.GeodesicComparison
