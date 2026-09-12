import Poincare.L4.GeodesicComparison.ZeroSpacing

/-!
Scratch (reviewer-side): adversarial sharpness check for the *interval* on which
`hstrict` is demanded in `zero_spacing_lt_of_curvature_gt`.

If `hstrict` were required only on the **closed** interval `[c₁, c₁+π/√K]`
instead of the open `(c₁, c₁+π/√K)`, the statement would be FALSE: with
`K = 1`, `k(t) = 3/2` at `t = π` and `k(t) = 1` elsewhere, the model
`sin` is still a Jacobi solution on `[0,π]` (at `t = π` both `u` and `u''`
vanish), it has consecutive zeros `0, π`, and `k` strictly exceeds `K`
at the closed-interval point `π`, yet the strict conclusion `π < π` fails.

So the open-interval placement in the artifact is exactly right.
-/

noncomputable section
open Set Filter
open scoped Topology
open Poincare.L4.GeodesicComparison
open Poincare.D12.ComparisonGeodesics

namespace ZeroSpacingClosedInterval

noncomputable def kend (t : ℝ) : ℝ := if t = Real.pi then 3 / 2 else 1

lemma kend_ge_one (t : ℝ) : (1 : ℝ) ≤ kend t := by
  unfold kend
  split_ifs <;> norm_num

lemma kend_gt_one_at_pi : (1 : ℝ) < kend Real.pi := by
  simp [kend]
  norm_num

lemma kend_jacobi :
    JacobiSolutionOn kend (sturmModel 1 0) (sturmModelDeriv 1 0)
      (sturmModelSecondDeriv 1 0) 0 Real.pi where
  hasDerivAt_u := fun t _ => hasDerivAtR_sturmModel 1 0 t
  hasDerivAt_du := fun t _ => hasDerivAtR_sturmModelDeriv (K := 1) (a := 0) (by norm_num)
  eq_secondDeriv := by
    intro t _
    by_cases ht : t = Real.pi
    · subst ht
      simp [kend, sturmModel, sturmModelSecondDeriv, Real.sin_pi]
    · have hk : kend t = 1 := by simp [kend, ht]
      rw [hk]
      simp only [sturmModelSecondDeriv, sturmModel]
      ring
  continuousOn_u := by unfold sturmModel; fun_prop
  continuousOn_du := by unfold sturmModelDeriv; fun_prop

/-- The closed-interval variant of `zero_spacing_lt_of_curvature_gt` is false. -/
theorem closed_interval_variant_false :
    ¬ (∀ {k : ℝ → ℝ} {K c₁ c₂ : ℝ} {u du ddu : ℝ → ℝ},
        (0 : ℝ) < K → c₁ < c₂ →
        JacobiSolutionOn k u du ddu c₁ c₂ →
        u c₁ = 0 → u c₂ = 0 →
        (∀ t ∈ Ioo c₁ c₂, u t ≠ 0) →
        (∀ t ∈ Icc c₁ (c₁ + Real.pi / Real.sqrt K), K ≤ k t) →
        (∃ t ∈ Icc c₁ (c₁ + Real.pi / Real.sqrt K), K < k t) →
        c₂ < c₁ + Real.pi / Real.sqrt K) := by
  intro h
  have hzero := sturmModel_zero_spacing (K := 1) (a := 0) (by norm_num)
  have hbad := h (k := kend) (K := 1) (c₁ := 0) (c₂ := Real.pi)
    (u := sturmModel 1 0) (du := sturmModelDeriv 1 0) (ddu := sturmModelSecondDeriv 1 0)
    (by norm_num) (by linarith [Real.pi_pos]) kend_jacobi
    (by simp [sturmModel]) (by simpa [Real.sqrt_one] using hzero.1)
    (fun t ht => hzero.2 t (by simpa [Real.sqrt_one] using ht))
    (fun t _ => kend_ge_one t)
    ⟨Real.pi, ⟨Real.pi_pos.le,
      by rw [Real.sqrt_one, div_one, zero_add]⟩, kend_gt_one_at_pi⟩
  rw [Real.sqrt_one, div_one, zero_add] at hbad
  exact lt_irrefl Real.pi hbad

#print axioms closed_interval_variant_false

end ZeroSpacingClosedInterval
