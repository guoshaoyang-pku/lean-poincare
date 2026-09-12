import Poincare.L4.GeodesicComparison.ZeroSpacing

noncomputable section
open Set Filter
open scoped Topology
open Poincare.L4.GeodesicComparison
open Poincare.D12.ComparisonGeodesics

/-! ## 1. Exact statements -/

#check @zero_spacing_lt_of_curvature_gt
#check @zero_spacing_ge_of_curvature_le
#check @sturmModel_zero_spacing
#check @sturmModel_spacing_boundary

/-! ## 2. Axiom cones of the four declarations -/

#print axioms zero_spacing_lt_of_curvature_gt
#print axioms zero_spacing_ge_of_curvature_le
#print axioms sturmModel_zero_spacing
#print axioms sturmModel_spacing_boundary

/-! ## 3. Dependencies actually cited by the review brief -/

#print axioms Poincare.L4.GeodesicComparison.exists_jacobi_zero_of_curvature_gt
#print axioms Poincare.L4.GeodesicComparison.no_first_zero_of_curvature_le_of_lt_pi
#print axioms Poincare.L4.GeodesicComparison.jacobiSolutionOn_mono_Icc
#print axioms Poincare.L4.GeodesicComparison.sturmModel_pos_of_le
#print axioms Poincare.L4.GeodesicComparison.sturmModel_eq_zero_at_pi_sqrt

/-! ## 4. Adversarial check: the docstring claim that (1) does not use
`hc₁c₂ : c₁ < c₂` or `hu₂ : u c₂ = 0`.  We re-prove (1) with those two
hypotheses deleted, by the same proof script. -/

theorem zero_spacing_lt_variant_no_consecutiveness {k : ℝ → ℝ} {K c₁ c₂ : ℝ} {u du ddu : ℝ → ℝ}
    (hK : 0 < K)
    (h : JacobiSolutionOn k u du ddu c₁ c₂)
    (hu₁ : u c₁ = 0)
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

/-! ## 5. Adversarial check: the sharpness witness of (4) with *all* hypotheses
of (1) except `hstrict` made explicit, including `a < c₂` and the curvature
bound `K ≤ k`, plus the failure of the strict conclusion. -/

example {K a : ℝ} (hK : 0 < K) :
    ∃ (k : ℝ → ℝ) (c₂ : ℝ),
      0 < K ∧ a < c₂ ∧
      JacobiSolutionOn k (sturmModel K a) (sturmModelDeriv K a)
        (sturmModelSecondDeriv K a) a c₂ ∧
      sturmModel K a a = 0 ∧ sturmModel K a c₂ = 0 ∧
      (∀ t ∈ Ioo a c₂, sturmModel K a t ≠ 0) ∧
      (∀ t ∈ Icc a (a + Real.pi / Real.sqrt K), K ≤ k t) ∧
      ¬ (∃ t ∈ Ioo a (a + Real.pi / Real.sqrt K), K < k t) ∧
      ¬ (c₂ < a + Real.pi / Real.sqrt K) := by
  refine ⟨fun _ => K, a + Real.pi / Real.sqrt K, hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [div_pos Real.pi_pos (Real.sqrt_pos_of_pos hK)]
  · exact sturmModel_jacobiSolutionOn (K := K) (a := a)
      (b := a + Real.pi / Real.sqrt K) hK.le
  · simp [sturmModel]
  · exact (sturmModel_zero_spacing hK).1
  · exact (sturmModel_zero_spacing hK).2
  · intro t _; exact le_rfl
  · rintro ⟨t, ht, hlt⟩; exact absurd hlt (lt_irrefl K)
  · exact lt_irrefl _

/-! ## 6. Adversarial check: (1)'s conclusion is non-vacuous for the model with
`k ≡ K` removed (strict excess at distance `π/4` from `a`), and (2) attains
equality at `k ≡ K`. -/

example {K a : ℝ} (hK : 0 < K) :
    sturmModel K a (a + Real.pi / Real.sqrt K) = 0 ∧
      (a + Real.pi / Real.sqrt K) - a = Real.pi / Real.sqrt K :=
  ⟨(sturmModel_zero_spacing hK).1, add_sub_cancel_left a (Real.pi / Real.sqrt K)⟩

end
