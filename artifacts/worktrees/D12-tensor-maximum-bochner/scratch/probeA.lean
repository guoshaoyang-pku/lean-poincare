import Mathlib.Tactic

section
universe uA
variable {A : Type uA} [CommRing A] [Algebra ℝ A]
abbrev gA (r : ℝ) : A := algebraMap ℝ A r
def ga (i : ℕ) : A := gA (i : ℝ)

lemma neg_self (h : ga 0 = - ga 0) : ga 0 = 0 := by
  have h2 : ga 0 + ga 0 = 0 := by rw [h]; abel
  have h3 : (2 : ℝ) • ga 0 = 0 := by
    rw [show (2 : ℝ) = (1 : ℝ) + 1 by norm_num, add_smul, one_smul, one_smul]
    exact h2
  have h4 : (1 / 2 : ℝ) • (2 : ℝ) • ga 0 = 0 := by rw [h3, smul_zero]
  have h5 : (1 : ℝ) • ga 0 = 0 := by
    simpa [mul_smul] using h4
  simpa using h5

lemma use : ga 0 = 0 := by
  apply neg_self
  sorry

end
